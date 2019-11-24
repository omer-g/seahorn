#include "seahorn/HornUnroll.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornClauseDBWto.hh"
#include "seahorn/HornToSMT.hh"
#include "seahorn/HornifyModule.hh"
#include "llvm/Support/CommandLine.h"

#include "ufo/Smt/EZ3.hh"
#include "ufo/Smt/Z3n.hpp"

#include <fstream>
#include <utility>
#include <vector>
#include <set>

#include "boost/unordered_map.hpp"
#include <boost/lexical_cast.hpp>
#include <boost/unordered_set.hpp>

using namespace llvm;
static cl::opt<unsigned> UnrollDepth("horn-unroll-depth", cl::Hidden,
                                     cl::init(5));

#define PRINT_DEBUG 0

namespace seahorn {
using namespace expr;
char HornUnrollPass::ID = 0;

class UnrollWtoVisitor : public WtoElementVisitor<Expr> {
  typedef boost::unordered_map<Expr, std::vector<std::vector<Expr>>>
      exp_to_vexp_t;
  typedef boost::unordered_map<Expr, unsigned> exp_set_t;
  typedef boost::unordered_map<Expr, Expr> exp_to_exp_t;
  typedef boost::unordered_map<Expr, Expr>::value_type exp_pair_t;

  bool m_bStrict;
  // A uniform bound for unrolling all loops
  // We can extend it to unroll specific loops with specific bounds
  unsigned m_nBound;
  // A map from a predicate in the recursive db to its

  // versions in the non-recursive db
  exp_to_vexp_t m_rel2unrolled;
  exp_set_t m_rule2depth;
  std::vector<Expr> m_currentHead;

  // latest version in the non-recursive db
  exp_to_exp_t m_rel2curr;
  exp_to_exp_t m_rel2prev;

  HornClauseDB &m_db;
  HornClauseDB &m_unrolledDB;

  std::vector<unsigned> m_boundStack;

public:
  // EDIT
  exp_to_vexp_t &getRel2Unrolled() { return m_rel2unrolled; } // TODO check - now reference. if copy is ok
  // Can be called from duplicateRule to avoid duplication
  static Expr getDst(HornRule &rule) {
    return bind::fname(rule.head());
  }
  static Expr getSrc(HornRule &rule) {
    return (rule.body()->arity() == 2) ? bind::fname(rule.body()->left())
                                           : bind::fname(rule.body());
  }
  // END EDIT

  UnrollWtoVisitor(unsigned nBound, HornClauseDB &db, HornClauseDB &u_db,
                   bool bStrict)
      : m_nBound(nBound), m_db(db), m_unrolledDB(u_db), m_bStrict(bStrict) {
    /*typedef boost::reverse_graph<HornClauseDBCallGraph> ChcBgl;

    HornClauseDBCallGraph ucg (*m_pUnrolledDB);
    ucg.buildCallGraph();
    ChcBgl rucg = boost::make_reverse_graph(ucg);

    ChcBgl::out_edge_iterator it, end;
    std::pair<ChcBgl::out_edge_iterator,ChcBgl::out_edge_iterator> it_end =
    boost::out_edges(q, rucg); it = it_end.first; end = it_end.second;

    int i=1;
    while (it != end) {
        outs() << "Out edges: " << i++ << "\n";
        it++;
    }*/
  }

  virtual void visit(const wto_singleton_t &s) {
    m_rule2depth.insert(
        std::pair<Expr, unsigned>(s.get(), m_boundStack.size()));
    // Get the relation from the singleton
    Expr rel = s.get();
    unroll(rel);
  }

  virtual void visit(const wto_component_t &c) {
    m_boundStack.push_back(0);
    m_rule2depth.insert(
        std::pair<Expr, unsigned>(c.head(), m_boundStack.size()));
    m_currentHead.push_back(c.head());
    while (m_boundStack.back() < m_nBound) {
      unroll(c.head());
      for (auto &e : c) {
        e.accept(this);
      }
      m_boundStack.back()++;
    }

    m_currentHead.pop_back();
    m_boundStack.pop_back();
  }

private:
  void unroll(Expr rel) {
    // Create the unrolled version
    duplicateRel(rel);
    // Get all rules defining this relation and unroll them
    auto rules = m_db.def(rel);
    for (auto &rule : rules) {
      duplicateRule(*rule);
    }
  }

  void duplicateRule(HornRule &rule) {
    Expr dst = bind::fname(rule.head());

    Expr src = (rule.body()->arity() == 2) ? bind::fname(rule.body()->left())
                                           : bind::fname(rule.body());

    // In case we have no unrolled version for any of the relations,
    // we do not duplicate the rule and return.
    if (m_rel2unrolled.find(dst) == m_rel2unrolled.end() ||
        m_rel2unrolled[dst].empty() || m_rel2unrolled[dst].back().empty() ||
        (src != NULL &&
         (m_rel2unrolled.find(src) == m_rel2unrolled.end() ||
          m_rel2unrolled[src].empty() ||
          (m_rel2unrolled[src].size() < m_rel2unrolled[dst].size() &&
           m_rule2depth.find(dst) != m_rule2depth.end() &&
           m_rule2depth[dst] > m_boundStack.size()) ||
          m_rel2unrolled[src].back().empty())))
      return;

    // There are cases where a rule points back to itself
    if (dst == src && m_rel2unrolled[src].back().size() <= 1)
      return;

    // There are cases where a  rule points back to itself
    if (dst == src && m_rel2prev.find(src) == m_rel2prev.end())
      return;

    // Get the unrolled version of dst
    std::vector<Expr> &dst_unrolled = m_rel2unrolled[dst].back();
    Expr u_dst = dst_unrolled.back();

    std::shared_ptr<HornRule> u_rule;
    // In case there's no body, src is NULL
    if (src == NULL) {
      u_rule.reset(new HornRule(rule.vars(), bind::reapp(rule.head(), u_dst),
                                mk<TRUE>(m_unrolledDB.getExprFactory())));
      m_unrolledDB.addRule(*u_rule);
    } else {
      // Get the unrolled version of src
      std::vector<Expr> &src_unrolled = m_rel2unrolled[src].back();
      if (m_rule2depth[src] < m_rule2depth[dst] && !m_boundStack.empty() &&
          m_boundStack.back() > 0)
        return;
      if (m_rule2depth[src] == m_rule2depth[dst] &&
          m_rel2unrolled[dst].size() > m_rel2unrolled[src].size())
        return;

      unsigned size =
          (src != dst) ? src_unrolled.size() : src_unrolled.size() - 1;
      unsigned i = ((m_currentHead.empty() || m_currentHead.back() != src) &&
                    m_rule2depth.find(src) != m_rule2depth.end()) &&
                           !m_bStrict
                       ? 0
                       : (size - 1);
      for (; i < size; i++) {
        Expr u_src = src_unrolled[i];

        Expr body =
            (rule.body()->arity() == 2) ? rule.body()->left() : rule.body();
        // Get the Transition
        Expr tr = (rule.body()->arity() == 2)
                      ? rule.body()->right()
                      : mk<TRUE>(m_unrolledDB.getExprFactory());

        u_rule.reset(new HornRule(rule.vars(), bind::reapp(rule.head(), u_dst),
                                  boolop::land(bind::reapp(body, u_src), tr)));
        m_unrolledDB.addRule(*u_rule);
      }
    }
  }

  void duplicateRel(Expr rel) {
    Expr name = bind::fname(rel);
#if PRINT_DEBUG
    outs() << "Duplicating... " << *name << "\n";
#endif
    std::string tag_str = "";
    for (int i = 0; i < m_boundStack.size(); i++)
      tag_str = tag_str + "_" + lexical_cast<std::string>(m_boundStack[i]);
    Expr new_name = tag_str.length() ? variant::tag(name, tag_str) : name;
    Expr u_rel = bind::rename(rel, new_name);
    m_unrolledDB.registerRelation(u_rel);

    if (m_rel2unrolled.find(rel) == m_rel2unrolled.end())
      m_rel2unrolled.insert(std::pair<Expr, std::vector<std::vector<Expr>>>(
          rel, std::vector<std::vector<Expr>>()));

    std::vector<std::vector<Expr>> &unrolled = m_rel2unrolled[rel];
    if (m_boundStack.empty() || m_boundStack.back() == 0) {
      assert(unrolled.empty() || unrolled.back().size() == m_nBound);
      unrolled.resize(unrolled.size() + 1);
    }
    unrolled.back().push_back(u_rel);
    if (m_rel2curr.find(rel) != m_rel2curr.end()) {
      // Save the previous version, we may need it for
      // self-pointing rules
      if (m_rel2prev.find(rel) != m_rel2prev.end())
        m_rel2prev[rel] = m_rel2curr[rel];
      else
        m_rel2prev.insert(exp_pair_t(rel, m_rel2curr[rel]));

      m_rel2curr[rel] = u_rel;
    } else
      m_rel2curr.insert(exp_pair_t(rel, u_rel));
  }
};

void HornUnroll::unroll(unsigned nBound, HornifyModule &hm, HornClauseDB &db) {
  m_pUnrolledDB.reset(new HornClauseDB(db.getExprFactory()));

  db.buildIndexes();

  HornClauseDBCallGraph cg(db);

  HornClauseDBWto wto(cg);
  wto.buildWto();

  UnrollWtoVisitor v(nBound, db, *m_pUnrolledDB, m_bStrict);
  auto wto_it = wto.begin();
  auto wto_end = wto.end();
  while (wto_it != wto_end) {
    wto_it->accept(&v);
    wto_it++;
  }


  // XXX TODO:
  // Need to make sure that queries are not unrolled as well
  for (Expr q : db.getQueries()) {
    m_pUnrolledDB->addQuery(q);
  }

  // EDIT
  rel_2_unrolled = v.getRel2Unrolled();

  // END EDIT

}

void HornUnrollPass::unroll() {
  HornifyModule &hm = getAnalysis<HornifyModule>();
  HornClauseDB &db = hm.getHornClauseDB();
  m_HornUnroll.unroll(m_nBound, hm, db);
}

bool HornUnrollPass::runOnModule(Module &M) {
  LOG("horn-unroll", outs() << "===HornUnroll::runOnModule===\n");
  HornifyModule &hm = getAnalysis<HornifyModule>();

  unroll();

  // ufo::ZSolver<EZ3> solver(hm.getZContext());
  // HornToSMT smt(m_pUnrolledDB);
  // smt.toSMT(solver);

  // ****
  // TEMP CODE
  // Solve unrolled, non-recursive CHC with Spacer
  // ****
  outs() << "\n";
  errs() << "\n";
  ZFixedPoint<EZ3> fp(hm.getZContext());
  ZParams<EZ3> params(hm.getZContext());
  params.set(":engine", "spacer");
  fp.set(params);
  HornClauseDB &udb = m_HornUnroll.getHornClauseDB();
  udb.loadZFixedPoint(fp, true, false);
  std::string fileName = "unrolled_" + std::to_string(m_nBound) + ".smt2";
  std::ofstream unrolledSmtFile(fileName);
  unrolledSmtFile << fp << "\n";
  unrolledSmtFile.close();
  outs() << "\n------------------------START-----------------\n";
  outs() << "Printed file\n";

  boost::tribool res = fp.query ();
  if (res){
    outs () << "SAT - Program is not safe\n";
    return false;
  }
  else if (!res){
    outs () << "Program UNSAT with bound: " << m_nBound << "\n" <<
      "Looking for inductive invariant:";
  }
  else outs () << "unknown";
  outs () << "\n";

  // MUST DO THIS, delete causes it to crash
  // m_pUnrolledDB = NULL;

  // EDIT
  HornClauseDB &db = hm.getHornClauseDB();
  auto original_rules = db.getRules();

  std::set<Expr> dst_predicates;
  std::set<Expr> src_predicates;
  std::set<Expr> predicates_intersection;
  for (auto &rel: original_rules){
    dst_predicates.insert(UnrollWtoVisitor::getDst(rel));
    src_predicates.insert(UnrollWtoVisitor::getSrc(rel));
  }

  // Intersection of destination and source predicates - these are recursive
  for (auto &pred: dst_predicates){
    if (src_predicates.count(pred)){
      predicates_intersection.insert(pred);
    }  
  }
  
  if (predicates_intersection.size()==0){
    outs() << "No recursive predicates - nothing to check.\n";
    return false;
  }
 

  // Go over all recursive predicates 
  for (auto &P: predicates_intersection){

    // Go over the unrolled predicates of P, create an expression to check
    // for closeness property of a potential inductive invariant,
    // and pass it to a solver. If UNSAT then inductive invariant found.
    auto unrolled_P = m_HornUnroll.rel_2_unrolled[P];
    outs() << "\nunrolled_P.size() = " << unrolled_P.size() << "\n";
    for (auto V: m_HornUnroll.rel_2_unrolled[P]){
      outs() << "Unrolled predicates of P: " << V.size() << "\n";

      if (V.size() < 2){
        outs() << "Just one F_i formula - go on\n";
        continue;
      }

      ExprVector predicate_args;
      // Get arguments from original recursive predicate
      for (int i=0; i< bind::domainSz(P); i++){
        Expr arg_i_type = bind::domainTy(P, i);
        Expr var = bind::bvar(i, arg_i_type);
        predicate_args.push_back(var);
      }

      std::vector<Expr> covers;
      for (auto expr: V){
        Expr func_app = bind::fapp(expr, predicate_args);
        covers.push_back(fp.getCoverDelta(func_app));
      }

      // Create inductive invariant formula

      Expr last_formula = covers.back();

      // Initial formula:
      
      // Expr neg_or = mk<NEG>(mknary<OR>(covers.begin(), covers.end() - 1));
      // Expr and_formula = boolop::land(last_formula, neg_or);


      // The closeness formula is: f_n -> OR(f_1, ... , f_{n-1})
      // If the negation of this formula is UNSAT then the closeness
      // formula is always satisfiable.

      // Equivalent new formula:
      // NOT((f_1 OR f_2 OR ... f_{n-1}) OR NOT(f_n))

      Expr neg_last = mk<NEG>(last_formula);
      Expr f_i_or = mknary<OR>(covers.begin(), covers.end() - 1);
      Expr disjunct = mk<OR>(f_i_or, neg_last);
      Expr neg_disjunct = mk<NEG>(disjunct);

      outs() << "Solve formula for closeness here:\n";
      ufo::ZSolver<ufo::EZ3> smt_solver(hm.getZContext());
      smt_solver.assertExpr(neg_disjunct);
      boost::tribool res1 = smt_solver.solve();
      if (res1) outs () << "Negation of inductive invariance SAT - didn't find invariant so far\n";
      else if (!res1){
        outs () << "Negation of inductive invariance UNSAT - found invariant\n";
        return false;
      }
      else outs () << "unknown";
    }
  }
  outs() << "\n-----------------------END--------------------\n";

  // END EDIT

  return false;
}

void HornUnrollPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<HornifyModule>();
  AU.setPreservesAll();
}
} // namespace seahorn

namespace seahorn {
llvm::Pass *createHornUnrollPass(unsigned bnd, bool strict) {
  return new HornUnrollPass(bnd, strict);
}
} // namespace seahorn
