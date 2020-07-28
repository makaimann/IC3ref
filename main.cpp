/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <iostream>
#include <fstream>
#include <string>
#include <time.h>

extern "C" {
#include "aiger.h"
}
#include "IC3.h"
#include "Model.h"

// Makai: include solver for dumping transition relation
#include "Solver.h"

int main(int argc, char ** argv) {
  unsigned int propertyIndex = 0;
  bool basic = false, random = false;
  bool dumpFiles = false;
  string baseDumpFilename = "";
  // to remove
  bool dumpTrans = false, dumpInv = false;
  string initFilename="", mappingFilename="", transFilename = "", invFilename = "", invPrimedFilename = "";
  // end to remove
  int verbose = 0;
  // Makai: Adding option to dump transition relation and final invariants
  //        (when property holds)
  string arg; ///< temporary var
  for (int i = 1; i < argc; ++i) {
    if (string(argv[i]) == "-v")
      // option: verbosity
      verbose = 2;
    else if (string(argv[i]) == "-s")
      // option: print statistics
      verbose = max(1, verbose);
    else if (string(argv[i]) == "-r") {
      // option: randomize the run, which is useful in performance
      // testing; default behavior is deterministic
      srand(time(NULL));
      random = true;
    }
    else if (string(argv[i]) == "-b")
      // option: use basic generalization
      basic = true;
    else if ((arg = string(argv[i])).substr(0, 7) == "--dump=") {
      dumpFiles = true;
      baseDumpFilename = arg.substr(7, arg.length() - 7);
    } else
      // optional argument: set property index
      propertyIndex = (unsigned) atoi(argv[i]);
  }

  // read AIGER model
  aiger * aig = aiger_init();
  const char * msg = aiger_read_from_file(aig, stdin);
  if (msg) {
    cout << msg << endl;
    return 0;
  }
  // create the Model from the obtained aig
  Model * model = modelFromAiger(aig, propertyIndex);
  aiger_reset(aig);
  if (!model) return 0;

  // model check it
  IC3::Result res = IC3::check(*model, verbose, basic, random);

  // Makai: dump cnf if asked
  // TODO: consider putting this in model. Only issue is it doesn't have access
  // to invariant NOTE: adding 1 to all vars so that they start at 1 instead of
  // 0, to avoid conflicting
  //       with the DIMACs format which uses zero as a line terminator
  if (dumpFiles) {
    // dumping Trans
    string transFilename = baseDumpFilename + "-trans.cnf";
    cout << "dumping CNF transition relation to file: " << transFilename << endl;
    ofstream trCnf(transFilename);
    Minisat::SimpSolver* sslv = model->getSimpSolver();
    for (Minisat::ClauseIterator c = sslv->clausesBegin();
         c != sslv->clausesEnd(); ++c) {
      const Minisat::Clause & cls = *c;
      for (int i = 0; i < cls.size(); ++i) {
        trCnf << (Minisat::sign(cls[i]) ? "-" : "") +
                     to_string(Minisat::toInt(model->varOfLit(cls[i]).var()) +
                               1) +
                     " ";
      }
      trCnf << "0\n";
    }
    // We need the trail because unit clauses are put in the trail automatically
    for (Minisat::TrailIterator c = sslv->trailBegin();
         c != sslv->trailEnd(); ++c) {
      trCnf << (Minisat::sign(*c) ? "-" : "") +
                   to_string(Minisat::toInt(model->varOfLit(*c).var()) + 1) +
                   " 0\n";
    }
    LitVec constraints = model->invariantConstraints();
    for (LitVec::const_iterator i = constraints.begin(); i != constraints.end();
         ++i) {
      trCnf << (Minisat::sign(model->primeLit(*i)) ? "-" : "") +
                   to_string(Minisat::toInt(
                                 model->varOfLit(model->primeLit(*i)).var()) +
                             1) +
                   " 0\n";
    }
    trCnf.close();

    // end dumping Trans

    // dump Init

    Minisat::Solver *init_solver = model->newSolver();
    model->loadInitialCondition(*init_solver);
    string initFilename = baseDumpFilename + "-init.cnf";
    cout << "dumping CNF transition relation to file: " << initFilename << endl;
    ofstream initCnf(initFilename);
    if (model->constraints.empty()) {
      // an intersection check (AIGER 1.9 w/o invariant constraints)
      std::cout << "init size " << model->init.size() << std::endl;
      for (Minisat::Lit lit : model->init) {
        init_solver->addClause(lit);
      }
    }

    for (Minisat::ClauseIterator c = init_solver->clausesBegin();
         c != init_solver->clausesEnd(); ++c) {
      const Minisat::Clause &cls = *c;
      for (int i = 0; i < cls.size(); ++i) {
        initCnf << (Minisat::sign(cls[i]) ? "-" : "");
        initCnf << to_string(Minisat::toInt(model->varOfLit(cls[i]).var()) + 1);
        initCnf << " ";
      }
      initCnf << "0\n";
    }

    for (Minisat::TrailIterator c = init_solver->trailBegin();
         c != init_solver->trailEnd(); ++c) {
      initCnf << (Minisat::sign(*c) ? "-" : "");
      initCnf << to_string(Minisat::toInt(model->varOfLit(*c).var()) + 1) +
                     " 0\n";
    }

    initCnf.close();
    delete init_solver;

    // end dumping Init

    // dump mapping from unprimed to primed vars

    string mappingFilename = baseDumpFilename + "-mapping.txt";
    cout << "dumping mapping from unprimed to primed vars to file: "
         << mappingFilename << endl;
    ofstream primeMapping(mappingFilename);
    primeMapping << model->varOfLit(model->error()).var() + 1;
    primeMapping << " ";
    primeMapping << model->varOfLit(model->primedError()).var() + 1
                 << std::endl;
    for (auto it = model->beginLatches(); it != model->endLatches(); ++it) {
      Var v = *it;
      primeMapping << v.var() + 1;
      primeMapping << " ";
      primeMapping << model->primeVar(v).var() + 1 << std::endl;
    }
    primeMapping.close();

    // end dumping primed mapping

    // dump invariant if result is true
    if (!res.rv) {
      cout << "asked to dump invariant but property does not hold -- aborting." << endl;
    }
    else {
      string invFilename = baseDumpFilename + "-inv.cnf";
      string invPrimedFilename = baseDumpFilename + "-inv-primed.cnf";
      cout << "Found " << res.inv.size() << " candidate invariant clauses." << endl;
      cout << "dumping CNF invariant to file: " << invFilename << endl;
      cout << "       and primed CNF to file: " << invPrimedFilename << endl;
      ofstream invCnf(invFilename);
      ofstream invPrimedCnf(invPrimedFilename);
      // dump the property as the first literal
      invCnf << "c first literal is the property\n";
      invPrimedCnf << "c first literal is the property\n";
      Minisat::Lit err = model->error();
      // property is negated, so complement it
      invCnf << (Minisat::sign(err) ? "" : "-") +
                    to_string(Minisat::toInt(model->varOfLit(err).var()) + 1) +
                    " 0\n";
      invPrimedCnf << (Minisat::sign(err) ? "" : "-") +
                          to_string(
                              Minisat::toInt(
                                  model->varOfLit(model->primeLit(err)).var()) +
                              1) +
                          " 0\n";
      for (IC3::CubeSet::const_iterator cube = res.inv.begin(); cube != res.inv.end(); ++cube) {
        const LitVec & lcube = *cube;
        for (unsigned int i = 0; i < lcube.size(); ++i) {
          // negating the literals
          invCnf << (Minisat::sign(lcube[i]) ? "" : "-") +
                        to_string(
                            Minisat::toInt(model->varOfLit(lcube[i]).var()) +
                            1) +
                        " ";
          invPrimedCnf
              << (Minisat::sign(lcube[i]) ? "" : "-") +
                     to_string(
                         Minisat::toInt(
                             model->varOfLit(model->primeLit(lcube[i])).var()) +
                         1) +
                     " ";
        }
        invCnf << "0\n";
        invPrimedCnf << "0\n";
      }
      invCnf.close();
      invPrimedCnf.close();
    }

    // end dumping invariant
  }

  // check the invariants

  if (res.rv)
  {
  Minisat::Lit err_ = model->error();
  Minisat::Lit primed_err_ = model->primedError();

  IC3::CubeSet toRemove;
  bool propRemoved = false;

  bool inductive = false;
  while (!inductive) {
    inductive = true;

    // debugging
    // do clause dropping procedure internally
    Minisat::Solver *dropper = model->newSolver();
    model->loadTransitionRelation(*dropper, true);
    model->loadError(*dropper);

    // add invariant clauses
    for (IC3::CubeSet::const_iterator cube = res.inv.begin(); cube != res.inv.end(); ++cube) {
      const LitVec & invcube = *cube;
      Minisat::vec<Minisat::Lit> cls;
      cls.capacity(invcube.size());
      for (unsigned i = 0; i < invcube.size(); ++i) {
        // negate to make it a clause
        cls.push(~invcube[i]);
      }
      dropper->addClause(cls);
    }

    // add property
    dropper->addClause(~err_);
    bool transRes = dropper->solve();
    cout << "transition relation and unprimed invariants (including property) is " << transRes << endl;
    assert(transRes);

    // check primed invariants
    // for now, don't even need indicator literal (just solve under assumptions)
    bool cex;
    for (IC3::CubeSet::const_iterator cube = res.inv.begin(); cube != res.inv.end(); ++cube) {
      const LitVec & invcube = *cube;
      Minisat::vec<Minisat::Lit> assumps;
      assumps.capacity(invcube.size());
      for (unsigned i = 0; i < invcube.size(); ++i) {
        // don't negate -- cube is negated clause which is what we want
        assumps.push(model->primeLit(invcube[i]));
      }
      cex = dropper->solve(assumps);
      inductive = inductive & !cex;

      if (cex) {
        toRemove.insert(*cube);
      }
    }

    // check primed property
    cex = dropper->solve(primed_err_);
    inductive = inductive & !cex;
    if (cex) {
      propRemoved = true;
    }
    // end debugging

    cout << "Need to remove " << toRemove.size() << " candidate invariants" << endl;
    if (propRemoved) {
      cout << "Property was removed -- uh oh" << endl;
    }
    else {
      cout << "Property was not removed -- phew!" << endl;
    }

    assert(toRemove.size() == 0);
    assert(!propRemoved);
  }
  }

  // print 0/1 according to AIGER standard
  cout << !res.rv << endl;

  delete model;

  return 1;
}
