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
  bool dumpTrans = false, dumpInv = false;
  string transFilename = "", invFilename = "", invPrimedFilename = "";
  int verbose = 0;
  // Makai: Adding option to dump transition relation and final invariants
  //        (when property holds)
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
    else if (string(argv[i]).substr(0, 8)=="--trans=") {
      // option: dump transition relation to file
      dumpTrans = true;
      string a = string(argv[i]);
      transFilename = a.substr(8, a.length()-8);
    }
    else if (string(argv[i]).substr(0, 6)=="--inv=") {
      // option: dump invariant to file
      dumpInv = true;
      string a = string(argv[i]);
      invFilename = a.substr(6, a.length()-6);
      size_t dotLoc = invFilename.find(".");
      if (dotLoc == string::npos) {
        invPrimedFilename = invFilename + "-primed";
      }
      else {
        invPrimedFilename = invFilename.substr(0, dotLoc) + "-primed" + invFilename.substr(dotLoc, invFilename.length()-dotLoc);
      }
    }
    else
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
  if (dumpTrans) {
    cout << "dumping CNF transition relation to file: " << transFilename << endl;
    string trCnf = "";
    Minisat::SimpSolver* sslv = model->getSimpSolver();
    for (Minisat::ClauseIterator c = sslv->clausesBegin(); 
         c != sslv->clausesEnd(); ++c) {
      const Minisat::Clause & cls = *c;
      for (int i = 0; i < cls.size(); ++i) {
        trCnf += (Minisat::sign(cls[i]) ? "-" : "") +
          to_string(Minisat::toInt(model->varOfLit(cls[i]).var())) + " ";
      }
      trCnf += "0\n";
    }
    // not sure if I need the trail?
    // for (Minisat::TrailIterator c = sslv->trailBegin(); 
    //      c != sslv->trailEnd(); ++c)
    //   slv.addClause(*c);
    LitVec constraints = model->invariantConstraints();
    for (LitVec::const_iterator i = constraints.begin(); 
         i != constraints.end(); ++i) {
      trCnf += (Minisat::sign(model->primeLit(*i)) ? "-" : "") +
        to_string(Minisat::toInt(model->varOfLit(model->primeLit(*i)).var())) + " 0\n";
    }
    ofstream trOut(transFilename);
    trOut << trCnf;
    trOut.close();
  }

  // Makai: do something if asked to dump invariant (and result is true)
  if (dumpInv) {
    if (!res.rv) {
      cout << "asked to dump invariant but property does not hold -- aborting." << endl;
    }
    else {
      cout << "Found " << res.inv.size() << " candidate invariant clauses." << endl;
      cout << "dumping CNF invariant to file: " << invFilename << endl;
      cout << "       and primed CNF to file: " << invPrimedFilename << endl;
      string invCnf = "", invPrimedCnf = "";
      // dump the property as the first literal
      invCnf += "c first literal is the property\n";
      invPrimedCnf += "c first literal is the property\n";
      Minisat::Lit err = model->error();
      // property is negated, so complement it
      invCnf += (Minisat::sign(err) ? "" : "-") + to_string(Minisat::toInt(model->varOfLit(err).var())) + " 0\n";
      invPrimedCnf += (Minisat::sign(err) ? "" : "-") + to_string(Minisat::toInt(model->varOfLit(model->primeLit(err)).var())) + " 0\n";
      for (IC3::CubeSet::const_iterator cube = res.inv.begin(); cube != res.inv.end(); ++cube) {
        const LitVec & lcube = *cube;
        for (unsigned int i = 0; i < lcube.size(); ++i) {
          // negating the literals
          invCnf += (Minisat::sign(lcube[i]) ? "" : "-") + to_string(Minisat::toInt(model->varOfLit(lcube[i]).var())) + " ";
          invPrimedCnf += (Minisat::sign(lcube[i]) ? "" : "-") +
            to_string(Minisat::toInt(model->varOfLit(model->primeLit(lcube[i])).var())) + " ";
        }
        invCnf += "0\n";
        invPrimedCnf += "0\n";
      }
      ofstream invOut(invFilename);
      ofstream invPrimedOut(invPrimedFilename);
      invOut << invCnf;
      invPrimedOut << invPrimedCnf;
      invOut.close();
      invPrimedOut.close();
    }
  }

  // print 0/1 according to AIGER standard
  cout << !res.rv << endl;

  delete model;

  return 1;
}
