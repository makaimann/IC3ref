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
  bool dumpTrans = false;
  string transFilename = "";
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

  // Makai: dump cnf if asked
  if (dumpTrans) {
    cout << "told dump CNF transition relation to file: " << transFilename << endl;
    Minisat::Solver * trDumper;
    trDumper = model->newSolver();
    // include primesConstraints
    model->loadTransitionRelation(*trDumper, true);
    trDumper->toDimacs(transFilename.c_str());
  }

  // model check it
  bool rv = IC3::check(*model, verbose, basic, random);
  // print 0/1 according to AIGER standard
  cout << !rv << endl;

  delete model;

  return 1;
}
