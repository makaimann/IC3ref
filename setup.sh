#!/bin/bash

git clone https://github.com/niklasso/minisat.git
# add a patch for dumping un-mapped CNF
# so we can print CNF that doesn't start at 1 -- i.e. just the invariants without anything else
patch -s -p0 < minisat.patch

cd minisat
make
cd ../

wget http://fmv.jku.at/aiger/aiger-1.9.4.tar.gz
tar -xzvf aiger-1.9.4.tar.gz
mv aiger-1.9.4/ aiger/
