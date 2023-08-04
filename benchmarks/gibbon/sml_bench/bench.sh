git -C $GIBBONDIR checkout jazullo/mlton-codegen
cabal v2-build $GIBBONDIR/gibbon-compiler/ -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project
cabal v2-exec gibbon -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project -- --mlton Insertion.hs
# cabal v2-exec gibbon -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project -- --mlton MergeSortSeq.hs  # no longer used
cabal v2-exec gibbon -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project -- --mlton DpsMerge.hs
cabal v2-exec gibbon -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project -- --mlton DpsMergeSort.hs
# cabal v2-exec gibbon -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project -- --mlton QSortShims.hs  # was hand modified
cabal v2-exec gibbon -w ghc-9.0.1 --project-file=$GIBBONDIR/cabal.project -- --mlton QuickSort.hs
mpl bench.mlb
./bench 9 40000
