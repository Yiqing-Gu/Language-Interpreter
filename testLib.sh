LIB=$1
F1=$2

echo "Test: Evaluate $F1 using $LIB"

cabal -v0 run logic -- $LIB $F1 > $F1.output;
./bin/logichk -2 $F1.output $F1.out;

RESULT=$?

rm $F1.output;

if [ $RESULT -eq 0 ] ; then
  echo "Evaluated $F1 successfully"  
else
  echo "Failed to Evaluate $F1"
fi

exit $RESULT
