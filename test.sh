F1=$1

# If two args are supplied, the first arg will be parsed,
# output, then compared against the second.
if [ -z "$2" ] ; then
    F2=$1
else
    F2=$2
fi

echo "Test: Parse $F1 against $F2\n"

cabal -v0 run logic -- -p $F1 > $F1.output;
./bin/logichk -1 $F1.output $F2;

RESULT=$?

rm $F1.output;

if [ $RESULT -eq 0 ] ; then
  echo "Parsed $1 successfully"  
else
  echo "Failed to Parse $1"
fi

exit $RESULT
