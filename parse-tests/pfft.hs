module Pfft where

pfft = [
  "parse-tests/atom-terms/atom1.l",
  "parse-tests/atom-terms/atom2.l",
  "parse-tests/atom-terms/atom3.l",
  "parse-tests/compound-terms/compound1.l",
  "parse-tests/compound-terms/compound2.l",
  "parse-tests/lib-tests/arithq.l",
  "parse-tests/lib-tests/listq2.l",
  "parse-tests/lib-tests/listq3.l",
  "parse-tests/lib-tests/listq.l",
  "parse-tests/lists/list1.l",
  "parse-tests/lists/list2.l",
  "parse-tests/naturals/nat1.l",
  "parse-tests/naturals/nat2.l",
  "parse-tests/rules/rule1.l",
  "parse-tests/rules/rule2.l",
  "parse-tests/rules/rule3.l",
  "parse-tests/rules/rule4.l",
  "parse-tests/rules/tests1.l",
  "parse-tests/rules/tests2.l",
  "parse-tests/rules/tests3.l",
  "parse-tests/rules/tests4.l",
  "parse-tests/simple-queries/simpleq1.l",
  "parse-tests/simple-queries/simpleq2.l",
  "parse-tests/simple-queries/simpleq3.l",
  "parse-tests/simple-queries/simpleq4.l",
  "parse-tests/simple-queries/simpleq5.l",
  "parse-tests/simple-rules/simpleq1.l",
  "parse-tests/simple-rules/simpleq2.l",
  "parse-tests/simple-rules/simpleq3.l",
  "parse-tests/simple-rules/simpleq4.l",
  "parse-tests/simple-rules/simpleq5.l",
  "parse-tests/vars/var1.l",
  "parse-tests/vars/var2.l",
  "parse-tests/vars/var3.l",
  "parse-tests/vars/var4.l",
  "parse-tests/vars/var5.l"
  ]

pfffffffffffft s = 
    "{\n\
      \\"name\": \"Logic Parse Test: " ++ s ++  "\",\n\
      \\"setup\": \"\",\n\
      \\"run\": \"./test.sh " ++ s ++ "\",\n\
      \\"input\": \"\",\n\
      \\"output\": \"\",\n\
      \\"comparison\": \"included\",\n\
      \\"timeout\": 0.5,\n\
      \\"points\": 1\n\
    \},\n"

main :: IO ()
main = mapM_ putStrLn (map pfffffffffffft pfft)
