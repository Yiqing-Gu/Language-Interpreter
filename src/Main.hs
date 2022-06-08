module Main where

import Control.Monad (when)
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import Bird.Parser hiding ((<|>), many)
import qualified Bird.Parser as Bird ((<|>), many)
import Bird.Printer
import Data.Char
import Data.List (nub, intersperse)
import Data.Monoid
import Control.Applicative
import qualified Data.Map as Map

data Term = Var  String
          | Str String
          | Compound Atom [Term] deriving Eq

type Atom = String

data Predicate = Predicate Atom [Term] deriving Eq

data Rule = Rule Predicate [Predicate] deriving Eq

newtype Query = Query [Predicate]

type Program = [Either Rule Query]

newtype Cal config log f a = Cal {runCal :: config -> f (log, a, config)}

type Config = (Int, Query)

type Sub = [(String, Term)]        

instance Show Term where
    show (Var var)    = var
    show (Str str)    = str
    show (Compound atom ts) = show_compound atom ts

show_compound :: String -> [Term] -> String
show_compound atom ts
    | null ts       = atom
    | otherwise     = atom ++ "(" ++ foldr1 (\xs acc -> xs ++ ", " ++ acc) (show <$> ts) ++ ")"

ignore :: Parser ()
ignore = (many $ (char '%' >> many (satisfy (const True) `sub` char '\n') >> char '\n') <|> (satisfy isSpace >> pure ())) >> pure ()

notFollow :: Parser a -> Parser ()
notFollow p = Parser $ \xs -> case runParser p xs of
    []  -> [((), xs)]
    _   -> []

sub :: Parser a -> Parser b -> Parser a
sub x y = notFollow y >> x  

tok :: Parser a -> Parser a
tok = (ignore >>)

varP :: Parser Term
varP = tok $ fmap Var $ (:) <$> upper <*> many (upper <|> lower)  

strP :: Parser Term
strP = tok $ do
    char '"'
    xs <- many $ satisfy (const True) `sub` char '"'
    char '"'
    pure . Str $ "\"" ++ xs ++ "\""

compoundP :: Parser Term
compoundP = do
    atom <- atomP
    args <- option [] $ do
        char '('
        xs <- sepBy1 (tok $ char ',') termP
        tok $ char ')'
        pure xs
    pure $ Compound atom args
  where atomP = tok $ (:) <$> lower <*> many (upper <|> lower)  

pNatP = tok $ nat >>= \x -> pure $ foldr (\_ -> succ) zero [1..x] where
    zero = Compound "zero" []
    succ = \x -> Compound "succ" [x]

listP = emp <|> list1 where
    emp = tok (char '[') >> tok (char ']') >> pure (Compound "nil" [])
    list1 = do
        tok $ char '['
        xs <- sepBy1 (tok $ char ',') termP
        xs1 <- option Nothing $ do
            tok $ char '|'
            Just <$> termP
        tok $ char ']'
        case xs1 of
            Nothing   -> pure $ foldr (\x acc -> Compound "cons" [x, acc]) (Compound "nil" []) xs
            Just xs1' -> pure $ foldr (\x acc -> Compound "cons" [x, acc]) xs1' xs

termP :: Parser Term
termP = varP <|> strP <|> compoundP <|> pNatP <|> listP

instance Show Predicate where
    show (Predicate atom ts) = show_compound atom ts

instance Show Rule where
    show (Rule header body)
      | null body            = show header ++ "."
      | otherwise            = show header ++ " :-\n" ++ foldr1 (\x acc -> x ++ ",\n" ++ acc) (("  " ++) . show <$> body) ++ "."

predicateP :: Parser Predicate
predicateP = compoundP >>= \term -> case term of
    Compound atom ts    -> pure $ Predicate atom ts
    _                   -> err

ruleP :: Parser Rule
ruleP = Rule <$> predicateP <*> bodyP
  where
      bodyP = tok $ opt1 <|> opt2
      opt1 = do 
          string ":-"
          ps <- sepBy (tok $ char ',') (predicateP <|> (varP >>= pure . Predicate "call" . (: []) ))
          tok $ char '.'
          pure ps
      opt2 = char '.' >> pure []

instance Show Query where
    show (Query qs)
      | null qs           = ""
      | otherwise         = foldr1 (\x acc -> x ++ ", " ++ acc) (show <$> qs) ++ "?"

queryP :: Parser Query
queryP = flip (const Query) <$> sepBy1 (tok $ char ',') predicateP <*> tok (char '?')

programP :: Parser Program
programP = many $ (Left <$> ruleP) <|> (Right <$> queryP)

-- part 2
underscore :: Term -> Bool
underscore (Var (x : _))   = x == '_'
underscore (Compound _ ts)  = any underscore ts
underscore _                = False

class HasVar t where
    vars :: t -> [String]

instance HasVar Term where
    vars (Var x)               = [x]
    vars (Str _)               = []
    vars (Compound _ ts)       = vars ts

instance HasVar Predicate where
    vars (Predicate _ ts)      = vars ts 

instance HasVar Rule where
    vars (Rule f fs)           = vars $ f : fs

instance HasVar Query where
    vars (Query qs)            = vars qs

instance HasVar t => HasVar [t] where
    vars ts                    = nub $ [v | t <- ts, v <- vars t]

class Unifiable t where
    unify :: t -> t -> Maybe Sub
    unify = unifyAux []
    unifyAux :: Sub -> t -> t -> Maybe Sub

instance Unifiable Term where
    unifyAux acc (Var x) (Var y)
      | x == y                        = Just acc
      | otherwise                     = Just $ (x, Var y) : acc 
    unifyAux acc (Var x) term
      | x `elem` vars term            = Nothing
      | otherwise                     = Just $ (x, term) : acc
    unifyAux acc term (Var x)         = unifyAux acc (Var x) term
    unifyAux acc (Str str1) (Str str2)
      | str1 == str2                  = Just acc
    unifyAux acc (Compound f1 ts1) (Compound f2 ts2)
      | f1 == f2 && length ts1 == length ts2              = unifyAux acc ts1 ts2
    unifyAux _  _ _                   = Nothing

instance (Unifiable t, Substitutable t) => Unifiable [t] where
    unifyAux acc [] []                      = Just acc
    unifyAux acc (t1 : ts1) (t2 : ts2)      = case unify t1 t2 of
        Nothing            -> Nothing
        Just sub           -> unifyAux (sub ++ acc) (withSub sub ts1) $ withSub sub ts2
    unifyAux _ _ _                          = Nothing

instance Unifiable Predicate where
    unifyAux acc (Predicate f ts) (Predicate f' ts') = unifyAux acc (Compound f ts) (Compound f' ts')

class Substitutable t where
    withSub :: Sub -> t -> t
    withSub = foldr ((.) . withSub1) id
    withSub1 :: (String, Term) -> t -> t

instance Substitutable Term where
    withSub1 (x, v) term = case term of
        Var x'
          | x' == x             -> v
          | otherwise           -> term
        Str _                   -> term
        Compound f ts           -> Compound f $ withSub1 (x, v) ts

instance Substitutable Predicate where
    withSub1 sub (Predicate f ts) = Predicate f $ withSub1 sub ts

instance Substitutable Rule where
  withSub1 sub (Rule f fs) = Rule (withSub1 sub f) $ withSub1 sub fs

instance Substitutable Query where
    withSub1 sub (Query qs) = Query . withSub1 sub $ qs

instance Substitutable t => Substitutable [t] where        
    withSub1 = map . withSub1

refreshAux :: Rule -> Int -> (Rule, Int)
refreshAux rule n =
    let vs = vars rule
        sub = zipWith (\v v' -> (v, Var $ "_" ++ show v')) vs [n..]
    in  (withSub sub rule, n + length vs)

instance (Monad f, Monoid log) => Functor (Cal config log f) where
    fmap f mx = mx >>= pure . f

instance (Monad f, Monoid log) => Applicative (Cal config log f) where
    pure = return
    mf <*> mx = mf >>= \f -> mx >>= pure . (f $)

instance (Monad f, Monoid log) => Monad (Cal config log f) where
    return x = Cal $ \config -> pure (mempty, x, config)
    mx >>= f = Cal $ \config -> runCal mx config >>= \(log, x, config') -> runCal (f x) config' >>= \(log', b, config'') -> pure (log <> log', b, config'')

instance Alternative Parser where
    empty = err
    (<|>) = (Bird.<|>)
    many = Bird.many

instance (Alternative f, Monad f, Monoid log) => Alternative (Cal config log f) where
    empty = Cal $ \_ -> empty
    (Cal f) <|> (Cal g) = Cal $ \config -> f config <|> g config

tell :: Applicative f => log -> Cal config log f ()
tell log = Cal $ \config -> pure (log, (), config)

modify :: (Applicative f, Monoid log) => (config -> config) -> Cal config log f ()
modify f = Cal $ \config -> pure (mempty, (), f config)

get :: (Applicative f, Monoid log) => Cal config log f config
get = Cal $ \config -> pure (mempty, config, config)

step1 :: Map.Map (Atom, Int) [Rule] -> Cal Config (Dual Sub) [] ()
step1 database = get >>= \config -> case config of
    (_, Query [])                                  -> empty
    (i, Query ((Predicate "call" [Compound name ts]) : qs))
                                                   -> modify (const (i, Query $ Predicate name ts : qs))
    (i, Query (q@(Predicate atom ts) : qs))        -> case Map.lookup (atom, length ts) database of
        Nothing                                    -> empty
        Just rules                                 -> 
            foldr (<|>) empty [ tell (Dual sub) >> modify (const (i', withSub sub . Query $ body ++ qs)) 
                              | rule <- rules
                              , let (Rule header body, i') = refreshAux rule i
                              , sub <- maybe [] pure $ unify q header]

steps :: (Monad f, Monoid log) => (config -> Bool) -> Cal config log f () -> Cal config log f ()
steps isLeaf step = get >>= \config -> if isLeaf config then pure () else step >> steps isLeaf step

query :: Map.Map (Atom, Int) [Rule] -> Query -> [([(String, Term)], Bool)]
query database q = results where
    isLeaf = \(_, Query qs) -> null qs
    action = steps isLeaf (step1 database)
    subs = runCal action (0, q) >>= \(Dual sub, _, _) -> pure sub
    vs = vars q
    results = [([(v, withSub sub . Var $ v) | v <- vs], null sub) | sub <- subs]

goParse, goEval :: String -> IO ()
goParse s = do
    case runParser (programP >>= \p -> tok (string "") >> pure p) s of
        [(p, "")]  -> mapM_ (either print print) p
        -- [(p, "")]  -> withFile "output.l" WriteMode $ \h -> mapM_ (either (hPrint h) (hPrint h)) p
        _          -> putStrLn "parse fail"
goEval s  = do
    case runParser (programP >>= \p -> tok (string "") >> pure p) s of
        [(p, "")]  -> loop p Map.empty
        _          -> putStrLn "parse fail"
  where
      loop [] _                                               = pure ()
      loop (Left rule@(Rule (Predicate atom ts) _) : p) m     = loop p (Map.alter (maybe (pure [rule]) (\rs -> pure $ rs ++ [rule])) (atom, length ts) m)
      loop (Right q : p) m                                    = print_results (take 20 . map (\(r, b) -> (filter (not . underscore . snd) r, b)) $ query m q) >> loop p m

      print_results []                 = putStrLn "No."
      print_results rs
        | all snd rs                   = putStrLn "Yes."
        | otherwise                    = putStrLn $ "Yes:\n" ++ concat (intersperse ";\n" . map (aux . fst) . filter (not . snd) $ rs) ++ "."
      aux xs                           = concat . intersperse ",\n" . map (\(var, t) -> var ++ " = " ++ show t) $ xs

main :: IO ()
main = do args <- getArgs
          let files = filter ("-p" /=) args
              go  
               | elem "-p" args = goParse
               | otherwise      = goEval
          when (not (null files)) $
            go  . concat =<< mapM readFile files  
