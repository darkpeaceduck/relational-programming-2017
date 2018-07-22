import Data.Char
import Data.List
import Data.Maybe
import Control.Monad.State



{- Terms and substitutions -}

data Term = Var String | Constr String [Term] deriving (Eq)

v = Var
f = Constr
c name = Constr name []

instance Show Term where
  show (Var x) = x
  show (Constr c []) = c
  show (Constr c (hd : tl)) = c ++ "(" ++ foldl (\ac t -> ac ++ ", " ++ show t) (show hd) tl ++ ")"

-- Dom `intersect` coDom = empty
type Subst = String -> Maybe Term

emptySubst :: Subst
emptySubst = const Nothing 

app :: Subst -> Term -> Term
app s (Var x) = case s x of Nothing -> Var x
                            Just t  -> t
app s (Constr c ts) = Constr c (map (app s) ts)

extend :: String -> Term -> Subst -> Subst
extend x t s y | y == x = Just (app s t)
               | otherwise = fmap (app (\z -> if z == x then Just (app s t) else Nothing)) (s y)

-- when (Dom(p) `union` coDom(p)) `isSubset` coDom(s)
compose :: Subst -> Subst -> Subst
compose p s x = case s x of Nothing -> p x
                            Just t  -> Just (app p t)

occursCheck :: String -> Term -> Bool
occursCheck x (Var y)       = x /= y
occursCheck x (Constr _ ts) = and $ map (occursCheck x) ts

unifyPass :: Maybe Subst -> Term -> Term -> Maybe Subst
unifyPass Nothing _ _        = Nothing
unifyPass (Just s) (Var x) (Var y) | x == y = Just s
unifyPass (Just s) (Var x) t = case s x of Nothing -> if occursCheck x t then Just (extend x t s) else Nothing
                                           Just xt -> unifyPass (Just s) (app s xt) t
unifyPass (Just s) c@(Constr _ _) v@(Var _) = unifyPass (Just s) v c
unifyPass (Just s) (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 && length ts1 == length ts2 = 
                                                       foldl (\ms (t1, t2) -> unifyPass ms t1 t2) (Just s) (zip ts1 ts2)
                                                   | otherwise                            = Nothing 

unify :: Term -> Term -> Maybe Subst
unify = unifyPass (Just emptySubst)



{- Programs interpretation -}

data Rule = Rule {head :: Term, body :: [Term]} deriving (Eq, Show)

ruleInstance :: Int -> Rule -> Rule 
ruleInstance i (Rule p qs) = Rule (termInstance p) (map termInstance qs)
  where
    termInstance (Var x) = Var (show i ++ "#" ++ x)
    termInstance (Constr c ts) = Constr c (map termInstance ts)

data Program = Program {rules :: [Rule], goals :: [Term], objectiveVars :: [String]} deriving (Eq, Show)

data IterationRes = Res Subst | Lazy [IterationRes]

machineStep :: [Rule] -> Maybe Int -> Int -> [Rule] -> Subst -> [Term] -> [IterationRes] -- [Subst]
machineStep _ _ _ _ s [] = [Res s]
machineStep _ _ _ [] _ _ = []
machineStep rs (Just l) d rTail s gs | d `mod` (l + 1) == 0 =
  [Lazy $ machineStep rs (Just l) (d + 1) rTail s gs]
machineStep rs limit d (r : tl) s (g : gs) =
    let (Rule p qs) = ruleInstance d r in
    case unify (app s g) p of Nothing -> machineStep rs limit (d + 1) tl s (g : gs)
                              Just s' -> let sNew = compose s' s
                                         in machineStep rs limit (d + 1) rs sNew (map (app sNew) qs ++ gs) ++ 
                                            machineStep rs limit (d + 1) tl s (g : gs)

traversal :: [IterationRes] -> [Subst]
traversal = traversalAcc []
  where
    traversalAcc [] [] = []
    traversalAcc acc [] = traversal $ concat $ reverse $ acc
    traversalAcc acc (Res s : ns) = s : traversalAcc acc ns
    traversalAcc acc (Lazy ins : ns) = traversalAcc (ins : acc) ns


{- machineStep _ _ s [] _ = [s]
machineStep _ [] _ _ _ = []
machineStep rs (r : tl) s (g : gs) i =
    let (Rule p qs) = ruleInstance i r in
    case unify (app s g) p of Nothing -> machineStep rs tl s (g : gs) (i + 1)
                              Just s' -> let sNew = compose s' s
                                         in machineStep rs rs sNew (map (app sNew) qs ++ gs) (i + 1) ++ 
                                            machineStep rs tl s (g : gs) (i + 1)

data Result = Result [(String, Maybe Term)]

instance Show Result where
    show (Result []) = "\n"
    show (Result (h : t)) = "\n" ++ foldl (\ac b -> ac ++ "; " ++ showBind b) (showBind h) t
        where
            showBind (x, Nothing) = x ++ " = _"
            showBind (x, Just t) = x ++ " = " ++ show t -}

runGen :: Maybe Int -> Program -> [[Term]]
runGen limit (Program rs gs vs) = let ssRes = traversal $ machineStep rs limit 1 rs emptySubst gs
                                  in [map (maybe (c "?") id . s) vs | s <- ssRes]

run :: Program -> [[Term]]
run = runGen Nothing

runIterative :: Int -> Program -> [[Term]]
runIterative d = runGen (Just d)

{- test :: Program
test = Program [f "add" [c "o", v "Y", v "Y"] -| [],
                f "add" [f "s" [v "X"], v "Y", f "s" [v "Z"]] -| [f "add" [v "X", v "Y", v "Z"]]]
               [f "add" [f "s" [f "s" [c "o"]], f "s" [c "o"], v "SUM"],
                f "add" [v "SUB", f "s" [c "o"], f "s" [f "s" [f "s" [c "o"]]]],
                f "add" [v "X", v "Y", f "s" [f "s" [f "s" [c "o"]]]],
                f "add" [s (s o), v "A", v "B"]]
               ["SUM", "SUB", "X", "Y", "A", "B"] -}



{- Parser -}

readsString :: String -> String -> [String]
readsString "" s                          = [s]
readsString _ ""                          = []
readsString (c : s) (c' : s') | c == c'   = readsString s s'
                              | otherwise = []

readsSpaces :: String -> [String]
readsSpaces (' ' : s) = readsSpaces s
readsSpaces ('\n' : s) = readsSpaces s
readsSpaces ('\t' : s) = readsSpaces s
readsSpaces s = [s]

readsSeq :: ReadS a -> ReadS [a]
readsSeq readsA s = case readsA s of [] -> [([], s)]
                                     ps -> [ (a : as, s2) | (a,  s0) <- ps                 ,
                                                                 s1  <- readsSpaces s0     ,
                                                            (as, s2) <- readsSeq readsA s1 ]

readsNumber :: ReadS String
readsNumber = filter (\p -> not $ null $ fst p) . readsSeq readsDigit
  where
    readsDigit "" = []
    readsDigit (c : s) | '0' <= c && c <= '9' = [(c, s)]
                       | otherwise = []

readsIdentTail :: ReadS String
readsIdentTail = readsSeq readsIdSym
  where
    readsIdSym "" = []
    readsIdSym (c : s) | 'a' <= c && c <= 'z' = [(c, s)]
                       | 'A' <= c && c <= 'Z' = [(c, s)]
                       | '0' <= c && c <= '9' = [(c, s)]
                       | c == '_'             = [(c, s)]
                       | otherwise = [] 

readsVar :: ReadS String
readsVar ""                             = []
readsVar (c : s) | 'A' <= c && c <= 'Z' = [(c : res, r) | (res, r) <- readsIdentTail s]
                 | otherwise            = []

readsConstr :: ReadS String
readsConstr ""                             = []
readsConstr (c : s) | 'a' <= c && c <= 'z' = [(c : res, r) | (res, r) <- readsIdentTail s]
                    | otherwise            = []

readsTerm :: ReadS Term
readsTerm s = [ (Var n, s0) | (n, s0) <- readsVar s ] ++
              [ (Constr n [], s0) | (n, s0) <- readsConstr s ] ++
              [ (Constr n [], s0) | (n, s0) <- readsNumber s ] ++
              [ (Constr n (t : ts), s8) | (n,  s0) <- readsConstr s              ,
                                               s1  <- readsSpaces s0             ,
                                               s2  <- readsString "(" s1         ,
                                               s3  <- readsSpaces s2             ,
                                          (t,  s4) <- readsTerm s3               ,
                                               s5  <- readsSpaces s4             ,
                                          (ts, s6) <- readsSeq readsInnerTerm s5 ,
                                               s7  <- readsSpaces s6             ,
                                               s8  <- readsString ")" s7         ]

readsInnerTerm :: ReadS Term
readsInnerTerm s = [ (t, s2) |     s0  <- readsString "," s ,
                                   s1  <- readsSpaces s0    ,
                               (t, s2) <- readsTerm s1      ]

readsRule :: ReadS Rule
readsRule s = [ (Rule h [], s2) | (h, s0) <- readsTerm s        ,
                                      s1  <- readsSpaces s0     ,
                                      s2  <- readsString "." s1 ] ++
              [ (Rule h (q : qs), s8) | (h,  s0) <- readsTerm s                ,
                                             s1  <- readsSpaces s0             ,
                                             s2  <- readsString ":-" s1        ,
                                             s3  <- readsSpaces s2             ,
                                        (q,  s4) <- readsTerm s3               ,
                                             s5  <- readsSpaces s4             ,
                                        (qs, s6) <- readsSeq readsInnerTerm s5 ,
                                             s7  <- readsSpaces s6             ,
                                             s8  <- readsString "." s7         ]

newtype Rules = Rules {getRules :: [Rule]}

instance Read Rules where
  readsPrec _ s = [ (Rules rs, s2)  |      s0  <- readsSpaces s         ,
                                     (rs, s1) <- readsSeq readsRule s0 ,
                                          s2  <- readsSpaces s1        ]




{- Task 1: addition puzzle -}

additionProg :: [Rule]
additionProg = getRules $ read "\
\  suc(0, 1).                                                                       \
\  suc(1, 2).                                                                       \
\  suc(2, 3).                                                                       \
\  suc(3, 4).                                                                       \
\  suc(4, 5).                                                                       \
\  suc(5, 6).                                                                       \
\  suc(6, 7).                                                                       \
\  suc(7, 8).                                                                       \
\  suc(8, 9).                                                                       \
\                                                                                   \
\  digit(0).                                                                        \
\  digit(D) :- suc(T, D).                                                           \
\                                                                                   \
\  half_adder(0, B, B, 0) :- digit(B).                                              \
\  half_adder(A, 9, C, 1) :- suc(C, A).                                             \
\  half_adder(A, B, C, Qr) :- suc(Ap, A), suc(B, Bs), half_adder(Ap, Bs, C, Qr).    \
\                                                                                   \
\  adder(0, A, B, C, Qr) :- half_adder(A, B, C, Qr).                                \
\  adder(1, 9, B, B, 1) :- digit(B).                                                \
\  adder(1, A, B, C, Qr) :- suc(A, As), half_adder(As, B, C, Qr).                   \
\                                                                                   \
\  rel(x, R).                                                                       \
\  rel(D, D) :- digit(D).                                                           \
\                                                                                   \
\  is_solution(0, nil, nil, nil, nil, nil, nil).                                    \
\  is_solution(Q, cons(A,  As),  cons(B,  Bs),  cons(C,  Cs),                       \
\                cons(Ar, Ars), cons(Br, Brs), cons(Cr, Crs)) :-                    \
\      rel(A, Ar),                                                                  \
\      rel(B, Br),                                                                  \
\      rel(C, Cr),                                                                  \
\      adder(Q, Ar, Br, Cr, Qr),                                                    \
\      is_solution(Qr, As, Bs, Cs, Ars, Brs, Crs).                                  \
\                                                                                   \
\  solve(A, B, C, Ar, Br, Cr) :- is_solution(0, A, B, C, Ar, Br, Cr).               \
\"

-- PDN: partially defined number

pdnToTerm :: String -> Term
pdnToTerm = pdnToTermR . reverse
  where
    pdnToTermR "" = c "nil"
    pdnToTermR ('?' : n) = f "cons" [c "x", pdnToTermR n]
    pdnToTermR (d : n) | '0' <= d && d <= '9' = f "cons" [c [d], pdnToTermR n]
                       | otherwise = error "Incorrect PDN"

termToPDN :: Term -> String
termToPDN = reverse . termToPDNr
  where
    termToPDNr (Constr "nil" []) = ""
    termToPDNr (Constr "cons" [Constr "x" [], tl]) = '?' : termToPDNr tl
    termToPDNr (Constr "cons" [Constr [d] [], tl]) | '0' <= d && d <= '9' = d : termToPDNr tl
    termToPDNr _ = error "Term is not PDN"


showSolution :: String -> String -> String -> String -> String -> String -> String
showSolution aPDN bPDN cPDN a b c = aPDN ++ " + " ++ bPDN ++ " = " ++ cPDN ++ "  ==>  " ++
                                    a ++ " + " ++ b ++ " = " ++ c

-- all solutions
solveEq :: String -> String -> String -> [String]
solveEq aPDN bPDN cPDN = do
  [a, b, c] <- run $ Program additionProg 
                             [f "solve" [pdnToTerm aPDN, pdnToTerm bPDN, pdnToTerm cPDN, v "A", v "B", v "C"]]
                             ["A", "B", "C"]
  return $ showSolution aPDN  bPDN cPDN (termToPDN a) (termToPDN b) (termToPDN c)


{- toPeano :: Int -> Term
toPeano 0 = c "z"
toPeano n = f "s" [toPeano (n - 1)]

generateEq :: Int -> Int -> [String]
generateEq k vn = let sols = run $ Program additionProg 
                                   [f "gen" [toPeano k, toPeano vn, v "Ap", v "Bp", v "Cp", v "A", v "B", v "C"]]
                                   ["Ap", "Bp", "Cp", "A", "B", "C"]
                  in map show {-(\s -> showSolution (t s 0) (t s 1) (t s 2) (t s 3) (t s 4)(t s 5))-} sols
  where
    t s i = termToPDN (s !! i) -}
{- (-|) = Rule

test :: Program
test = Program [f "add" [c "o", v "Y", v "Y"] -| [],
                f "add" [f "s" [v "X"], v "Y", f "s" [v "Z"]] -| [f "add" [v "X", v "Y", v "Z"]]]
               [f "add" [f "s" [f "s" [c "o"]], f "s" [c "o"], v "SUM"],
                f "add" [v "SUB", f "s" [c "o"], f "s" [f "s" [f "s" [c "o"]]]],
                f "add" [v "X", v "Y", f "s" [f "s" [f "s" [c "o"]]]] {-,
                f "add" [f "s" [f "s" [c "o"]], v "A", v "B"] -} ]
               ["SUM", "SUB", "X", "Y", "A", "B"] -}


{- Task 2: wolf, goat and cabbage -}

crossingProg :: [Rule]
crossingProg = getRules $ read "\
\  member(X, cons(X, Xs)).                                                                                \
\  member(X, cons(Y, Ys)) :- member(X, Ys).                                                               \
\                                                                                                         \
\  extract(cons(X, Xs), X, Xs).                                                                           \
\  extract(cons(X, Xs), Y, cons(X, Ys)) :- extract(Xs, Y, Ys).                                            \
\                                                                                                         \
\  check_pairs(nil, S).                                                                                   \
\  check_pairs(cons(p(A, B), Ps), S) :- member(A, S), check_pairs(Ps, S).                                 \
\  check_pairs(cons(p(A, B), Ps), S) :- member(B, S), check_pairs(Ps, S).                                 \
\                                                                                                         \
\  step(ProhibitedPairs, BoatS, OtherS, BoatS, OtherS, alone) :- check_pairs(ProhibitedPairs, OtherS).    \
\  step(ProhibitedPairs, BoatS, OtherS, NBoatS, cons(X, OtherS), with(X)) :-                              \
\    extract(BoatS, X, NBoatS),                                                                           \
\    check_pairs(ProhibitedPairs, cons(X, OtherS)).                                                       \
\                                                                                                         \
\  go(ProhibitedPairs, right, nil, S, nil).                                                               \
\  go(ProhibitedPairs, left, LS, RS, cons(M, Log)) :-                                                     \
\    step(ProhibitedPairs, LS, RS, NLS, NRS, M),                                                          \
\    go(ProhibitedPairs, right, NLS, NRS, Log).                                                           \
\  go(ProhibitedPairs, right, LS, RS, cons(M, Log)) :-                                                    \
\    step(ProhibitedPairs, RS, LS, NRS, NLS, M),                                                          \
\    go(ProhibitedPairs, left, NLS, NRS, Log).                                                            \
\                                                                                                         \
\  isList(nil).                                                                                           \
\  isList(cons(X, Xs)) :- isList(Xs).                                                                     \
\                                                                                                         \
\  solve(ProhibitedPairs, S, R) :- isList(R), go(ProhibitedPairs, left, S, nil, R).                       \
\"

listTermToTermsList :: Term -> [Term]
listTermToTermsList (Constr "nil" []) = []
listTermToTermsList (Constr "cons" [h, tl]) = h : listTermToTermsList tl
listTermToTermsList _ = error "Term is not list"

tltlt :: [Term] -> Term
tltlt = foldr (\h t -> f "cons" [h, t]) (c "nil")

crossingAllSolutions :: [[Term]]
crossingAllSolutions = map listTermToTermsList $ nub $ concat $ run $ 
                       Program crossingProg 
                               [f "solve" [tltlt [f "p" [c "wolf", c "goat"],
                                                  f "p" [c "goat", c "cabbage"]], 
                                           tltlt [c "wolf", c "goat", c "cabbage"], 
                                           v "R"]]
                               ["R"]

