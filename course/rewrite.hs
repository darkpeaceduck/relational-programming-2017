import Data.List
import Data.Maybe



{--- Terms ---}
data Term = Var String | Constr String [Term] deriving (Eq)

v = Var
f = Constr
c name = Constr name []

instance Show Term where
  show (Var x) = x
  show (Constr c []) = c
  show (Constr c (hd : tl)) = c ++ "(" ++ foldl (\ac t -> ac ++ "," ++ show t) (show hd) tl ++ ")"

true_constr = c "true"
false_constr = c "false"

s t = Constr "s" [t]
o = Constr "o" []



{--- Substitution ---}
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
unifyPass Nothing _ _  = Nothing
unifyPass (Just s) (Var x) (Var y) | x == y = Just s
unifyPass (Just s) (Var x) t = case s x of Nothing -> if occursCheck x t then Just (extend x t s) else Nothing
                                           Just xt -> unifyPass (Just s) (app s xt) t
unifyPass (Just s) c@(Constr _ _) v@(Var _) = unifyPass (Just s) v c
unifyPass (Just s) (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 && length ts1 == length ts2 = foldl (\ms (t1, t2) -> unifyPass ms t1 t2) (Just s) (zip ts1 ts2)
                                                   | otherwise                            = Nothing 

unify :: Term -> Term -> Maybe Subst
unify = unifyPass (Just emptySubst)


semiExtend :: String -> Term -> Subst -> Subst
semiExtend x t s y | y == x = Just t
                   | otherwise = s y

semiunifyPass :: Maybe Subst -> Term -> Term -> Maybe Subst
semiunifyPass Nothing _ _ = Nothing
semiunifyPass (Just s) (Var x) t = case s x of Just t' -> if t == t' then Just s else Nothing
                                               Nothing -> Just (semiExtend x t s)
semiunifyPass (Just s) (Constr _ _) (Var _) = Nothing
semiunifyPass (Just s) (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 && length ts1 == length ts2 = foldl (\ms (t1, t2) -> semiunifyPass ms t1 t2) (Just s) (zip ts1 ts2)
                                                       | otherwise = Nothing 

semiunify :: Term -> Term -> Maybe Subst
semiunify = semiunifyPass (Just emptySubst)



{--- Subterms ---}

type ContextStep = (String, [Term], [Term])

type Context = [ContextStep]

type Subterm = (Term, Context)



insert_term_in_cntxt :: Term -> Context -> Term
insert_term_in_cntxt t [] = t
insert_term_in_cntxt t ((c, ts1, ts2) : cs) = insert_term_in_cntxt (Constr c (ts1 ++ [t] ++ ts2)) cs

subterms :: Bool -> Term -> [Subterm]
subterms b = map (\(t, rc) -> (t, reverse rc)) . subterms_rev b

-- second argument: are variables allowed?
subterms_rev :: Bool -> Term -> [Subterm]
subterms_rev True (Var x) = [(Var x, [])]
subterms_rev False (Var _) = []
subterms_rev vf (Constr c []) = [(Constr c [], [])]
subterms_rev vf (Constr c ts) = (Constr c ts, []) : (concat $ zipWith helper (init (inits ts)) (init (tails ts)))
  where
    helper (ts1) (t : ts2) = map (\(st, cs) -> (st, (c, ts1, ts2) : cs)) $ subterms_rev vf t



{--- Rewriting ---}

type Rule = (Term, Term)

type System = [Rule]

one_step :: System -> Term -> [Term]
one_step rs t = do
  (st, cntxt) <- subterms True t
  (l, r) <- rs
  (Just s) <- return (semiunify l st)
  return (insert_term_in_cntxt (app s r) cntxt)


normal_forms :: System -> Term -> [Term]
normal_forms rs t = case one_step rs t of [] -> [t]
                                          ts -> nub $ concat $ map (normal_forms rs) ts 



{--- Derivation example ---}

dx t = f "dx" [t]
zero = c "zero"
one = c "one"
x = c "x"
y = c "y"
plus a b = f "plus" [a, b]
mul a b = f "mul" [a, b]


der_rules :: [Rule]
der_rules = [
              (dx x, one),
              (dx y, zero),
              (dx (plus (v "U") (v "V")), plus (dx (v "U")) (dx (v "V"))),
              (dx (mul (v "U") (v "V")), plus (mul (dx (v "U")) (v "V")) (mul (v "U") (dx (v "V"))))
            ]

rewriting_test0 :: [Term]
rewriting_test0 = normal_forms der_rules (dx (mul (plus x y) (plus x y)))


{--- Confluence test ---}

termInstance :: String -> Term -> Term
termInstance pref (Var x) = Var (pref ++ "#" ++ x)
termInstance pref (Constr c ts) = Constr c (map (termInstance pref) ts)

crirical_pairs :: System -> [(Term, Term)]
crirical_pairs rs = nub $ do
  (l1i, r1i) <- rs
  let (l1, r1) = (termInstance "1" l1i, termInstance "1" r1i)
  (l2i, r2i) <- rs
  let (l2, r2) = (termInstance "2" l2i, termInstance "2" r2i)
  (st, cntxt) <- subterms False l1
  Just s <- return $ unify st l2
  let res = (app s r1, app s (insert_term_in_cntxt r2 cntxt))
  False <- return $ fst res == snd res
  return res


ff t = f "f" [t]
gf t = f "g" [t]

fg_rules :: System
fg_rules = [(ff (ff (v"X")), gf (v"X"))]

crirical_pairs_test :: [(Term, Term)]
crirical_pairs_test = crirical_pairs fg_rules

der_rules_ext :: System
der_rules_ext = der_rules ++ [(plus (v"X") zero, v"X")]


areJoinable :: System -> Term -> Term -> Bool
areJoinable rs t1 t2 = head (normal_forms rs t1) == head (normal_forms rs t2)

isConfluent :: System -> Bool
isConfluent rs = all (uncurry (areJoinable rs)) (crirical_pairs rs)

complete :: System -> System
complete rs = rs ++ filter (not . uncurry (areJoinable rs)) (crirical_pairs rs)


complete_test0 :: System
complete_test0 = complete fg_rules

complete_test1 :: System
complete_test1 = complete der_rules_ext


confluence_test0 :: Bool
confluence_test0 = isConfluent fg_rules

confluence_test1 :: Bool
confluence_test1 = isConfluent (complete fg_rules)

confluence_test2 :: Bool
confluence_test2 = isConfluent der_rules

confluence_test3 :: Bool
confluence_test3 = isConfluent der_rules_ext

confluence_test4 :: Bool
confluence_test4 = isConfluent (complete der_rules_ext)


der_rules_full :: System
der_rules_full = der_rules ++ [
                                (dx zero, zero),
                                (dx one, zero),
                                (plus (v"X") zero, v"X"),
                                (plus zero (v"X"), v"X"),
                                (mul (v"X") zero, zero),
                                (mul zero (v"X"), zero),
                                (mul (v"X") one, v"X"),
                                (mul one (v"X"), v"X")
                              ]

confluence_test5 :: Bool
confluence_test5 = isConfluent der_rules_full

rewriting_test1 :: [Term]
rewriting_test1 = normal_forms der_rules_full (dx (mul (plus x y) (plus x y)))





