import Data.Char
import Data.List
import Data.Maybe
import Control.Monad.State

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



-- Dom `intersect` VRan = empty
type Subst = String -> Maybe Term

emptySubst :: Subst
emptySubst = const Nothing 

app :: Subst -> Term -> Term
app s (Var x) = case s x of Nothing -> Var x
                            Just t  -> t
app s (Constr c ts) = Constr c (map (app s) ts)

extend :: String -> Term -> Subst -> Subst
extend x t s y | y == x = Just t
               | otherwise = s y

semiunify :: Maybe Subst -> Term -> Term -> Maybe Subst
semiunify Nothing _ _ = Nothing
semiunify (Just s) (Var x) t = case s x of Just t' -> if t == t' then Just s else Nothing
                                           Nothing -> Just (extend x t s)
semiunify (Just s) (Constr _ _) (Var _) = Nothing
semiunify (Just s) (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 && length ts1 == length ts2 = foldl (\ms (t1, t2) -> semiunify ms t1 t2) (Just s) (zip ts1 ts2)
                                                   | otherwise = Nothing 


data RuleType = Simplification | Propogation

data Rule = Rule RuleType [Term] [Term]

(<=>) = Rule Simplification
(==>) = Rule Propogation

ruleInstance :: Int -> Rule -> Rule 
ruleInstance i (Rule t hs qs) = Rule t (map termInstance hs) (map termInstance qs)
    where
        termInstance (Var x) = Var (x ++ "_" ++ show i)
        termInstance (Constr c ts) = Constr c (map termInstance ts) 

applySomeRuleRec :: Maybe Subst -> [Term] -> [Term] -> [Term] -> [Term] -> Maybe ([Term], [Term], [Term])
applySomeRuleRec Nothing _ _ _ _ = Nothing
applySomeRuleRec (Just s) [] qs gs1 gs2 = Just (map (app s) qs, [], gs1 ++ gs2)
applySomeRuleRec (Just s) (h : hs) qs gs1 [] = Nothing
applySomeRuleRec (Just s) (h : hs) qs gs1 (g : gs2) = 
    maybe
        (applySomeRuleRec (Just s) (h : hs) qs (g : gs1) gs2)
        Just
        (fmap (\(rs, ps, os) -> (rs, g : ps, os)) (applySomeRuleRec (semiunify (Just s) h g) hs qs [] (gs1 ++ gs2)))

applySomeRule :: [Term] -> [Term] -> [Term] -> Maybe ([Term], [Term], [Term])
applySomeRule hs qs gs = applySomeRuleRec (Just emptySubst) hs qs [] gs


applyRule :: Rule -> [Term] -> Maybe [Term]
applyRule (Rule Simplification hs qs) goal = fmap (\(rs, ps, os) -> rs ++ os) $ applySomeRule hs qs goal
applyRule (Rule Propogation hs qs) goal = fmap (\(rs, ps, os) -> rs ++ ps ++ os) $ applySomeRule hs qs goal


run :: [Rule] -> [Term] -> Maybe [Term]
run = run_step 0
  where
    run_step i rules goal | elem false_constr goal = Nothing
                          | otherwise = let goal' = filter (/= true_constr) goal in
                                        case foldl (\m r -> maybe (applyRule (ruleInstance i r) goal') Just m) Nothing rules of Nothing -> Just goal'   
                                                                                                                                Just goal'' -> run_step (i + 1) rules goal''




prog1 :: [Rule]
prog1 = [[c "east", c "west"] <=> [true_constr],
         [c "north", c "south"] <=> [true_constr]]

test1_0 :: Maybe [Term]
test1_0 = run prog1 [c "north", c "east", c "south", c "south", c "west", c "east", c "north"]

test1_1 :: Maybe [Term]
test1_1 = run prog1 []


prog2 :: [Rule]
prog2 = [[c "e1", c "e1"] <=> [c "e2"],
         [c "c50", c "c50"] <=> [c "e1"],
         [c "c20", c "c20", c "c20", c "c20", c "c20"] <=> [c "e1"],
         [c "c20", c "c20", c "c10"] <=> [c "c50"],
         [c "c10", c "c10"] <=> [c "c20"]]

test2_0 :: Maybe [Term]
test2_0 = run prog2 [c "c10", c "c20", c "c50", c "e1", c "e2"]

test2_1 :: Maybe [Term]
test2_1 = run prog2 [c "c50", c "c50", c "c50", c "e1", c "e2", c "c20", c "c10", c "c20"]

test2_2 :: Maybe [Term]
test2_2 = run prog2 [c "c20", c "c20", c "c20", c "e1", c "c20", c "c20"]


prog3 :: [Rule]
prog3 = [[c "heat", c "h2", c "o2", c "h2"] <=> [c "h2o", c "h2o"],
         [c "electricity", c "h2o", c "h2o"] <=> [c "h2", c "o2", c "h2"]]

test3_0 :: Maybe [Term]
test3_0 = run prog3 [c "h2", c "h2", c "h2o", c "h2o", c "heat", c "electricity", c "electricity"]


arithm_prog :: [Rule]
arithm_prog =
    [[c "zero"] <=> [f "result" [c "zero"]],
     [f "pos" [v "X"]] <=> [f "result" [f "pos" [v "X"]]],
     [f "aop" [v "T", v "X", v "Y"]] <=> [f "zipper" [f "aop" [v "T", v "X", v "Y"], c "empty"]],
     [f "zipper" [c "zero", v "C"]] <=> [f "zipper" [f "res" [c "zero"], v "C"]],
     [f "zipper" [f "pos" [v "X"], v "C"]] <=> [f "zipper" [f "res" [f "pos" [v "X"]], v "C"]],
     [f "zipper" [f "aop" [v "T", v "X", v "Y"], v "C"]] <=> [f "zipper" [v "X", f "l" [v "T", v "Y", v "C"]]],
     [f "zipper" [f "res" [v "X"], c "empty"]] <=> [f "result" [v "X"]],
     [f "zipper" [f "res" [c "zero"], f "l" [c "plus", v "Y", v "C"]]] <=> [f "zipper" [v "Y", v "C"]],
     [f "zipper" [f "res" [c "zero"], f "l" [c "mult", v "Y", v "C"]]] <=> [f "zipper" [f "res" [c "zero"], v "C"]],
     [f "zipper" [f "res" [f "pos" [v "X"]], f "l" [v "T", v "Y", v "C"]]] <=> [f "zipper" [v "Y", f "r" [v "T", f "pos" [v "X"], v "C"]]],
     [f "zipper" [f "res" [f "aop" [v "TT", v "A", v "B"]], f "l" [v "T", v "Y", v "C"]]] <=> [f "zipper" [v "Y", f "r" [v "T", f "aop" [v "TT", v "A", v "B"], v "C"]]],
     [f "zipper" [f "res" [c "zero"], f "r" [c "plus", v "Y", v "C"]]] <=> [f "zipper" [v "Y", v "C"]],
     [f "zipper" [f "res" [c "zero"], f "r" [c "mult", v "Y", v "C"]]] <=> [f "zipper" [f "res" [c "zero"], v "C"]],
     [f "zipper" [f "res" [f "pos" [v "X"]], f "r" [v "T", v "Y", v "C"]]] <=> [f "zipper" [f "res" [f "aop" [v "T", v "Y", f "pos" [v "X"]]], v "C"]],
     [f "zipper" [f "res" [f "aop" [v "TT", v "A", v "B"]], f "r" [v "T", v "Y", v "C"]]] <=> [f "zipper" [f "res" [f "aop" [v "T", v "Y", f "aop" [v "TT", v "A", v "B"]]], v "C"]]]


arithm_test :: Maybe [Term]
arithm_test = run arithm_prog [f "aop" [c "plus", f "aop" [c "mult", f "pos" [c "1"], f "aop" [c "plus", c "zero", f "pos" [c "2"]]], f "aop" [c "mult", f "aop" [c "plus", c "zero", c "zero"], f "aop" [c "plus", f "pos" [c "1"], c "zero"]]]]
