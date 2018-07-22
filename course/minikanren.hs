import Data.Char
import Data.List
import Data.Maybe
-- import Control.Monad.State

data Term = Var Int | Constr String [Term] deriving (Eq)

v = Var
f = Constr
c name = Constr name []

instance Show Term where
    show (Var x) = "_" ++ show x
    show (Constr c []) = c
    show (Constr c (hd : tl)) = c ++ "(" ++ foldl (\ac t -> ac ++ "," ++ show t) (show hd) tl ++ ")"

s t = Constr "s" [t]
o = Constr "o" []

cons t1 t2 = Constr "cons" [t1, t2]
nil = Constr "nil" []


-- Dom `intersect` coDom = empty
type Subst = Int -> Maybe Term

emptySubst :: Subst
emptySubst = const Nothing 

app :: Subst -> Term -> Term
app s (Var x) = case s x of Nothing -> Var x
                            Just t  -> t
app s (Constr c ts) = Constr c (map (app s) ts)

extend :: Int -> Term -> Subst -> Subst
extend x t s y | y == x = Just (app s t)
               | otherwise = fmap (app (\z -> if z == x then Just (app s t) else Nothing)) (s y)

-- when (Dom(p) `union` coDom(p)) `isSubset` coDom(s)
compose :: Subst -> Subst -> Subst
compose p s x = case s x of Nothing -> p x
                            Just t  -> Just (app p t)

occursCheck :: Int -> Term -> Bool
occursCheck x (Var y)       = x /= y
occursCheck x (Constr _ ts) = and $ map (occursCheck x) ts

unifyPass :: Maybe Subst -> Term -> Term -> Maybe Subst
unifyPass Nothing _ _        = Nothing
unifyPass (Just s) (Var x) (Var y) | x == y = Just s
unifyPass (Just s) (Var x) t = case s x of Nothing -> if occursCheck x t then Just (extend x t s) else Nothing
                                           Just xt -> unifyPass (Just s) (app s xt) t
unifyPass (Just s) c@(Constr _ _) v@(Var _) = unifyPass (Just s) v c
unifyPass (Just s) (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 && length ts1 == length ts2 = foldl (\ms (t1, t2) -> unifyPass ms t1 t2) (Just s) (zip ts1 ts2)
                                                   | otherwise                            = Nothing 

unify :: Term -> Term -> Maybe Subst
unify = unifyPass (Just emptySubst)



type State = (Subst, Int)

type Goal = State -> [State]


(===) :: Term -> Term -> Goal
t1 === t2 = \(s, i) -> case unify (app s t1) (app s t2) of Nothing -> []
                                                           Just s' -> [(compose s' s, i)]

(|||) :: Goal -> Goal -> Goal
g1 ||| g2 = \s -> (g1 s) ++ (g2 s)

(&&&) :: Goal -> Goal -> Goal
g1 &&& g2 = \s -> (g1 s) >>= g2

fresh :: (Term -> Goal) -> Goal
fresh f = \(s, i) -> f (Var i) (s, i + 1)

emptyState :: State
emptyState = (emptySubst, 0)

run :: Int -> (Term -> Goal) -> [Term]
run n f = take n $ map (maybe (Var 0) id) $ map ($ 0) $ map fst $ fresh f emptyState 



pluso :: Term -> Term -> Term -> Goal
pluso x y r = 
    ((x === o) &&& (y === r)) ||| 
    (fresh (\x' -> 
        (fresh (\r' -> 
            (x === s x') &&&
            (r === s r') &&&
            (pluso x' y r')))))


appendo :: Term -> Term -> Term -> Goal
appendo a b ab = 
    ((a === nil) &&& (ab === b)) ||| 
    (fresh (\h ->
        (fresh (\t -> 
            (fresh (\tb -> 
                (a === cons h t) &&&
                (ab === cons h tb) &&&
                (appendo t b tb)))))))

reverso :: Term -> Term -> Goal
reverso a b = 
    ((a === nil) &&& (b === nil)) ||| 
    (fresh (\h ->
        (fresh (\t -> 
            (fresh (\t' -> 
                (a === cons h t) &&&
                (reverso t t') &&&
                (appendo t' (cons h nil) b)))))))

multo :: Term -> Term -> Term -> Goal
multo x y r = 
    ((x === o) &&& (r === o)) ||| 
    (fresh (\x' ->
        (fresh (\r' -> 
            (x === s x') &&&
            (pluso r' y r) &&&
            (multo x' y r')))))
