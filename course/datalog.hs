import Data.List


data Term = Const String | Var String deriving (Eq, Show)

data Predicate = Pred String [Term] deriving (Eq, Show)

data Atom = Pos Predicate | Neg Predicate deriving (Eq, Show)

data Rule = Rule Predicate [Atom] deriving (Eq, Show)

type Program = [Rule]


eject :: (a -> Bool) -> [a] -> Maybe (a, [a])
eject f xs = case span (not . f) xs of (l, [])      -> Nothing
                                       (l, (x : r)) -> Just (x, l ++ r)

rulePredName :: Rule -> String
rulePredName (Rule (Pred p _) _) = p

isNeg :: Atom -> Bool
isNeg (Pos _) = False
isNeg (Neg _) = True

atomPredName :: Atom -> String
atomPredName (Pos (Pred p _)) = p
atomPredName (Neg (Pred p _)) = p


findStratum :: [String] -> [Rule] -> Either String [String]
findStratum visited_ps unused_rules = 
   case eject (\r -> elem (rulePredName r) visited_ps) unused_rules 
   of Nothing -> Right visited_ps
      Just (Rule p ats, rs) -> case eject isNeg ats
                               of Just (a, _) -> Left (atomPredName a)
                                  Nothing -> findStratum (union visited_ps (map atomPredName ats)) rs


isFact :: Rule -> Bool
isFact (Rule _ []) = True
isFact _ = False


allHeadPredicateNames :: [Rule] -> [String]
allHeadPredicateNames = nub . map rulePredName

getLevels :: [Rule] -> [[Rule]]
getLevels [] = []
getLevels rs@(r : rs') = let stratum_members = helper (rulePredName r) rs
                         in filter (\r -> elem (rulePredName r) stratum_members) rs
                            : getLevels (filter (\r -> not (elem (rulePredName r) stratum_members)) rs)
  where
    helper :: String -> [Rule] -> [String]
    helper p rs = case findStratum [p] rs of Left q -> helper q rs
                                             Right ps -> ps


splitProgram :: Program -> ([Rule], [[Rule]])
splitProgram pr = (filter isFact pr, getLevels (filter (not . isFact) pr))


{-
sublists :: Int -> [a] -> [[a]]
sublists 0 _ = [[]]
sublists l [] = []
sublists l (x : xs) = map (x:) sublists 
-}

type Subst = String -> Maybe Term

emptySubst :: Subst
emptySubst = const Nothing 

extendSubst :: String -> Term -> Subst -> Subst
extendSubst x t s y | x == y = Just t
                    | otherwise = s y

appSubst :: Predicate -> Subst -> Predicate
appSubst (Pred p ts) s = Pred p (map ap ts)
  where
    ap (Const c) = Const c
    ap (Var x) = case s x of Nothing -> undefined
                             Just t -> t

semiunifyPassTerm :: Maybe Subst -> Term -> Term -> Maybe Subst
semiunifyPassTerm Nothing _ _ = Nothing
semiunifyPassTerm (Just s) (Const c) (Const c') | c == c' = Just s
                                                | otherwise = Nothing
semiunifyPassTerm (Just s) (Const c) _ = Nothing
semiunifyPassTerm (Just s) (Var x) t = case s x of Nothing -> Just (extendSubst x t s)
                                                   Just t' -> if t == t' then Just s else Nothing
                                                
semiunifyPass :: Maybe Subst -> Predicate -> Predicate -> Maybe Subst
semiunifyPass Nothing _ _ = Nothing
semiunifyPass (Just s) (Pred p ts) (Pred p' ts') | p == p' && length ts == length ts' = foldl (fmap uncurry semiunifyPassTerm) (Just s) (zip ts ts')
                                                 | otherwise = Nothing

applyRule :: Rule -> Predicate  -> [Predicate] -> [Predicate] -> [Predicate]
applyRule _ _ _ _ = undefined



saturated_set :: Program -> [Predicate]
saturated_set = undefined

check_predicate :: Program -> Predicate -> Bool
check_predicate rs p = elem p (saturated_set rs)
