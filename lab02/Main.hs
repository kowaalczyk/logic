module Main where

import Control.Monad.State
import Test.QuickCheck
import Data.List

-- ============== FROM Utils.hs ==========================

rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort

checkAll :: Testable prop => [prop] -> IO ()
checkAll [] = return ()
checkAll (p:ps) = do quickCheck p; checkAll ps

-- find all ways of joining the lists (c.f. example below)
distribute :: [[a]] -> [[a]] -> [[a]]
distribute xss yss = go xss yss yss where
  go [] _ _ = []
  go (_:xss) yss [] = go xss yss yss
  go (xs:xss) yss (ys:yss') = (xs ++ ys) : go (xs:xss) yss yss'

prop_distribute :: Bool
prop_distribute = distribute [[1, 2], [3, 4]] [[5, 6], [7]] == [[1, 2, 5, 6], [1, 2, 7], [3, 4, 5, 6], [3, 4, 7]]

-- ================= FROM Lab01.hs ======================

-- Variable names are just strings
type VarName = String

-- our inductive type for propositional formulas
data Formula = T | F | Var VarName | Not Formula | And Formula Formula | Or Formula Formula | Implies Formula Formula | Iff Formula Formula deriving (Eq, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, -->
(\/) = Or
(∨) = Or
(-->) = Implies

infixr 4 <-->
(<-->) = Iff

instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ map Var ["p", "q", "r", "s", "t"] ++ [T, F]

      f size = frequency [
        (1, fmap Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- finds all variables occurring in the formula (sorted, without duplicates)
variables :: Formula -> [VarName]
variables = rmdups . go where
  go T = []
  go F = []
  go (Var x) = [x]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi

-- truth valuations
type Valuation = VarName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Var x) rho = rho x
eval (Not phi) rho = not $ eval phi rho
eval (And phi psi) rho = eval phi rho && eval psi rho
eval (Or phi psi) rho = eval phi rho || eval psi rho
eval (Implies phi psi) rho = not (eval phi rho) || eval psi rho
eval (Iff phi psi) rho = eval phi rho == eval psi rho

-- updating a truth valuation
extend :: Valuation -> VarName -> Bool -> Valuation
extend rho x v y
  | x == y = v
  | otherwise = rho y

-- the list of all valuations on a given list of variables
valuations :: [VarName] -> [Valuation]
valuations [] = [undefined] -- any initial valuation would do
valuations (x : xs) = concat [[extend rho x True, extend rho x False] | rho <- valuations xs]

-- satisfiability checker based on truth tables
satisfiable :: Formula -> Bool
satisfiable phi = or [eval phi rho | rho <- valuations (variables phi)]

-- formula simplification
simplify :: Formula -> Formula

simplify T = T
simplify F = F
simplify (Var p) = Var p

simplify (Not T) = F
simplify (Not F) = T
simplify (Not (Not phi)) = simplify phi
simplify (Not phi) = Not (simplify phi)

simplify (And T phi) = simplify phi
simplify (And phi T) = simplify phi
simplify (And F _) = F
simplify (And _ F) = F
simplify (And phi psi) = And (simplify phi) (simplify psi)

simplify (Or T _) = T
simplify (Or _ T) = T
simplify (Or F phi) = simplify phi
simplify (Or phi F) = simplify phi
simplify (Or phi psi) = Or (simplify phi) (simplify psi)

simplify (Implies T phi) = simplify phi
simplify (Implies _ T) = T
simplify (Implies F _) = T
simplify (Implies phi F) = simplify (Not phi)
simplify (Implies phi psi) = Implies (simplify phi) (simplify psi)

simplify (Iff T phi) = simplify phi
simplify (Iff phi T) = simplify phi
simplify (Iff F phi) = simplify (Not phi)
simplify (Iff phi F) = simplify (Not phi)
simplify (Iff phi psi) = Iff (simplify phi) (simplify psi)

-- keep simplifying until no more simplifications are possible
deepSimplify :: Formula -> Formula
deepSimplify phi = go where
  psi = simplify phi
  go | phi == psi = phi
     | otherwise = deepSimplify psi

-- compute the NNF (negation normal form)
nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Not T) = F
nnf (Not F) = T
nnf (Var p) = Var p
nnf (Not (Var p)) = Not $ Var p
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = nnf (Or (Not phi) psi)
nnf (Iff phi psi) = nnf (And (Implies phi psi) (Implies psi phi))
nnf (Not (Not phi)) = nnf phi
nnf (Not (And phi psi)) = nnf (Or (Not phi) (Not psi))
nnf (Not (Or phi psi)) = nnf (And (Not phi) (Not psi))
nnf (Not (Implies phi psi)) = nnf (And phi (Not psi))
nnf (Not (Iff phi psi)) = nnf (Or (And phi (Not psi)) (And (Not phi) psi))

-- data structure used in the SAT solver
data Literal = Pos VarName | Neg VarName deriving (Eq, Show, Ord)

-- compute the opposite literal
opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type SatSolver = Formula -> Bool

test_solver :: SatSolver -> Bool
test_solver solver = and $ map solver satisfiableFormulas ++ map (not . solver) unsatisfiableFormulas

-- some examples of formulas
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"

satisfiableFormulas = [p /\ q /\ s /\ p, T, p, Not p, (p \/ q /\ r) /\ (Not p \/ Not r), (p \/ q) /\ (Not p \/ Not q)]
unsatisfiableFormulas = [p /\ q /\ s /\ Not p, T /\ F, F, (p \/ q /\ r) /\ Not p /\ Not r, (p <--> q) /\ (q <--> r) /\ (r <--> s) /\ (s <--> Not p)]

-- ==================== NEW MATERIAL ===================

-- A clause is a list of literals
type Clause = [Literal]

-- A cnf if a list of clauses
type CNF = [Clause]

-- transform a formula to logically equivalent cnf (exponential complexity)
-- (entirely analogous to dnf from Lab01)
cnf :: Formula -> CNF
cnf phi = go $ nnf phi where
  go T = []
  go F = [[]]
  go (Var x) = [[Pos x]]
  go (Not (Var x)) = [[Neg x]]
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = distribute (go phi) (go psi)

-- TODO
-- transform a formula to equi-satisfiable cnf (linear complexity)
-- there is no assumption on the input formula
-- Hints:
-- - Create a fresh variable x_phi for every subformula phi.
-- - For a subformula of the form phi = phi1 op phi2, use cnf :: Formula -> [[Literal]] above to produce the cnf psi_phi of x_phi <--> x_phi1 op x_phi2
-- - Concatenate all the cnfs psi_phi for every subformula phi.
-- - See slide #5 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
ecnf :: Formula -> CNF
ecnf phi = cnf topVar ++ formula where
  (_, topVar, formula) = go (nnf phi) 0  -- todo: make sure nnf is ok to do (no exponential blowup)
  go :: Formula -> Int -> (Int, Formula, CNF)
  go T v = (v, T, [])
  go F v = (v, F, [])
  go (Var x) v = (v, Var x, [])
  go (Not (Var x)) v = (v, Not (Var x), [])
  go (And phi psi) v = (v3, var3, cnf (Iff var3 (And var1 var2)) ++ ephi ++ epsi) where
    (v1, var1, ephi) = go phi v
    (v2, var2, epsi) = go psi v1
    v3 = succ v2
    var3 = makeVar v3
  go (Or phi psi) v = (v3, var3, cnf (Iff var3 (Or var1 var2)) ++ ephi ++ epsi) where
    (v1, var1, ephi) = go phi v
    (v2, var2, epsi) = go psi v1
    v3 = succ v2
    var3 = makeVar v3
  makeVar :: Int -> Formula
  makeVar v = Var ("__" ++ show v)


equiSatisfiable :: Formula -> Formula -> Bool
equiSatisfiable phi psi = satisfiable phi == satisfiable psi

-- convert a CNF in the list of clauses form to a formula
-- entirely analogous to "dnf2formula" from Lab01
cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos x) = Var x
  go2 (Neg x) = Not (Var x)

-- test for ecnf
prop_ecnf :: Formula -> Bool
prop_ecnf phi = equiSatisfiable phi (cnf2formula $ ecnf phi)

-- TODO
-- RESOLUTION
-- Apply the resolution rule by picking a variable appearing both positively and negatively.
-- Perform all possible resolution steps involving this variable in parallel.
-- Add all the resulting clauses (resolvents) and remove all clauses involving the selected variable.
-- See slide #15, point 6 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf

-- Assumption 1: every variable appears positively and negatively
-- Assumption 2: no variable appears both positively and negatively in the same clause (tautology)
-- Assumption 3: there is at least one clause
-- Assumption 4: all clauses are nonempty

resolution :: CNF -> CNF
resolution lss = undefined

prop_resolution :: Bool
prop_resolution = resolution [[Pos "p", Pos "q"], [Neg "p", Neg "q"]] == [[Pos "q", Neg "q"]]

-- find all positive occurrences of a variable name
positiveLiterals :: Clause -> [VarName]
positiveLiterals ls = rmdups [p | Pos p <- ls]

-- find all negative occurrences of a variable name
negativeLiterals :: Clause -> [VarName]
negativeLiterals ls = rmdups [p | Neg p <- ls]

-- find all occurrences of a variable name
literals :: Clause -> [VarName]
literals ls = rmdups $ positiveLiterals ls ++ negativeLiterals ls

-- TODO
-- remove clauses containing a positive and a negative occurrence of the same literal
removeTautologies :: CNF -> CNF
removeTautologies lss = undefined

-- TODO
-- One literal rule (aka unit propagation):
-- A one-literal clause [... [l] ...] can be removed
-- Hint: Remove [l] and all clauses containing l
-- Hint: Remove all occurrences of "opposite l"
-- Hint: Remove any empty clause [... [] ...] arising from this process
-- see slide #6 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
oneLiteral :: CNF -> CNF
oneLiteral lss = undefined

-- correctness test
prop_oneLiteral :: Bool
prop_oneLiteral =
  oneLiteral [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] ==
    [[Neg "q",Pos "r",Neg "r"],[Neg "q"],[Pos "q",Pos "r",Pos "s"]] &&
  oneLiteral [[Pos "p2"],[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Pos "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  oneLiteral [[Pos "q"],[Pos "p0"],[Neg "p0",Pos "s"],[Neg "p0"]] ==
    [[]]

-- TODO
-- Affirmative-negative rule (aka elimination of pure literals)
-- Remove all clauses containing a literal that appears only positively or negatively in every clause
-- see slide #7 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
-- this is the same as "elimination of pure literals" from the slide
affirmativeNegative :: CNF -> CNF
affirmativeNegative lss = undefined

prop_affirmativeNegative :: Bool
prop_affirmativeNegative =
  affirmativeNegative [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]]

-- the main DP satisfiability loop
-- this implements #15 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
loopDP :: CNF -> Bool
loopDP [] = True -- if the CNF is empty, then it is satisfiable
loopDP lss | [] `elem` lss = False -- if there is an empty clause, then the CNF is not satisfiable
loopDP lss =
  -- apply one round of simplification by removing tautologies, applying the one-literal rule, and the affirmativeNegative rule
  let lss' = rmdups . map rmdups . affirmativeNegative . oneLiteral . removeTautologies $ lss in
    if lss == lss'
      -- if the CNF didn't change, then do a resolution step (expensive)
      then loopDP $ resolution lss
      -- if the CNF did change, then do another round of simplifications recursively
      else loopDP lss'

-- the DP SAT solver
satDP :: SatSolver
satDP = loopDP . ecnf . deepSimplify . nnf

-- tests on random formulas
prop_DP :: Formula -> Bool
prop_DP phi = -- unsafePerformIO (do print "Checking:"; print phi; return True) `seq`
  satDP phi == satisfiable phi

-- tests on fixed formulas
prop_DP2 :: Bool
prop_DP2 = test_solver satDP

main = do 
  quickCheckWith (stdArgs {maxSize = 5}) prop_ecnf
  quickCheck prop_oneLiteral
  quickCheck prop_resolution
  quickCheckWith (stdArgs {maxSize = 10}) prop_DP
  quickCheck prop_DP2