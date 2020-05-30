module Regex where
import Data.Char
import Control.Monad.State.Lazy

data Regex = Null | Empty | Literal Char | Kleene Regex | Union Regex Regex | Concat Regex Regex

data NFA state = NFA {
    states :: [state],
    transitionF :: (state -> Char -> [state]),
    start :: [state],
    accept :: state -> Bool
}

generateAll :: Regex -> [String]
generateAll Null = []
generateAll Empty = [""]
generateAll (Literal a) = [[a]]
generateAll (Kleene r) = kleene (generateAll r)
generateAll (Union r1 r2) = (generateAll r1) ++ (generateAll r2)
generateAll (Concat r1 r2) = [x ++ y | x <- (generateAll r1), y <- (generateAll r2)]

type NFABuiler = State Int (NFA Int)

newState :: State Int Int
newState = do
    x <- get
    put (x+1)
    return x

buildNFA :: Regex -> NFABuiler
buildNFA Null = do
    a <- newState
    return (NFA
        [a]
        (\s x -> [a])
        [a]
        (\a->False))

buildNFA Empty = do
    a <- newState
    b <- newState
    return (NFA
        [a, b]
        (\s x -> [b])
        [a]
        (\s->s==a)) 

buildNFA (Literal l) = do
    a <- newState
    b <- newState
    c <- newState
    return (NFA
        [a, b, c]
        (\s x -> if (s,x) == (a,l) then [b] else [c])
        [a]
        (\s->s==b))

buildNFA (Union r1 r2) = do
    nfa1 <- buildNFA r1
    nfa2 <- buildNFA r2
    return (NFA
        ((states nfa1) ++ (states nfa2))
        (\s x -> (transitionF nfa1 s x) ++ (transitionF nfa2 s x))
        ((start nfa1) ++ (start nfa2))
        (\s->(accept nfa1 s) || (accept nfa2 s)))

buildNFA (Concat r1 r2) = do
    nfa1 <- buildNFA r1
    nfa2 <- buildNFA r2
    return (NFA
        ((states nfa1) ++ (states nfa2))
        (\s x -> (transitionF nfa1 s x) 
            ++ (transitionF nfa2 s x) 
            ++ (if accept nfa1 s 
                then concat (map (\s2 -> transitionF nfa2 s2 x) (start nfa2))
                else []))
        (start nfa1)
        (\s->(accept nfa2 s)))

buildNFA (Kleene r) = do
    nfa <- buildNFA r
    return (NFA
        (states nfa)
        (\s x -> (transitionF nfa s x)
            ++ (if accept nfa s 
                then concat (map (\s2 -> transitionF nfa s2 x) (start nfa))
                else []))
        (start nfa)
        (\s->(accept nfa s)))

-- nfa evaluator will need to return empty list if states not in set
compileNFA :: NFABuiler -> NFA Int
compileNFA b = evalState b 0

evalNFA :: NFA Int -> [Char] -> Bool
evalNFA nfa string =
    any (accept nfa) (run (start nfa) string)
    where
        run states [] = states
        run states (char:string) = run
            (concat (map (\state -> next state char) states))
            string
        next s c = if s `elem` (states nfa) then transitionF nfa s c else []

kleeneN :: [String] -> Int -> [String]
kleeneN xs 0 = [""]
kleeneN xs 1 = xs
kleeneN xs n = [ x ++ y | x <- xs, y <- (kleeneN xs (n-1))]
kleene :: [String] -> [String]
kleene xs = concat $ map (kleeneN xs) [0..]


main :: IO ()
main = return () 
