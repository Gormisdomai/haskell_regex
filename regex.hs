module Regex where
import Data.Char
import Data.Set hiding (map, filter)
import qualified Data.Set (map)
import Control.Monad.State.Lazy

-- we don't need KleenePlus as a seperate operator, it's just there to make NFA building easier
data Regex = Null | Empty | Literal Char | Kleene Regex | KleenePlus Regex | Union Regex Regex | Concat Regex Regex deriving Show

data NFA state = NFA {
    states :: Set state,
    transitionF :: (state -> Char -> Set state),
    start :: Set state,
    accept :: state -> Bool
}

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
        (singleton a)
        (\s x -> (singleton a))
        (singleton a)
        (\a->False))

buildNFA Empty = do
    a <- newState
    b <- newState
    return (NFA
        (fromList [a, b])
        (\s x -> (singleton b))
        (singleton a)
        (\s->s==a)) 

buildNFA (Literal l) = do
    a <- newState
    b <- newState
    c <- newState
    return (NFA
        (fromList [a, b, c])
        (\s x -> if (s,x) == (a,l) then (singleton b) else (singleton c))
        (singleton a)
        (\s->s==b))

buildNFA (Union r1 r2) = do
    nfa1 <- buildNFA r1
    nfa2 <- buildNFA r2
    return (NFA
        ((states nfa1) `union` (states nfa2))
        (\s x -> (transitionF nfa1 s x) `union` (transitionF nfa2 s x))
        ((start nfa1) `union` (start nfa2))
        (\s->(accept nfa1 s) || (accept nfa2 s)))

buildNFA (Concat r1 r2) = do
    nfa1 <- buildNFA r1
    nfa2 <- buildNFA r2
    return (NFA
        ((states nfa1) `union` (states nfa2))
        (\s x -> (transitionF nfa1 s x) 
            `union` (transitionF nfa2 s x) 
            `union` (if accept nfa1 s 
                then unions (Data.Set.map (\s2 -> transitionF nfa2 s2 x) (start nfa2))
                else empty))
        (start nfa1)
        (\s->(accept nfa2 s)))

buildNFA (KleenePlus r)  = do
    nfa <- buildNFA r
    return (NFA
        (states nfa)
        (\s x -> (transitionF nfa s x)
            `union` (if accept nfa s 
                then unions (Data.Set.map (\s2 -> transitionF nfa s2 x) (start nfa))
                else empty))
        (start nfa)
        (\s->(accept nfa s)))

buildNFA (Kleene r) = buildNFA (Union (KleenePlus r) Empty)

compileNFA :: NFABuiler -> NFA Int
compileNFA b = evalState b 0

evalNFA :: NFA Int -> [Char] -> Bool
evalNFA nfa string =
    any (accept nfa) (run (start nfa) string)
    where
        run states [] = states
        run states (char:string) = run
            (unions (Data.Set.map (\state -> next state char) states))
            string
        -- return empty list if states not in set
        next s c = if s `member` (states nfa) then transitionF nfa s c else empty


-- dump an NFA for testing / profiling / optimisation

dumpNFA :: NFA Int -> [Char] -> String
dumpNFA nfa xs = (dumpNFAStates nfa) ++ "\n" ++ (dumpNFATransitions nfa xs)

dumpNFAStates :: NFA Int -> String
dumpNFAStates nfa =
    show (zip ((toList . states) nfa) (map (accept nfa) ((toList . states) nfa)))

dumpNFATransitions :: NFA Int -> [Char] -> String
dumpNFATransitions nfa xs =
    let statesXinputs = [(state, input) | state <- ((toList . states) nfa), input <- xs] in show $ zip statesXinputs (map (uncurry (transitionF nfa)) statesXinputs)


-- generator functions for testing

generateAll :: Regex -> [String]
generateAll Null = []
generateAll Empty = [""]
generateAll (Literal a) = [[a]]
generateAll (Kleene r) = kleene (generateAll r)
generateAll (Union r1 r2) = (generateAll r1) ++ (generateAll r2)
generateAll (Concat r1 r2) = [x ++ y | x <- (generateAll r1), y <- (generateAll r2)]

kleeneN :: [String] -> Int -> [String]
kleeneN xs 0 = [""]
kleeneN xs 1 = xs
kleeneN xs n = [ x ++ y | x <- xs, y <- (kleeneN xs (n-1))]
kleene :: [String] -> [String]
kleene xs = concat $ map (kleeneN xs) [0..]

-- parser functions for utility

-- Parsing, (value matched, rest of string)

type Parse a = String -> Maybe (a, String)

token :: Char -> Parse Char
token c (x:xs) = if x==c then Just (c,xs) else Nothing
token c [] = Nothing

spot :: (Char -> Bool) -> Parse Char
spot p (x:xs) = if p x then Just (x,xs) else Nothing
spot p [] = Nothing
-- Functions for Combining Parsers


-- Chain Parsers if their outputs are sucessful

infixr 5 ^^^
(^^^) :: Parse a -> Parse b -> Parse (a,b)

(p1 ^^^ p2) inp =
    case p1 inp of
        Nothing -> Nothing
        Just (a, p1out) -> case p2 p1out of
            Nothing -> Nothing
            Just (b, p2out) -> Just ((a,b), p2out)

-- Apply a function to the output of a parser

infixl 4 >>>
(>>>) :: Parse a -> (a -> b) -> Parse b

(p1 >>> f) inp =
    case p1 inp of
        Nothing -> Nothing
        Just (a, p1out) -> Just (f a, p1out)

-- Apply the first parser which succeeds (or Nothing)

infixr 3 |||
(|||) :: Parse a -> Parse a -> Parse a

(p1 ||| p2) inp =
    case p1 inp of
        Just (a, p1out) -> Just (a, p1out)
        Nothing -> p2 inp

-- Apply a parser as many times as possible, accumalating the results into a list

many :: Parse a -> Parse [a]
many p =
    p ^^^ many p >>> join
    |||
    \inp -> Just ([], inp)
    where join (a,b) = a:b

-- Parsing Regex. We use underscore for the empty string # for the null regex | for union * for kleene and concatenation for concatenation

parseLiteral :: Parse Char
parseLiteral =
    spot isAlpha

parseRegex :: Parse Regex
parseRegex =
    token '(' ^^^ parseRegex ^^^ token ')' ^^^ token '*' >>> extractKleene >>> Kleene
    |||
    token '(' ^^^ parseRegex ^^^ token '|' ^^^ parseRegex ^^^ token ')' >>> extractBinary >>> (uncurry Union)
    |||
    token '(' ^^^ many parseRegex ^^^ token ')' >>> extractConcat >>> (foldr1 Concat)
    |||
    parseLiteral >>> Literal
    |||
    token '#' >>> const Null
    |||
    token '_' >>> const Empty
    where
        remSuf (e, _) = e
        extractKleene (p1, (r, (p2, k))) = r
        extractConcat (p1, (rs, p2)) = rs
        extractBinary (p1, (r1, (t, (r2, (p2))))) = (r1, r2)

parseInput :: Parse a -> String -> a
parseInput p inp =
    case p inp of
        Just (result,"") -> result
        Just (result,rest) -> error ("parse failed; unconsumed input: " ++ rest)
        Nothing -> error "parse unsucessful"

parseR :: String -> Regex
parseR = parseInput parseRegex

evalR :: String -> String -> Bool
evalR r i = evalNFA ((compileNFA . buildNFA . parseR) r) i

dumpNFAR :: String -> String
dumpNFAR r = dumpNFA ((compileNFA . buildNFA . parseR) r) (filter isAlpha r)

generateR :: String -> [String]
generateR = generateAll . parseR

main :: IO ()
main = return () 
