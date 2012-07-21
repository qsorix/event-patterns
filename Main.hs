-- implementation of an algorithm introduced by Jan Carlson in
-- Event Pattern Detection for Embedded Systems
--
-- I've added an operator 'last restriction' that accepts an event only after
-- some time. I'm not sure if my implementation is correct but it seems to work
-- in simple cases. With this operator I can say A and not B for 3 seconds which
-- is written as (A .@ 3) .- B
--
module Main where

import Data.List
import Test.HUnit

type Time     = Int
type TimeDiff = Int

-- | This both represents an event and allows matching against it.
--   Later it should be changed so I have a separate matcher type
--   and another type to store events with their attributes. Depending on how
--   complicated I want matchers to be, I can either change this and Instance,
--   or just the Instance type, because attributes have to be stored under
--   Instance
data Event = MouseClick
           | KeyPress
           | Alarm
           | Tick
           deriving (Show, Eq)

data EventExpr = E Event
               | Disjunction EventExpr EventExpr
               | Conjunction EventExpr EventExpr
               | Negation    EventExpr EventExpr
               | Sequence    EventExpr EventExpr
               | TempRestr   EventExpr TimeDiff
               | LastRestr   EventExpr TimeDiff

(.|) = Disjunction
(.+) = Conjunction
(.-) = Negation
(.>) = Sequence
(.@) = TempRestr
(.&) = LastRestr

type Instance = [(Time, Event)]

start :: Instance -> Time
start [] = -1
start i = minimum $ map fst i

end :: Instance -> Time
end [] = -1
end i = maximum $ map fst i

iJoin :: Instance -> Instance -> Instance
iJoin = union


-- Detector state. This is a trivial copy of book's implementation.
-- To do it properly, I should split private and shared states and make a
-- separate private state type for each Detector type.
data DState = DState
            { l_i  :: Instance
            , r_i  :: Instance
            , qq_i :: [Instance]
            , t_i  :: Time
            , a_i  :: Instance
            , ss_i :: [Time]
            }
            deriving (Show)

-- FIXME: turn this types into DPrimitive, DBinary, DTimed or sth like that and
-- pattern match on expression. This way some code duplication will be removed
data Detector = DPrimitive Event DState
              | DDisjunction Detector Detector DState
              | DConjunction Detector Detector DState
              | DNegation    Detector Detector DState
              | DSequence    Detector Detector DState
              | DTempRestr   Detector TimeDiff DState
              | DLastRestr   Detector TimeDiff DState
              deriving (Show)

state :: Detector -> DState
state (DPrimitive _ s) = s
state (DDisjunction _ _ s) = s
state (DConjunction _ _ s) = s
state (DNegation    _ _ s) = s
state (DSequence    _ _ s) = s
state (DTempRestr   _ _ s) = s
state (DLastRestr   _ _ s) = s


initialState :: DState
initialState = DState
             { l_i = []
             , r_i = []
             , qq_i = []
             , t_i = -1
             , a_i = []
             , ss_i = []
             }


makeDetector :: EventExpr -> Detector
makeDetector (E ev) = DPrimitive ev initialState
makeDetector (Disjunction j k) = DDisjunction (makeDetector j) (makeDetector k) initialState
makeDetector (Conjunction j k) = DConjunction (makeDetector j) (makeDetector k) initialState
makeDetector (Negation    j k) = DNegation    (makeDetector j) (makeDetector k) initialState
makeDetector (Sequence    j k) = DSequence    (makeDetector j) (makeDetector k) initialState
makeDetector (TempRestr   j t) = DTempRestr   (makeDetector j) t                initialState
makeDetector (LastRestr   j t) = DLastRestr   (makeDetector j) t                initialState


starting_later :: Instance -> Instance -> Instance
starting_later a b | start(a) <   start(b) = b
                   | start(a) >=  start(b) = a

all_possible_starts :: [Time] -> [Instance] -> [Time]
all_possible_starts ts is = filter (/= (-1)) $ union ts (map start is)

observe :: Detector -> Instance -> Detector
observe d [] = d

observe (DPrimitive ev st) [(t, cur_event)] =
    let a_i' = if ev == cur_event then [(t, cur_event)]
                                  else []
    in DPrimitive ev st{a_i=a_i'}

observe (DDisjunction j k st) ev =
    let j' = observe j ev
        k' = observe k ev
        a_j = (a_i . state) j'
        a_k = (a_i . state) k'
        ss_j = (ss_i . state) j'
        ss_k = (ss_i . state) k'
        a_i' = starting_later a_k a_j
        ss_i' = all_possible_starts (union ss_j ss_k) []
    in DDisjunction j' k' st{a_i = a_i', ss_i = ss_i'}

observe (DConjunction j k st) ev =
    let j' = observe j ev
        k' = observe k ev
        a_j = (a_i . state) j'
        a_k = (a_i . state) k'
        l_i' = starting_later (l_i st) a_j
        r_i' = starting_later (r_i st) a_k
        a_i' = if l_i' == [] || r_i' == [] || (a_j == [] && a_k == [])
                 then []
                 else if start a_k <= start a_j then a_j  `iJoin` r_i'
                                                else l_i' `iJoin` a_k
        ss_j = (ss_i . state) j'
        ss_k = (ss_i . state) k'
        ss_i' = all_possible_starts (union ss_j ss_k) [l_i', r_i']
    in DConjunction j' k' st{a_i = a_i', ss_i = ss_i', l_i = l_i', r_i = r_i'}

observe (DNegation j k st) ev =
    let j' = observe j ev
        k' = observe k ev
        a_j = (a_i . state) j'
        a_k = (a_i . state) k'
        t_i' = max (t_i st) (start a_k)
        a_i' = if t_i' < start(a_j) then a_j else []
        ss_i' = (ss_i . state) j'
    in DNegation j' k' st{a_i = a_i', ss_i = ss_i', t_i = t_i'}

observe (DSequence j k st) ev =
    let j' = observe j ev
        k' = observe k ev
        a_k = (a_i . state) k'
        a_j = (a_i . state) j'
        ss_j = (ss_i . state) j'
        ss_k = (ss_i . state) k'

        latest_prec t e' e = if end e < t && start e' < start e then e else e'
        e' = foldl (latest_prec (start a_k)) [] (union (qq_i st) [l_i st])
        a_i' = if e' /= [] then a_k `iJoin` e' else []

        qq_i' = foldl union [] $ [map (\t -> foldl (latest_prec t) [] (union (qq_i st) [l_i st])) ss_k]

        l_i' = starting_later (l_i st) a_j
        ss_i' = all_possible_starts ss_j (union (qq_i') [l_i'])

    in (DSequence j' k' st{a_i = a_i', qq_i=qq_i', l_i=l_i', ss_i=ss_i'})


observe (DTempRestr j t st) ev =
    let j' = observe j ev
        a_j = (a_i . state) j'
        a_i' = if (end a_j - start a_j) <= t then a_j else []
        ss_i' = (ss_i . state) j
    in DTempRestr j' t st{a_i = a_i', ss_i = ss_i'}


observe (DLastRestr j dur st) ev@[(cur_t, _)] =
    let j' = observe j ev
        a_j = (a_i . state) j'
        ss_j = (ss_i . state) j'

        latest_prec t e' e = if end e < t && start e' < start e then e else e'
        e' = foldl (latest_prec (start ev - dur)) [] (union (qq_i st) [l_i st])
        a_i' = if e' /= [] then ev `iJoin` e' else []

        qq_i' = delete a_i' $ filter (\e -> end e >= cur_t - dur) (union (qq_i st) [l_i st])

        l_i' = if a_i' /= [] then [] else (if start (l_i st) < start a_j then a_j else (l_i st))
        ss_i' = all_possible_starts ss_j (union (qq_i') [l_i'])

    in (DLastRestr j' dur st{a_i = a_i', qq_i=qq_i', l_i=l_i', ss_i=ss_i'})


-- ----------------------------------------------------------------------
-- ----------------------------------------------------------------------
-- ----------------------------------------------------------------------


-- detect :: Detector -> [Instance] -> [Maybe Instance]
-- detect d is = let d' = scanl observe d is
              -- in map (\d'' -> case (a_i . state) d'' of [] -> Nothing; a  -> Just a) d'


-- TODO: now that it works, make it aware of some reaction types and report that
-- instead of matched event patterns
data Reaction = R1 | R2 | R3 | R4
                deriving (Show, Eq)

detectME :: [(EventExpr, Reaction)] -> [Instance] -> [(Reaction, Instance)]
detectME es is = let ds = map (\(e, r) -> (makeDetector e, r)) es
                     ds' :: [[(Detector, Reaction)]]
                     ds' = scanl (\dss i -> map (\(d, r) -> (observe d i, r)) dss) ds is
                     ds'' = map (concat . map (\(d, r) -> case (a_i . state) d of [] -> []; a -> [(r, a)])) ds'
                 in concat ds''

justReactions xs = map fst xs
detectMER es is = justReactions $ (detectME es is)

-- example
-- detectME [(((E Alarm .& 3) .- (E MouseClick)), R1), (E Alarm, R2)] [[(1, Alarm)], [(5, Tick)], [(7, MouseClick)], [(10, Alarm)]]
--
-- detects 3 patterns:
--  [(R2,[(1,Alarm)]),
--   (R1,[(5,Tick),
--        (1,Alarm)]),
--   (R2,[(10,Alarm)])]

t@@e = [(t, e)]

event_stream0 = [[]]
event_stream1 = [1@@Alarm, 5@@Tick, 7@@MouseClick, 10@@Alarm]
event_stream2 = [1@@Alarm, 5@@Tick, 6@@Alarm, 7@@MouseClick, 10@@MouseClick]
event_stream3 = [1@@Alarm, 5@@Tick, 6@@MouseClick, 7@@Alarm, 10@@MouseClick]
event_stream4 = [1@@Alarm, 2@@Alarm, 5@@Tick, 6@@MouseClick, 7@@Alarm, 10@@MouseClick]
event_stream5 = [1@@Alarm, 2@@Alarm, 5@@Tick, 6@@MouseClick]

det1  = [(((E Alarm .& 3) .- (E MouseClick)), R1), (E Alarm, R2)]
det2  = [((E Alarm .& 3), R1)]
det3  = [(((E Alarm .& 3) .> E MouseClick), R1)]
det4  = [((((E Alarm .> E Alarm) .@ 20) .- E MouseClick), R1)]
det5  = [((((E Alarm .> E Alarm) .@ 20) .- (E Tick .| E MouseClick)), R1)]
det6  = [((((E Alarm .> E Alarm) .@ 20) .- (E Tick .+ E MouseClick)), R1)]
det7  = [((((E Alarm .> E Alarm) .@ 20) .- (E MouseClick .+ E Tick)), R1)]
det8  = [(((E Alarm .+ E Tick) .> E Alarm), R1)]
det9  = [(((E Alarm .+ E Tick) .> E Alarm) .> E MouseClick, R1)]
det10 = [((E Alarm .> (E Tick .+ E MouseClick) .> E Alarm), R1)]
det11 = [((E Alarm .> (E Tick .| E MouseClick) .> E Alarm), R1)]
det12 = [(E Alarm .> ((E Alarm .> E MouseClick) .- E Tick), R1)]
det13 = [((E Alarm .+ E MouseClick) .@ 3, R1)]

tests_suite1 = TestList
  [ TestLabel "test1"  $ TestCase (assertEqual "eq" [R2, R1, R2] (detectMER det1 event_stream1))
  , TestLabel "test2"  $ TestCase (assertEqual "eq" [R1, R1]     (detectMER det2 event_stream2))
  , TestLabel "test3"  $ TestCase (assertEqual "eq" [R1, R1]     (detectMER det3 event_stream2))
  , TestLabel "test4"  $ TestCase (assertEqual "eq" [R1]         (detectMER det4 event_stream2))
  , TestLabel "test5"  $ TestCase (assertEqual "eq" []           (detectMER det5 event_stream2))
  , TestLabel "test6"  $ TestCase (assertEqual "eq" [R1]         (detectMER det6 event_stream2))
  , TestLabel "test7"  $ TestCase (assertEqual "eq" []           (detectMER det6 event_stream3))
  , TestLabel "test8"  $ TestCase (assertEqual "eq" []           (detectMER det7 event_stream3))
  , TestLabel "test9"  $ TestCase (assertEqual "eq" [R1]         (detectMER det8 event_stream3))
  , TestLabel "test10" $ TestCase (assertEqual "eq" []           (detectMER det8 event_stream0))
  , TestLabel "test11" $ TestCase (assertEqual "eq" [R1]         (detectMER det9 event_stream3))
  , TestLabel "test12" $ TestCase (assertEqual "eq" [R1]         (detectMER det10 event_stream3))
  , TestLabel "test13" $ TestCase (assertEqual "eq" [(R1, [(7,Alarm),(5,Tick),(6,MouseClick),(2,Alarm)])] (detectME det10 event_stream4))
  , TestLabel "test14" $ TestCase (assertEqual "eq" [(R1, [(7,Alarm),(5,Tick),(2,Alarm)])]                (detectME det11 event_stream4))
  , TestLabel "test15" $ TestCase (assertEqual "eq" [(R1,[(10,MouseClick),(7,Alarm),(2,Alarm)])]          (detectME det12 event_stream4))
  , TestLabel "test16" $ TestCase (assertEqual "eq" []           (detectME det12 event_stream5))
  , TestLabel "test17" $ TestCase (assertEqual "eq" []           (detectME det13 event_stream5))
  , TestLabel "test18" $ TestCase (assertEqual "eq" [(R1, [(10,Alarm),(7,MouseClick)])]               (detectME det13 event_stream1))
  , TestLabel "test19" $ TestCase (assertEqual "eq" [(R1, [(6,Alarm),(1,Alarm)])]                     (detectME det7 event_stream2))
  , TestLabel "test20" $ TestCase (assertEqual "eq" [(R1, [(2,Alarm),(1,Alarm)])]                     (detectME det5 event_stream4))
  , TestLabel "test21" $ TestCase (assertEqual "eq" []                                                (detectME det14 event_stream4))
  ]



event_stream7 = [1@@Alarm, 2@@MouseClick, 3@@Tick, 4@@Tick, 5@@Tick, 6@@Alarm, 7@@Tick, 8@@Tick,
                 10@@Tick, 12@@MouseClick, 13@@Tick, 15@@Alarm, 16@@Tick, 17@@Alarm, 18@@Tick, 19@@Tick, 20@@Tick, 21@@KeyPress]

det14 = [(((E Alarm .& 2) .- E MouseClick) .> ((E Alarm .& 3) .- E KeyPress), R1)]
det15 = [(((E Alarm .& 3) .- E MouseClick), R1)]
det16 = [(((E Alarm .& 3) .- E KeyPress), R1)]
det17 = [((((E Alarm .+ E MouseClick) .@ 2) .- E MouseClick) .> ((E Alarm .@ 3) .- E KeyPress), R1)]

event_stream8 = [1@@MouseClick, 2@@KeyPress, 3@@Alarm, 4@@KeyPress]
event_stream9 = [1@@MouseClick, 2@@KeyPress, 3@@KeyPress, 4@@Alarm]

det18 = [((E KeyPress .> E KeyPress) .- (E MouseClick .+ E Alarm), R1)]
det19 = [((E MouseClick .+ E Alarm) .- (E KeyPress .> E KeyPress), R1)]

--det18 = [(((E Alarm .@ 3) .- E MouseClick), R1)]
--det19 = [(((E Alarm .@ 3) .- E KeyPress), R1)]


tests_suite2 = TestList
  [ TestLabel "test22" $ TestCase (assertEqual "eq" [(R1,[(19,Tick),(15,Alarm),(10,Tick),(6,Alarm)])] (detectME det14 event_stream7))
  , TestLabel "test23" $ TestCase (assertEqual "eq" [(R1, [(5,Tick),(1,Alarm)]),
                                                     (R1,[(10,Tick),(6,Alarm)]),
                                                     (R1, [(19,Tick),(15,Alarm)])]                    (detectME det16 event_stream7))
  , TestLabel "test24" $ TestCase (assertEqual "eq" [(R1,[(10,Tick),(6,Alarm)]),
                                                     (R1,[(19,Tick),(15,Alarm)]),
                                                     (R1,[(21,KeyPress),(17,Alarm)])]                 (detectME det15 event_stream7))
  , TestLabel "test25" $ TestCase (assertEqual "eq" []                                                (detectME det17 event_stream7))
  , TestLabel "test26" $ TestCase (assertEqual "eq" [(R1,[(4,KeyPress),(2,KeyPress)])]                (detectME det18 event_stream8))
  , TestLabel "test27" $ TestCase (assertEqual "eq" [(R1,[(1,MouseClick),(3,Alarm)])]                 (detectME det19 event_stream8))
  , TestLabel "test27" $ TestCase (assertEqual "eq" [(R1,[(3,KeyPress),(2,KeyPress)])]                (detectME det18 event_stream9))
  , TestLabel "test28" $ TestCase (assertEqual "eq" []                                                (detectME det19 event_stream9))
  ]


main = do
        runTestTT tests_suite1
        runTestTT tests_suite2
        -- putStrLn $ show $ detectME det3 event_stream2
