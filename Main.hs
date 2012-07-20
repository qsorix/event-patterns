-- implementation of an algorithm introduced by Jan Carlson in
-- Event Pattern Detection for Embedded Systems
--
-- I've added an operator 'last restriction' that accepts an event only after
-- some time. I'm not sure if my implementation is correct but it seems to work
-- in simple cases. With this operator I can say A and not B for 3 seconds which
-- is written as (A .@ 3) .- B
--
import List

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
        a_i' = if start(a_j) <= start(a_k) then a_k else a_j
        ss_i' = union ss_j ss_k
    in DDisjunction j' k' st{a_i = a_i', ss_i = ss_i'}

observe (DConjunction j k st) ev =
    let j' = observe j ev
        k' = observe k ev
        a_j = (a_i . state) j'
        a_k = (a_i . state) k'
        l_i' = if start(l_i st) < start(a_j) then a_j else l_i st
        r_i' = if start(r_i st) < start(a_k) then a_k else r_i st
        a_i' = if l_i' == [] || r_i' == [] || (a_j == [] && a_k == [])
                 then []
                 else if start a_k <= start a_j then a_j  `iJoin` r_i'
                                                else l_i' `iJoin` a_k
        ss_j = (ss_i . state) j'
        ss_k = (ss_i . state) k'
        ss_i' = delete (-1) (union (union ss_j ss_k) [start l_i', start r_i'])
    in DConjunction j' k' st{a_i = a_i', ss_i = ss_i', l_i = l_i', r_i = r_i'}

observe (DNegation j k st) ev =
    let j' = observe j ev
        k' = observe k ev
        a_j = (a_i . state) j'
        a_k = (a_i . state) k'
        t_i' = if (t_i st) < start(a_k) then start(a_k) else (t_i st)
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

        l_i' = if start (l_i st) < start a_j then a_j else (l_i st)
        ss_i' = delete (-1) (ss_j `union` map start (union (qq_i') [l_i']))

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

        l_i' = if start (l_i st) < start a_j then a_j else (l_i st)
        ss_i' = delete (-1) (ss_j `union` map start (union (qq_i') [l_i']))

    in (DLastRestr j' dur st{a_i = a_i', qq_i=qq_i', l_i=l_i', ss_i=ss_i'})



a = E Alarm
b = E MouseClick
c = E KeyPress


da    = makeDetector $  a
dab   = makeDetector $ (a .| b)
daab  = makeDetector $ (a .+ b)
dabnc = makeDetector $ (a .+ b) .- c


detectE :: EventExpr -> [Instance] -> [Maybe Instance]
detectE e is = detect (makeDetector e) is


detect :: Detector -> [Instance] -> [Maybe Instance]
detect d is = let d' = scanl observe d is
              in map (\d'' -> case (a_i . state) d'' of [] -> Nothing; a  -> Just a) d'


-- TODO: now that it works, make it aware of some reaction types and report that
-- instead of matched event patterns
data Reaction = R1 | R2 | R3 | R4
                deriving (Show)

detectME :: [(EventExpr, Reaction)] -> [Instance] -> [(Reaction, Instance)]
detectME es is = let ds = map (\(e, r) -> (makeDetector e, r)) es
                     ds' :: [[(Detector, Reaction)]]
                     ds' = scanl (\dss i -> map (\(d, r) -> (observe d i, r)) dss) ds is
                     ds'' = map (concat . map (\(d, r) -> case (a_i . state) d of [] -> []; a -> [(r, a)])) ds'
                 in concat ds''

-- example
-- detectME [(((E Alarm .& 3) .- (E MouseClick)), R1), (E Alarm, R2)] [[(1, Alarm)], [(5, Tick)], [(7, MouseClick)], [(10, Alarm)]]
--
-- detects 3 patterns:
--  [(R2,[(1,Alarm)]),
--   (R1,[(5,Tick),
--        (1,Alarm)]),
--   (R2,[(10,Alarm)])]

