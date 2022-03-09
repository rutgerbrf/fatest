{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad.Writer.Lazy
  ( MonadWriter (tell),
    execWriter,
    forM_,
    when,
  )
import Data.Bifunctor (first)
import Data.List (foldl', intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Text.Lare (RE (..), parseStr)

data DFA s a = DFA
  { dfaA :: Set.Set a,
    dfaQ :: Set.Set s,
    dfaI :: s,
    dfaF :: Set.Set s,
    dfaD :: Map.Map (s, a) s
  }

data NFA s a = NFA
  { nfaA :: Set.Set a,
    nfaQ :: Set.Set s,
    nfaI :: s,
    nfaF :: Set.Set s,
    nfaD :: Map.Map (s, a) (Set.Set s)
  }

data Partition a = Partition
  { partSet :: Set.Set a,
    partEqc :: a -> Set.Set a
  }

resolvePartition :: Ord a => Partition a -> Set.Set (Set.Set a)
resolvePartition part = Set.map (partEqc part) $ partSet part

instance (Ord a, Show a) => Show (Partition a) where
  show = show . resolvePartition

makeConcrete :: Ord a => Partition a -> Partition a
makeConcrete part =
  let mapping = Map.fromSet (partEqc part) (partSet part)
   in part {partEqc = (mapping Map.!)}

forAll :: Foldable t => t a -> (a -> Bool) -> Bool
forAll a f = foldl' (\c x -> c && f x) True a

nextPartition :: (Ord s, Ord a, Show s) => DFA s a -> Partition s -> Partition s
nextPartition dfa part =
  part
    { partEqc = \q ->
        Set.filter
          ( \q' ->
              forAll (dfaA dfa) $ \a ->
                partEqc part (dfaD dfa Map.! (q, a)) == partEqc part (dfaD dfa Map.! (q', a))
          )
          $ partEqc part q
    }

instance Ord a => Eq (Partition a) where
  p1 == p2 = resolvePartition p1 == resolvePartition p2

untilEq :: Eq a => (a -> a) -> a -> a
untilEq m a = snd $ until (uncurry (==)) (\(_, y) -> (y, m y)) (a, m a)

partitionFinal :: Ord s => DFA s a -> Partition s
partitionFinal dfa =
  let nonAccepting = dfaQ dfa Set.\\ dfaF dfa
      accepting = dfaF dfa
      eqc q =
        if
            | q `Set.member` accepting -> accepting
            | q `Set.member` nonAccepting -> nonAccepting
            | otherwise -> undefined
   in Partition {partSet = dfaQ dfa, partEqc = eqc}

minimizeDFA :: (Ord s, Ord a, Show s) => DFA s a -> DFA (Set.Set s) a
minimizeDFA dfa =
  let initialPart = partitionFinal dfa
      part = untilEq (nextPartition dfa . makeConcrete) initialPart
      q = resolvePartition part
   in dfa
        { dfaQ = q,
          dfaI = partEqc part $ dfaI dfa,
          dfaF = Set.map (partEqc part) $ dfaF dfa,
          dfaD =
            Map.fromSet
              ( \(p, a) -> let p' = head (Set.elems p) in partEqc part $ dfaD dfa Map.! (p', a)
              )
              $ Set.cartesianProduct q (dfaA dfa)
        }

data FA s a = FA {faA :: Set.Set a, faD :: (s, a) -> s}

faFromDFA :: (Ord s, Ord a) => DFA s a -> FA s a
faFromDFA dfa = FA {faA = dfaA dfa, faD = (dfaD dfa Map.!)}

faStep :: Ord s => FA s a -> Set.Set s -> Set.Set s
faStep fa =
  Set.unions
    . Set.map
      ( \q ->
          Set.map (\a -> faD fa (q, a)) $ faA fa
      )

faMultiStep :: Ord s => FA s a -> Set.Set s -> Set.Set s -> Set.Set s
faMultiStep fa ss frontier =
  let frontier' = faStep fa frontier Set.\\ frontier
   in if frontier' `Set.isSubsetOf` ss
        then ss
        else faMultiStep fa (Set.union ss frontier') frontier'

faReachable :: Ord s => FA s a -> s -> Set.Set s
faReachable fa from = faMultiStep fa froms froms
  where
    froms = Set.singleton from

dfaRemoveUnreached :: (Ord s, Ord a) => DFA s a -> DFA s a
dfaRemoveUnreached dfa =
  dfa
    { dfaQ = reached,
      dfaF = dfaF dfa `Set.intersection` reached
    }
  where
    reached = faReachable (faFromDFA dfa) (dfaI dfa)

toDFA :: (Ord s, Ord a) => NFA s a -> DFA (Set.Set s) a
toDFA nfa =
  let d (q, a) = Set.unions $ Set.map (\q' -> fromMaybe Set.empty $ nfaD nfa Map.!? (q', a)) q
      i = Set.singleton $ nfaI nfa
      q = faReachable (FA {faA = nfaA nfa, faD = d}) i
      f = Set.filter (\h -> not $ Set.null $ h `Set.intersection` nfaF nfa) q
   in DFA
        { dfaA = nfaA nfa,
          dfaI = i,
          dfaQ = q,
          dfaD = Map.fromSet d (Set.cartesianProduct q (nfaA nfa)),
          dfaF = f
        }

data NFAL s a = NFAL
  { nfalA :: Set.Set a,
    nfalQ :: Set.Set s,
    nfalI :: s,
    nfalF :: Set.Set s,
    nfalD :: Map.Map (s, Maybe a) (Set.Set s)
  }

lStep :: (Ord s, Ord a) => NFAL s a -> Set.Set s -> Set.Set s
lStep nfal = Set.unions . Set.map (\q -> nfalD nfal Map.! (q, Nothing))

lMultiStep :: (Ord s, Ord a) => NFAL s a -> Set.Set s -> Set.Set s -> Set.Set s
lMultiStep nfal ss frontier =
  let frontier' = lStep nfal frontier Set.\\ frontier
   in if frontier' `Set.isSubsetOf` ss
        then ss
        else lMultiStep nfal (Set.union ss frontier') frontier'

lClosure :: (Ord s, Ord a) => NFAL s a -> s -> Set.Set s
lClosure nfal s = lMultiStep nfal ss ss
  where
    ss = Set.singleton s

toNFA :: (Show s, Show a, Ord s, Ord a) => NFAL s a -> NFA s a
toNFA nfal =
  NFA
    { nfaA = nfalA nfal,
      nfaQ = nfalQ nfal,
      nfaI = nfalI nfal,
      nfaF =
        Set.filter
          ( \q ->
              not $ Set.null $ lClosure nfal q `Set.intersection` nfalF nfal
          )
          $ nfalQ nfal,
      nfaD =
        Map.unionsWith Set.union $
          Set.map
            ( \q ->
                let reachableFromQ = lClosure nfal q
                 in Map.foldrWithKey'
                      ( \(q', a) q'' total ->
                          if q' `Set.member` reachableFromQ
                            then case a of
                              Just a' -> Map.insertWith Set.union (q, a') q'' total
                              Nothing -> total
                            else total
                      )
                      Map.empty
                      (nfalD nfal)
            )
            (nfalQ nfal)
    }

newtype IntGenerator a = IntGenerator {runIntGenerator :: Int -> (Int, a)}

updateSnd :: (b -> c) -> (a, b) -> (a, c)
updateSnd f (x, y) = (x, f y)

instance Functor IntGenerator where
  fmap f a = IntGenerator $ updateSnd f . runIntGenerator a

instance Applicative IntGenerator where
  pure a = IntGenerator (,a)
  liftA2 f ia ib = IntGenerator $ \x ->
    let (x', a) = runIntGenerator ia x
        (x'', b) = runIntGenerator ib x'
     in (x'', f a b)

instance Monad IntGenerator where
  (>>=) ig f = IntGenerator $ \x ->
    let (x', a) = runIntGenerator ig x
     in runIntGenerator (f a) x'

nextInt :: IntGenerator Int
nextInt = IntGenerator $ \x -> (x + 1, x)

execIntGenerator :: IntGenerator a -> a
execIntGenerator ig = snd $ runIntGenerator ig 0

nfalDefaultD :: (Ord s, Ord a) => Set.Set s -> Map.Map (s, Maybe a) (Set.Set s)
nfalDefaultD q = Map.fromSet (Set.singleton . fst) $ Set.map (,Nothing) q

withNFALDefaultD :: (Ord s, Ord a) => Set.Set s -> [Map.Map (s, Maybe a) (Set.Set s)] -> Map.Map (s, Maybe a) (Set.Set s)
withNFALDefaultD q d = Map.unionsWith Set.union (nfalDefaultD q : d)

toNFAL :: Ord a => RE a -> NFAL Int a
toNFAL = execIntGenerator . toNFAL_

toNFAL_ :: Ord a => RE a -> IntGenerator (NFAL Int a)
toNFAL_ RE0 = do
  q0 <- nextInt
  let q = Set.singleton q0
  pure $
    NFAL
      { nfalA = Set.empty,
        nfalQ = q,
        nfalI = q0,
        nfalF = Set.empty,
        nfalD = nfalDefaultD q
      }
toNFAL_ RE1 = do
  q0 <- nextInt
  let q = Set.singleton q0
  pure $
    NFAL
      { nfalA = Set.empty,
        nfalQ = q,
        nfalI = q0,
        nfalF = q,
        nfalD = nfalDefaultD q
      }
toNFAL_ (REA a) = do
  q0 <- nextInt
  f <- nextInt
  let q = Set.fromList [q0, f]
  pure $
    NFAL
      { nfalA = Set.singleton a,
        nfalQ = q,
        nfalI = q0,
        nfalF = Set.singleton f,
        nfalD =
          withNFALDefaultD
            q
            [ Map.fromList [((q0, Just a), Set.singleton f)]
            ]
      }
toNFAL_ (REC a b) = do
  m1 <- toNFAL_ a
  m2 <- toNFAL_ b
  q0 <- nextInt
  f <- nextInt
  let q1 = nfalI m1
  let q2 = nfalI m2
  let f1 = head $ Set.toList $ nfalF m1
  let f2 = head $ Set.toList $ nfalF m2
  let q = Set.unions [nfalQ m1, nfalQ m2, Set.fromList [q0, f]]
  pure $
    NFAL
      { nfalA = nfalA m1 `Set.union` nfalA m2,
        nfalQ = q,
        nfalI = q0,
        nfalF = Set.singleton f,
        nfalD =
          withNFALDefaultD
            q
            [ Map.fromList
                [ ((q0, Nothing), Set.fromList [q1, q2]),
                  ((f1, Nothing), Set.singleton f),
                  ((f2, Nothing), Set.singleton f)
                ],
              nfalD m1,
              nfalD m2
            ]
      }
toNFAL_ (RES a b) = do
  m1 <- toNFAL_ a
  m2 <- toNFAL_ b
  let q1 = nfalI m1
  let q2 = nfalI m2
  let f1 = head $ Set.toList $ nfalF m1
  let f2 = head $ Set.toList $ nfalF m2
  let q = nfalQ m1 `Set.union` nfalQ m2
  pure $
    NFAL
      { nfalA = nfalA m1 `Set.union` nfalA m2,
        nfalQ = q,
        nfalI = q1,
        nfalF = Set.singleton f2,
        nfalD =
          withNFALDefaultD
            q
            [ Map.fromList [((f1, Nothing), Set.singleton q2)],
              nfalD m1,
              nfalD m2
            ]
      }
toNFAL_ (REK a) = do
  m1 <- toNFAL_ a
  q0 <- nextInt
  let q1 = nfalI m1
  let f1 = head $ Set.toList $ nfalF m1
  let q = Set.insert q0 $ nfalQ m1
  pure $
    NFAL
      { nfalA = nfalA m1,
        nfalQ = q,
        nfalI = q0,
        nfalF = Set.singleton q0,
        nfalD =
          withNFALDefaultD
            q
            [ Map.fromList [((f1, Nothing), Set.singleton q0), ((q0, Nothing), Set.singleton q1)],
              nfalD m1
            ]
      }

renumerateDFA :: (Ord s, Ord a) => DFA s a -> DFA Int a
renumerateDFA dfa =
  let q = Set.toAscList $ dfaQ dfa
      mapping = Map.fromAscList $ zip q [0 ..]
      numberOf = (mapping Map.!)
   in DFA
        { dfaA = dfaA dfa,
          dfaQ = Set.map numberOf $ dfaQ dfa,
          dfaI = mapping Map.! dfaI dfa,
          dfaF = Set.map numberOf $ dfaF dfa,
          dfaD = Map.map numberOf $ Map.mapKeys (first numberOf) (dfaD dfa)
        }

dfaOutgoing :: (Ord s, Ord a) => DFA s a -> s -> Map.Map s (Set.Set a)
dfaOutgoing dfa q =
  Set.foldr'
    ( \a ->
        Map.alter (Just . maybe (Set.singleton a) (Set.insert a)) (dfaD dfa Map.! (q, a))
    )
    Map.empty
    $ dfaA dfa

nfalOutgoing :: (Ord s, Ord a) => NFAL s a -> s -> Map.Map s (Set.Set (Maybe a))
nfalOutgoing nfal q =
  Set.foldr'
    ( \a total ->
        case nfalD nfal Map.!? (q, a) of
          Just statesForChar ->
            Set.foldr'
              ( Map.alter (Just . maybe (Set.singleton a) (Set.insert a))
              )
              total
              statesForChar
          Nothing ->
            total
    )
    Map.empty
    $ Set.insert Nothing (Set.map Just (nfalA nfal))

nfaOutgoing :: (Ord s, Ord a) => NFA s a -> s -> Map.Map s (Set.Set a)
nfaOutgoing nfa q =
  Set.foldr'
    ( \a total ->
        case nfaD nfa Map.!? (q, a) of
          Just statesForChar ->
            Set.foldr'
              ( Map.alter (Just . maybe (Set.singleton a) (Set.insert a))
              )
              total
              statesForChar
          Nothing ->
            total
    )
    Map.empty
    $ nfaA nfa

instance (Show s, Show a, Ord s, Ord a) => Show (NFAL s a) where
  show nfal = execWriter $ do
    tell "digraph {\n  rankdir=\"LR\";\n  start [shape=point];\n"
    forM_ (nfalQ nfal) $ \q -> do
      tell "  "
      tell $ show q
      if q `Set.member` nfalF nfal
        then tell " [shape=doublecircle]"
        else tell " [shape=circle]"
      tell ";\n"
    forM_ (nfalQ nfal) $ \q -> do
      let outgoing = nfalOutgoing nfal q
      forM_ (Map.keys outgoing) $ \q' -> do
        tell "  "
        tell $ show q
        tell " -> "
        tell $ show q'
        tell " [label="
        tell $ show $ intercalate ", " $ map show $ Set.toList $ outgoing Map.! q'
        tell "]"
        tell ";\n"
    tell "  start -> "
    tell $ show (nfalI nfal)
    tell ";\n"
    tell "}"

instance (Show s, Show a, Ord s, Ord a) => Show (NFA s a) where
  show nfa = execWriter $ do
    tell "digraph {\n  rankdir=\"LR\";\n  start [shape=point];\n"
    forM_ (nfaQ nfa) $ \q -> do
      tell "  "
      tell $ show q
      if q `Set.member` nfaF nfa
        then tell " [shape=doublecircle]"
        else tell " [shape=circle]"
      tell ";\n"
    forM_ (nfaQ nfa) $ \q -> do
      let outgoing = nfaOutgoing nfa q
      forM_ (Map.keys outgoing) $ \q' -> do
        tell "  "
        tell $ show q
        tell " -> "
        tell $ show q'
        tell " [label="
        tell $ show $ intercalate ", " $ map show $ Set.toList $ outgoing Map.! q'
        tell "]"
        tell ";\n"
    tell "  start -> "
    tell $ show (nfaI nfa)
    tell ";\n"
    tell "}"

instance (Show s, Show a, Ord s, Ord a) => Show (DFA s a) where
  show dfa = execWriter $ do
    tell "digraph {\n  rankdir=\"LR\";\n  start [shape=point];\n"
    forM_ (dfaQ dfa) $ \q -> do
      tell "  "
      tell $ show q
      if q `Set.member` dfaF dfa
        then tell " [shape=doublecircle]"
        else tell " [shape=circle]"
      tell ";\n"
    forM_ (dfaQ dfa) $ \q -> do
      let outgoing = dfaOutgoing dfa q
      forM_ (Map.keys outgoing) $ \q' -> do
        tell "  "
        tell $ show q
        tell " -> "
        tell $ show q'
        tell " [label="
        tell $ show $ intercalate ", " $ map show $ Set.toList $ outgoing Map.! q'
        tell "]"
        tell ";\n"
    tell "  start -> "
    tell $ show (dfaI dfa)
    tell ";\n"
    tell "}"

main :: IO ()
main = do
  args <- getArgs
  progName <- getProgName
  when (length args /= 2) $ do
    putStrLn $ "Expected exactly two arguments: " ++ progName ++ " <regex> <format>"
    putStrLn "Where <format> is one of [re, nfal, nfa, dfa, mdfa]"
    exitFailure

  let reStr = head args
  re <- case parseStr reStr of
    Left errMsg -> do
      putStrLn $ "Could not parse the provided regex " ++ show reStr
      putStrLn $ "(Error: " ++ errMsg ++ ")"
      exitFailure
    Right tree ->
      pure tree
  let nfal = toNFAL re
  let nfa = toNFA nfal
  let dfa = renumerateDFA $ toDFA nfa
  let mdfa = renumerateDFA $ minimizeDFA dfa
  putStrLn $ case args !! 1 of
    "re" -> show re
    "nfal" -> show nfal
    "nfa" -> show nfa
    "dfa" -> show dfa
    "mdfa" -> show mdfa
    _ -> "Unknown format " ++ show (args !! 1)
