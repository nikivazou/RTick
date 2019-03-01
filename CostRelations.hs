
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}

module CostRelations where

import RTick
import ProofCombinators

--
-- Formalisation of cost relations, including relationships between the
-- them. For example, t1 >~> t2 ==> t2 <~< t1.
--
-------------------------------------------------------------------------------
-- | Cost equivalence:
-------------------------------------------------------------------------------

--
-- Cost equivalence is reflexive:
--
-- ∀t. t <=> t.
--
{-@ reflCostEq :: t:(Tick a) -> { COSTEQ t t } @-}
reflCostEq :: Tick a -> Proof
reflCostEq _ = ()

--
-- Cost equivalence is transitive:
--
-- ∀t1,t2,t3. [(t1 <=> t2 && t2 <=> t3) ==> (t1 <=> t3)].
--
{-@ transCostEq :: t1:(Tick a) -> t2:(Tick a) -> t3:(Tick a)
    -> { p1:Proof | COSTEQ t1 t2 }
    -> { p2:Proof | COSTEQ t2 t3 }
    -> { COSTEQ t1 t3 }
@-}
transCostEq :: Tick a -> Tick a -> Tick a -> Proof -> Proof -> Proof
transCostEq _ _ _ _ _ = ()

--
-- Cost equivalence is antisymmetric:
--
-- ∀t1,t2. [(t1 <=> t2 && t2 <=> t1) ==> (t1 == t2)].
--
{-@ antiSymCostEq :: t1:(Tick a) -> t2:(Tick a)
    -> { p1:Proof | COSTEQ t1 t2 }
    -> { p2:Proof | COSTEQ t2 t1 }
    -> { t1 == t2 }
@-}
antiSymCostEq :: Tick a -> Tick a -> Proof -> Proof -> Proof
antiSymCostEq (Tick n x) (Tick m y) _ _ = ()

--
-- Cost equivalence is commutative:
--
-- ∀t1,t2. [(t1 <=> t2) ==> (t2 <=> t1)].
--
{-@ commCostEq :: t1:(Tick a) -> t2:(Tick a)
    -> { p:Proof | COSTEQ t1 t2 }
    -> { COSTEQ t2 t1 }
@-}
commCostEq :: Tick a -> Tick a -> Proof -> Proof
commCostEq _ _ _ = ()

--
-- Cost equivalence implies every other relation:
--
-- ∀t1,t2. [ (t1 <=> t2) ==>
--             ( (t1 >~> t2) && (t2 >~> t1)
--                           &&
--               (t1 <~< t2) && (t2 <~< t1)
--                           &&
--         (t1 >== 0 ==> t2) && (t2 >== 0 ==> t1)
--                           &&
--         (t1 <== 0 ==< t2) && (t2 <== 0 ==< t1) ]
--
{-@ costEqAll :: t1:Tick a -> t2:Tick a
    -> { p:Proof | COSTEQ t1 t2 }
    -> { IMP t1 t2 && QIMP t1 0 t2 && DIM t1 t2 &&
         IMP t2 t1 && QIMP t2 0 t1 && DIM t2 t1 }
@-}
costEqAll :: Tick a -> Tick a -> Proof -> Proof
costEqAll _ _ _ = ()

--
-- Improvement and diminishment imply cost equivalence:
--
-- ∀t1,t2. [(t1 >~> t2 && t2 <~< t1) ==> (t1 <=> t2)].
--
{-@ impDimCostEq :: t1:(Tick a) -> t2:(Tick a)
    -> { p1:Proof | IMP t1 t2 }
    -> { p2:Proof | DIM t1 t2 }
    -> { COSTEQ t1 t2 }
@-}
impDimCostEq :: Tick a -> Tick a -> Proof -> Proof -> Proof
impDimCostEq _ _ _ _ = ()

--
-- If t1 is improved by t2, and t2 is improved by t1, then t1 and t2 are
-- cost-equivalent:
--
-- ∀t1,t2. [(t1 >~> t2 && t2 >~> t1) ==> (t1 <=> t2)].
--
{-@ impImpCostEq :: t1:(Tick a) -> t2:(Tick a)
    -> { p1:Proof | IMP t1 t2 }
    -> { p2:Proof | IMP t2 t1 }
    -> { COSTEQ t1 t2 }
@-}
impImpCostEq :: Tick a -> Tick a -> Proof -> Proof -> Proof
impImpCostEq _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | Improvement:
-------------------------------------------------------------------------------

--
-- Improvement is reflexive:
--
-- ∀t. t >~> t.
--
{-@ reflImp :: t:(Tick a) -> { IMP t t } @-}
reflImp :: Tick a -> Proof
reflImp _ = ()

--
-- Improvement is transitive:
--
-- ∀t1,t2,t3. [(t1 >~> t2 && t2 >~> t3) ==> (t1 >~> t3)].
--
{-@ transImp :: t1:(Tick a) -> t2:(Tick a) -> t3:(Tick a)
    -> { p1:Proof | IMP t1 t2 }
    -> { p2:Proof | IMP t2 t3 }
    -> { IMP t1 t3 }
@-}
transImp :: Tick a -> Tick a -> Tick a -> Proof -> Proof -> Proof
transImp _ _ _ _ _ = ()

--
-- Improvement is antisymmetric:
--
-- ∀t1,t2. [(t1 >~> t2 && t2 >~> t1) ==> (t1 == t2)].
--
{-@ antiSymImp :: t1:(Tick a) -> t2:(Tick a)
    -> { p1:Proof | IMP t1 t2 }
    -> { p2:Proof | IMP t2 t1 }
    -> { t1 == t2 }
@-}
antiSymImp :: Tick a -> Tick a -> Proof -> Proof -> Proof
antiSymImp (Tick m x) (Tick n y) _ _ = ()

--
-- Improvement and diminishment are opposites, i.e.,
-- t1 is improved by t2  iff  t2 is diminished by t1:
--
-- ∀t1,t2. [(t1 >~> t2 ==> t2 <~< t1) && (t2 <~< t1 ==> t1 >~> t2)].
--

--
-- ∀t1,t2. [(t1 >~> t2) ==> (t2 <~< t1)].
--
{-@ impDim :: t1:(Tick a) -> t2:(Tick a)
    -> { p:Proof | IMP t1 t2 }
    -> { DIM t2 t1 }
@-}
impDim :: Tick a -> Tick a -> Proof -> Proof
impDim _ _ _ = ()

--
-- ∀t1,t2. [(t2 <~< t1) ==> (t1 >~> t2)].
--
{-@ dimImp :: t1:(Tick a) -> t2:(Tick a)
    -> { p:Proof | DIM t2 t1 }
    -> { IMP t1 t2 }
@-}
dimImp :: Tick a -> Tick a -> Proof -> Proof
dimImp _ _ _ = ()

--
-- Improvement and quantified improvement are equivalent, but quantified
-- improvement is more explicit:
--
-- ∀t1,t2. [ [(t1 >~> t2) ==> (∃n. t1 >== n ==> t2)] &&
--           [(∃n. t1 >== n ==> t2) ==> (t1 >~> t2]) ].
--

--
-- ∀t1,t2. [(t1 >~> t2) ==> (∃n. t1 >== n ==> t2)].
--
{-@ impQimp :: t1:(Tick a) -> t2:(Tick a)
    -> { p:Proof | IMP t1 t2 }
    -> { QIMP t1 (tcost t1 - tcost t2) t2 }
@-}
impQimp :: Tick a -> Tick a -> Proof -> Proof
impQimp _ _ _ = ()

--
-- ∀t1,t2,n. [(t1 >== n ==> t2) ==> (t1 >~> t2)].
--
{-@ qimpImp :: t1:(Tick a) -> n:Nat -> t2:(Tick a)
    -> { p:Proof | QIMP t1 n t2 }
    -> { IMP t1 t2 }
@-}
qimpImp :: Tick a -> Int -> Tick a -> Proof -> Proof
qimpImp _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | Quantified improvement:
-------------------------------------------------------------------------------

--
-- Quantified improvement is reflexive:
--
-- ∀t. t >== 0 ==> t.
--
{-@ reflQimp :: t:(Tick a) -> { QIMP t 0 t } @-}
reflQimp :: Tick a -> Proof
reflQimp _ = ()

--
-- Quantified improvement is transitive:
--
-- ∀t1,t2,t3,n1,n2.
--   [(t1 >== n1 ==> t2 && t2 >== n2 ==> t3) ==> (t1 >== n1 + n2 ==> t3)].
--
{-@ transQimp :: t1:(Tick a) -> n1:Nat -> t2:(Tick a) -> n2:Nat -> t3:(Tick a)
    -> { p1:Proof | QIMP t1 n1 t2 }
    -> { p2:Proof | QIMP t2 n2 t3 }
    -> { QIMP t1 (n1 + n2) t3 }
@-}
transQimp
  :: Tick a
  -> Int
  -> Tick a
  -> Int
  -> Tick a
  -> Proof
  -> Proof
  -> Proof
transQimp _ _ _ _ _ _ _ = ()

--
-- Quantified improvement is antisymmetric:
--
-- ∀t1,t2,n. [(t1 >== n ==> t2 && t2 >== n ==> t1) ==> (t1 == t2)]
--
{-@ antiSymQimp :: t1:(Tick a) -> n:Nat -> t2:(Tick a)
    -> { p1:Proof | QIMP t1 n t2 }
    -> { p2:Proof | QIMP t2 n t1 }
    -> { t1 == t2 }
@-}
antiSymQimp :: Tick a -> Int -> Tick a -> Proof -> Proof -> Proof
antiSymQimp (Tick m x) _ (Tick n y) _ _ = ()

--
-- Quantified improvement and quantified diminishment are opposites, i.e.,
-- t1 is improved by t2, by a cost equal to n
--                      iff
-- t2 is diminished by t1, by a cost equal to n:
--
-- ∀t1,t2,n. [ ((t1 >== n ==> t2) ==> (t2 <== n ==< t1)) &&
--             ((t2 <== n ==< t1) ==> (t1 >== n ==> t2)) ].
--

--
-- ∀t1,t2,n. [(t1 >== n ==> t2) ==> (t2 <== n ==< t1)].
--
{-@ qimpQdim :: t1:(Tick a) -> n:Nat -> t2:(Tick a)
    -> { p:Proof | QIMP t1 n t2 }
    -> { QDIM t2 n t1 }
@-}
qimpQdim :: Tick a -> Int -> Tick a -> Proof -> Proof
qimpQdim _ _ _ _ = ()

--
-- ∀t1,t2,n. [(t2 <== n ==< t1) ==> (t1 >== n ==> t2)].
--
{-@ qdimQimp :: t1:(Tick a) -> n:Nat -> t2:(Tick a)
    -> { p:Proof | QDIM t2 n t1 }
    -> { QIMP t1 n t2 }
@-}
qdimQimp :: Tick a -> Int -> Tick a -> Proof -> Proof
qdimQimp _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | Diminishment:
-------------------------------------------------------------------------------

--
-- Diminishment is reflexive:
--
-- ∀t. t <~< t.
--
{-@ reflDim :: t:(Tick a) -> { DIM t t } @-}
reflDim :: Tick a -> Proof
reflDim _ = ()

--
-- Diminishment is transitive:
--
-- ∀t1,t2,t3. [((t1 <~< t2) && (t2 <~< t3)) ==> (t1 <~< t3)].
--
{-@ transDim :: t1:(Tick a) -> t2:(Tick a) -> t3:(Tick a)
    -> { p1:Proof | DIM t1 t2 }
    -> { p2:Proof | DIM t2 t3 }
    -> { DIM t1 t3 }
@-}
transDim
  :: Tick a
  -> Tick a
  -> Tick a
  -> Proof
  -> Proof
  -> Proof
transDim _ _ _ _ _ = ()

--
-- Diminishment is antisymmetric:
--
-- ∀t1,t2. [(t1 <~< t2 && t2 <~< t1) ==> (t1 == t2)].
--
{-@ antiSymDim :: t1:(Tick a) -> t2:(Tick a)
    -> { p1:Proof | DIM t1 t2 }
    -> { p2:Proof | DIM t2 t1 }
    -> { t1 == t2 }
@-}
antiSymDim :: Tick a -> Tick a -> Proof -> Proof -> Proof
antiSymDim (Tick m x) (Tick n y) _ _ = ()

--
-- Diminishment and quantified diminishment are equivalent, but quantified
-- diminishment is more explicit:
--
-- ∀t1,t2. [ [(t1 <~< t2) ==> (∃n. t1 <== n ==< t2)] &&
--           [(∃n. t1 <== n ==< t2) ==> (t1 <~< t2]) ].
--

--
-- ∀t1,t2. [(t1 <~< t2) ==> (∃n. t1 <== n ==< t2)].
--
{-@ dimQdim :: t1:(Tick a) -> t2:(Tick a)
    -> { p:Proof | DIM t1 t2 }
    -> { QDIM t1 (tcost t2 - tcost t1) t2 }
@-}
dimQdim :: Tick a -> Tick a -> Proof -> Proof
dimQdim _ _ _ = ()

--
-- ∀t1,t2,n. [(t1 <== n ==< t2) ==> (t1 <~< t2)].
--
{-@ qdimDim :: t1:(Tick a) -> n:Nat -> t2:(Tick a)
    -> { p:Proof | QDIM t1 n t2 }
    -> { DIM t1 t2 }
@-}
qdimDim :: Tick a -> Int -> Tick a -> Proof -> Proof
qdimDim _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | Quantified diminishment:
-------------------------------------------------------------------------------

--
-- Quantified diminishment is reflexive:
--
-- ∀t. t <== 0 ==< t.
--
{-@ reflQdim :: t:(Tick a) -> { QDIM t 0 t } @-}
reflQdim :: Tick a -> Proof
reflQdim _ = ()

--
-- Quantified diminishment is transitive:
--
-- ∀t1,t2,t3,n1,n2.
--   [((t1 <== n1 ==< t2) && (t2 <== n2 ==< t3)) ==> (t1 <== n1 + n2 ==< t3)].
--
{-@ transQdim :: t1:(Tick a) -> n1:Nat -> t2:(Tick a) -> n2:Nat -> t3:(Tick a)
    -> { p1:Proof | QDIM t1 n1 t2 }
    -> { p2:Proof | QDIM t2 n2 t3 }
    -> { QDIM t1 (n1 + n2) t3 }
@-}
transQdim
  :: Tick a
  -> Int
  -> Tick a
  -> Int
  -> Tick a
  -> Proof
  -> Proof
  -> Proof
transQdim _ _ _ _ _ _ _ = ()

--
-- Quantified diminishment is antisymmetric:
--
-- ∀t1,t2,n. [(t1 <== n ==< t2 && t2 <== n ==< t1) ==> (t1 == t2)]
--
{-@ antiSymQdim :: t1:(Tick a) -> n:Nat -> t2:(Tick a)
    -> { p1:Proof | QDIM t1 n t2 }
    -> { p2:Proof | QDIM t2 n t1 }
    -> { t1 == t2 }
@-}
antiSymQdim :: Tick a -> Int -> Tick a -> Proof -> Proof -> Proof
antiSymQdim (Tick m x) _ (Tick n y) _ _ = ()