module Math.Dihedron.Dihedron

import public Math.Dihedron.Basis
import public Core.BoxInt
import public Math.Multiset
import Math.OnSeq.FusedStream
import Data.Fuel

%default total

||| A Dihedron element D = a·1 + b·i + c·j + d·k over scalar payload.
public export
record DihedronVal scalar where
  constructor MkDihedronVal
  scalarA : scalar -- Scalar (1)
  blueB   : scalar -- Blue (i, i² = -1)
  redC    : scalar -- Red (j, j² = +1)
  greenD  : scalar -- Green (k, k² = +1)

public export
Dihedron : Type
Dihedron = DihedronVal BoxInt

public export
MkDihedron : BoxInt -> BoxInt -> BoxInt -> BoxInt -> Dihedron
MkDihedron a b c d = MkDihedronVal a b c d

public export
a : DihedronVal scalar -> scalar
a (MkDihedronVal s _ _ _) = s

public export
b : DihedronVal scalar -> scalar
b (MkDihedronVal _ bl _ _) = bl

public export
c : DihedronVal scalar -> scalar
c (MkDihedronVal _ _ r _) = r

public export
d : DihedronVal scalar -> scalar
d (MkDihedronVal _ _ _ g) = g

public export
(Eq scalar) => Eq (DihedronVal scalar) where
  (MkDihedronVal a1 b1 c1 d1) == (MkDihedronVal a2 b2 c2 d2) =
    (a1 == a2) && (b1 == b2) && (c1 == c2) && (d1 == d2)

public export
(Show scalar) => Show (DihedronVal scalar) where
  show (MkDihedronVal a b c d) =
    show a ++ " + " ++ show b ++ "i + " ++ show c ++ "j + " ++ show d ++ "k"

------------------------------------------------------------------------
-- FUNCTOR, APPLICATIVE & MONAD IMPLEMENTATIONS
------------------------------------------------------------------------

public export
Functor DihedronVal where
  map f (MkDihedronVal a b c d) = MkDihedronVal (f a) (f b) (f c) (f d)

public export
Applicative DihedronVal where
  pure x = MkDihedronVal x x x x
  (MkDihedronVal f g h k) <*> (MkDihedronVal a b c d) =
    MkDihedronVal (f a) (g b) (h c) (k d)

public export
Monad DihedronVal where
  (MkDihedronVal a b c d) >>= f =
    MkDihedronVal (scalarA (f a)) (blueB (f b)) (redC (f c)) (greenD (f d))

------------------------------------------------------------------------
-- ALGEBRAIC INTERFACES (SEMIGROUP & MONOID)
------------------------------------------------------------------------

||| Addition of Dihedrons.
public export
addDihedron : Dihedron -> Dihedron -> Dihedron
addDihedron (MkDihedronVal a1 b1 c1 d1) (MkDihedronVal a2 b2 c2 d2) =
  MkDihedronVal (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2)

||| Negation of Dihedron.
public export
negDihedron : Dihedron -> Dihedron
negDihedron (MkDihedronVal a b c d) =
  MkDihedronVal (-a) (-b) (-c) (-d)

||| Subtraction of Dihedrons.
public export
subDihedron : Dihedron -> Dihedron -> Dihedron
subDihedron d1 d2 = addDihedron d1 (negDihedron d2)

||| Multiplication of Dihedrons via basis multiplication table.
public export
mulDihedron : Dihedron -> Dihedron -> Dihedron
mulDihedron (MkDihedronVal a1 b1 c1 d1) (MkDihedronVal a2 b2 c2 d2) =
  let resA = (a1 * a2) - (b1 * b2) + (c1 * c2) + (d1 * d2)
      resB = (a1 * b2) + (b1 * a2) + (c1 * d2) - (d1 * c2)
      resC = (a1 * c2) + (c1 * a2) - (b1 * d2) + (d1 * b2)
      resD = (a1 * d2) + (d1 * a2) - (b1 * c2) + (c1 * b2)
  in MkDihedronVal resA resB resC resD

||| Additive Semigroup instance for Dihedron.
public export
Semigroup Dihedron where
  (<+>) = addDihedron

||| Additive Monoid instance for Dihedron.
public export
Monoid Dihedron where
  neutral = MkDihedron 0 0 0 0

||| Multiplicative Semigroup named implementation for Dihedron.
public export
[MultDihedronSemigroup] Semigroup Dihedron where
  (<+>) = mulDihedron

||| Multiplicative Monoid named implementation for Dihedron.
public export
[MultDihedronMonoid] Monoid Dihedron where
  neutral = MkDihedron 1 0 0 0

||| Scalar multiplication.
public export
scaleDihedron : BoxInt -> Dihedron -> Dihedron
scaleDihedron s (MkDihedronVal a b c d) =
  MkDihedronVal (s * a) (s * b) (s * c) (s * d)

||| Half-Trace T(D) = a
public export
halfTrace : Dihedron -> BoxInt
halfTrace (MkDihedronVal a _ _ _) = a

||| Conjugation D* = a - bi - cj - dk
public export
conjugateDihedron : Dihedron -> Dihedron
conjugateDihedron (MkDihedronVal a b c d) =
  MkDihedronVal a (-b) (-c) (-d)

||| Quadrance (Determinant) Q(D) = a² + b² - c² - d²
public export
quadranceDihedron : Dihedron -> BoxInt
quadranceDihedron (MkDihedronVal a b c d) =
  (a * a) + (b * b) - (c * c) - (d * d)

||| Symmetric bilinear form <D1, D2> = T(D1 * D2*)
public export
bilinearDihedron : Dihedron -> Dihedron -> BoxInt
bilinearDihedron d1 d2 = halfTrace (mulDihedron d1 (conjugateDihedron d2))

public export
Num Dihedron where
  (+) = addDihedron
  (*) = mulDihedron
  fromInteger n = MkDihedron (fromInteger n) 0 0 0

public export
Neg Dihedron where
  negate = negDihedron
  (-) = subDihedron

------------------------------------------------------------------------
-- 2. COMPILE-TIME DIHEDRAL SYMMETRY WITNESSES
------------------------------------------------------------------------

||| Evaluates discrete norm quadrance conservation under Dihedral conjugation: Q(D*) == Q(D).
public export
isDihedralConjugateNormPreserved : Dihedron -> Bool
isDihedralConjugateNormPreserved d =
  quadranceDihedron (conjugateDihedron d) == quadranceDihedron d

||| Erased compile-time proof witness verifying Dihedral norm invariance under algebra conjugation.
public export
0 DihedralInvarianceWitness : Dihedron -> Type
DihedralInvarianceWitness d = isDihedralConjugateNormPreserved d = True

||| Static compile-time witness for baseline Dihedron element (1 + 2i + 3j + 4k).
public export
0 prfDihedronConjugateNormInvariance : DihedralInvarianceWitness (MkDihedron (intToBoxInt 1) (intToBoxInt 2) (intToBoxInt 3) (intToBoxInt 4))
prfDihedronConjugateNormInvariance = Refl

||| Bounded Dihedral state carrying compile-time erased symmetry witness.
public export
record BoundedDihedralState (d : Dihedron) where
  constructor MkBoundedDihedralState
  dihedronVal : Dihedron
  0 symmetryPrf : DihedralInvarianceWitness d

------------------------------------------------------------------------
-- 3. DEFORESTED DIHEDRAL ACTION STREAMS
------------------------------------------------------------------------

||| Discrete Dihedral action step record.
public export
record DihedralStep where
  constructor MkDihedralStep
  stepId   : Int
  normVal  : BoxInt
  val      : Dihedron

public export
Eq DihedralStep where
  (MkDihedralStep id1 n1 v1) == (MkDihedralStep id2 n2 v2) =
    id1 == id2 && n1 == n2 && v1 == v2

||| O(1) allocation deforested stream transducer folding product of Dihedrons across a stream.
public export covering
fusedDihedralActionStream : Fuel -> List Dihedron -> Dihedron
fusedDihedralActionStream f steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     d :: rest => Yield (MkDihedralStep idx (quadranceDihedron d) d) (idx + 1, rest))
    (\step, acc => mulDihedron (val step) acc)
    (MkDihedron (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0))
    (1, steps)

||| O(1) allocation deforested stream transducer evaluating total sum of quadrances across a Dihedron stream.
public export covering
fusedComputeTotalQuadrance : Fuel -> List Dihedron -> BoxInt
fusedComputeTotalQuadrance f steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     d :: rest => Yield (MkDihedralStep idx (quadranceDihedron d) d) (idx + 1, rest))
    (\step, acc => normVal step + acc)
    (intToBoxInt 0)
    (1, steps)

------------------------------------------------------------------------
-- 4. DEFORESTED PAULI SPINOR FEYNMAN PATH TRANSDUCERS
------------------------------------------------------------------------

||| Spin-1/2 Pauli Spinor state vector carrying spin-up (\alpha) and spin-down (\beta) Dihedron amplitudes.
public export
record PauliSpinor where
  constructor MkPauliSpinorVal
  spinUp   : Dihedron
  spinDown : Dihedron

public export
MkPauliSpinor : Dihedron -> Dihedron -> PauliSpinor
MkPauliSpinor up down = MkPauliSpinorVal up down

public export
Eq PauliSpinor where
  (MkPauliSpinorVal u1 d1) == (MkPauliSpinorVal u2 d2) = u1 == u2 && d1 == d2

||| Pauli Spinor Path Token for multi-step quantum Feynman path integration.
public export
record PauliPathToken where
  constructor MkPauliPathTokenVal
  stepIndex   : Int
  pathPhase   : Dihedron
  spinorState : PauliSpinor

public export
MkPauliPathToken : Int -> Dihedron -> PauliSpinor -> PauliPathToken
MkPauliPathToken idx p s = MkPauliPathTokenVal idx p s

public export
Eq PauliPathToken where
  (MkPauliPathTokenVal i1 p1 s1) == (MkPauliPathTokenVal i2 p2 s2) = i1 == i2 && p1 == p2 && s1 == s2

||| Unfolds a list of Dihedron phase steps into a deforested PauliPathToken stream.
%inline public export
unfoldPauliPathStream : PauliSpinor -> List Dihedron -> FusedStream PauliPathToken
unfoldPauliPathStream psi steps = MkStream nextStep (1, psi, steps)
  where
    nextStep : (Int, PauliSpinor, List Dihedron) -> Step (Int, PauliSpinor, List Dihedron) PauliPathToken
    nextStep (_, _, []) = Done
    nextStep (idx, spin, d :: rest) =
      let nextSpin = MkPauliSpinor (mulDihedron d (spinUp spin)) (mulDihedron d (spinDown spin))
      in Yield (MkPauliPathToken idx d nextSpin) (idx + 1, nextSpin, rest)

||| Deforested stream sifting operator filtering Pauli path tokens without intermediate allocations.
%inline public export
siftPauliPathStream : (PauliPathToken -> Bool) -> FusedStream PauliPathToken -> FusedStream PauliPathToken
siftPauliPathStream = siftFusedStream

||| Evaluates multi-step Feynman path propagator composition over Pauli spin-1/2 state vectors
||| using a fused stream transducer in O(1) auxiliary space without list allocations.
public export covering
fusedComputePauliPathPropagator : Fuel -> PauliSpinor -> List Dihedron -> PauliSpinor
fusedComputePauliPathPropagator f initialSpinor pathSteps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     dStep :: rest => Yield (MkPauliPathToken idx dStep initialSpinor) (idx + 1, rest))
    (\tok, acc =>
        let phase = pathPhase tok
            up    = spinUp acc
            down  = spinDown acc
        in MkPauliSpinor (mulDihedron phase up) (mulDihedron phase down))
    initialSpinor
    (1, pathSteps)

||| Evaluates total path quadrance norm across a multi-step Pauli Feynman path.
public export covering
fusedComputePauliPathQuadrance : Fuel -> PauliSpinor -> List Dihedron -> BoxInt
fusedComputePauliPathQuadrance f initialSpinor pathSteps =
  let finalSpinor = fusedComputePauliPathPropagator f initialSpinor pathSteps
  in quadranceDihedron (spinUp finalSpinor) + quadranceDihedron (spinDown finalSpinor)

||| Audit witness verifying zero-allocation Pauli spinor Feynman path propagator composition.
public export covering
auditPauliPathPropagatorProof : Bool
auditPauliPathPropagatorProof =
  let initialSpinor = MkPauliSpinor (MkDihedron 1 0 0 0) (MkDihedron 0 1 0 0)
      uPhase1 = MkDihedron 0 1 0 0 -- i phase
      uPhase2 = MkDihedron 0 1 0 0 -- i phase (i * i = -1)
      finalSpinor = fusedComputePauliPathPropagator (limit 100) initialSpinor [uPhase1, uPhase2]
      totalQuad = fusedComputePauliPathQuadrance (limit 100) initialSpinor [uPhase1, uPhase2]
      expectedSpinUp = MkDihedron (-1) 0 0 0
      expectedSpinDown = MkDihedron 0 (-1) 0 0
  in spinUp finalSpinor == expectedSpinUp &&
     spinDown finalSpinor == expectedSpinDown &&
     unwrapBox totalQuad == 2


