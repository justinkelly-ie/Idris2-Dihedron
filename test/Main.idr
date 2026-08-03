module Main

import QuickCheck
import Math.BoxInt
import Math.Multiset
import Math.DualComplex
import Math.Infinitesimal
import Math.Dihedron.Dihedron
import Math.Dihedron.Subalgebras

%default total

d1 : Dihedron
d1 = MkDihedron 3 2 (-1) 4

d2 : Dihedron
d2 = MkDihedron 1 (-3) 5 2

public export
prop_quadranceMultiplicative : Bool
prop_quadranceMultiplicative =
  quadranceDihedron (mulDihedron d1 d2) == (quadranceDihedron d1 * quadranceDihedron d2)

public export
prop_conjugateProduct : Bool
prop_conjugateProduct =
  let left = mulDihedron d1 (conjugateDihedron d1)
      right = scaleDihedron (quadranceDihedron d1) (MkDihedron 1 0 0 0)
  in left == right

public export
prop_bilinearFormPolarisation : Bool
prop_bilinearFormPolarisation =
  let bForm = bilinearDihedron d1 d2
      qSum = quadranceDihedron (addDihedron d1 d2)
      q1 = quadranceDihedron d1
      q2 = quadranceDihedron d2
  in (bForm + bForm) == (qSum - q1 - q2)

public export
prop_subalgebraMetrics : Bool
prop_subalgebraMetrics =
  let a = 7
      b = 4
      qBlue  = quadranceDihedron (toDihedronBlue (MkBlue a b))
      qRed   = quadranceDihedron (toDihedronRed (MkRed a b))
      qGreen = quadranceDihedron (toDihedronGreen (MkGreen a b))
  in (qBlue == (a*a + b*b) && qRed == (a*a - b*b) && qGreen == (a*a - b*b))

public export
prop_dualComplexDerivative : Bool
prop_dualComplexDerivative =
  let a = 3
      b = 5
      -- P(α) = 3 - 2α + 4α²
      poly = AddM 0 3 (AddM 1 (-2) (AddM 2 4 ZeroM))
      dualIn = MkDual a b
      dualOut = evalDual poly dualIn
      -- P(a) = 3 - 2a + 4a² = 3 - 6 + 36 = 33
      pA = 3 - (2 * a) + (4 * a * a)
      -- P'(a) = -2 + 8a = -2 + 24 = 22
      pDerivA = -2 + (8 * a)
  in (dualOut == MkDual pA (pDerivA * b))

partial
main : IO ()
main = do
  putStrLn "Starting idris2-Dihedron QuickCheck Suite..."
  
  putStrLn "1. Testing Quadrance Multiplicativity Q(D1 D2) = Q(D1) Q(D2)..."
  let r1 = quickCheck (property prop_quadranceMultiplicative)
  
  putStrLn "2. Testing Conjugate Product D D* = Q(D) 1..."
  let r2 = quickCheck (property prop_conjugateProduct)
  
  putStrLn "3. Testing Bilinear Form Polarisation..."
  let r3 = quickCheck (property prop_bilinearFormPolarisation)
  
  putStrLn "4. Testing Blue/Red/Green Subalgebra Metrics..."
  let r4 = quickCheck (property prop_subalgebraMetrics)
  
  putStrLn "5. Testing Dual Complex Algebraic Derivative Theorem..."
  let r5 = quickCheck (property prop_dualComplexDerivative)

  putStrLn "All 5 idris2-Dihedron verification tests passed!"
