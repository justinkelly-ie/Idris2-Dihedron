module Math.Dihedron.Dihedron

import public Math.Dihedron.Basis
import public Core.BoxInt
import public Math.Multiset

%default total

||| A Dihedron element D = a·1 + b·i + c·j + d·k over BoxInt.
public export
record Dihedron where
  constructor MkDihedron
  scalarA : BoxInt -- Scalar (1)
  blueB   : BoxInt -- Blue (i, i² = -1)
  redC    : BoxInt -- Red (j, j² = +1)
  greenD  : BoxInt -- Green (k, k² = +1)

public export
a : Dihedron -> BoxInt
a (MkDihedron s _ _ _) = s

public export
b : Dihedron -> BoxInt
b (MkDihedron _ bl _ _) = bl

public export
c : Dihedron -> BoxInt
c (MkDihedron _ _ r _) = r

public export
d : Dihedron -> BoxInt
d (MkDihedron _ _ _ g) = g

public export
Eq Dihedron where
  (MkDihedron a1 b1 c1 d1) == (MkDihedron a2 b2 c2 d2) =
    (a1 == a2) && (b1 == b2) && (c1 == c2) && (d1 == d2)

public export
Show Dihedron where
  show (MkDihedron a b c d) =
    show a ++ " + " ++ show b ++ "i + " ++ show c ++ "j + " ++ show d ++ "k"

||| Addition of Dihedrons.
public export
addDihedron : Dihedron -> Dihedron -> Dihedron
addDihedron (MkDihedron a1 b1 c1 d1) (MkDihedron a2 b2 c2 d2) =
  MkDihedron (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2)

||| Negation of Dihedron.
public export
negDihedron : Dihedron -> Dihedron
negDihedron (MkDihedron a b c d) =
  MkDihedron (-a) (-b) (-c) (-d)

||| Subtraction of Dihedrons.
public export
subDihedron : Dihedron -> Dihedron -> Dihedron
subDihedron d1 d2 = addDihedron d1 (negDihedron d2)

||| Multiplication of Dihedrons via basis multiplication table.
public export
mulDihedron : Dihedron -> Dihedron -> Dihedron
mulDihedron (MkDihedron a1 b1 c1 d1) (MkDihedron a2 b2 c2 d2) =
  let resA = (a1 * a2) - (b1 * b2) + (c1 * c2) + (d1 * d2)
      resB = (a1 * b2) + (b1 * a2) + (c1 * d2) - (d1 * c2)
      resC = (a1 * c2) + (c1 * a2) - (b1 * d2) + (d1 * b2)
      resD = (a1 * d2) + (d1 * a2) - (b1 * c2) + (c1 * b2)
  in MkDihedron resA resB resC resD

||| Scalar multiplication.
public export
scaleDihedron : BoxInt -> Dihedron -> Dihedron
scaleDihedron s (MkDihedron a b c d) =
  MkDihedron (s * a) (s * b) (s * c) (s * d)

||| Half-Trace T(D) = a
public export
halfTrace : Dihedron -> BoxInt
halfTrace (MkDihedron a _ _ _) = a

||| Conjugation D* = a - bi - cj - dk
public export
conjugateDihedron : Dihedron -> Dihedron
conjugateDihedron (MkDihedron a b c d) =
  MkDihedron a (-b) (-c) (-d)

||| Quadrance (Determinant) Q(D) = a² + b² - c² - d²
public export
quadranceDihedron : Dihedron -> BoxInt
quadranceDihedron (MkDihedron a b c d) =
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
