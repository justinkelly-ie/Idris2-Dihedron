# FinSc-Dihedron

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 3d 4D Clifford Hypercomplex Subalgebras & Spatial Torsion for Idris 2**

`FinSc-Dihedron` forms **Layer 3d** of the 10-layer constructive non-linear multiset science framework. It formalizes 4D Clifford hypercomplex basis elements ($1, i, j, k$), dihedral group actions, metric splitting into elliptic, hyperbolic, and parabolic components, and discrete 4D spatial torsion.

---

## 📦 Core Library Architecture & Modules

### 1. `Math.Dihedron.Basis`
- **4D Hypercomplex Basis:** Fundamental basis elements ($1, i, j, k$) obeying hypercomplex multiplication rules over exact rational numbers.
- **Vector Operations:** Basis vector addition, scalar multiplication, and norm calculations.

### 2. `Math.Dihedron.Dihedron`
- **Dihedron Hypercomplex Algebra:** Elements $q = a + bi + cj + dk$ over rational subfields.
- **Algebraic Multiplications:** Non-commutative hypercomplex products, conjugates, and inverse norms.

### 3. `Math.Dihedron.Subalgebras`
- **Metric Splitting:** Subalgebra decompositions partitioning 4D spacetime into Elliptic (Euclidean), Hyperbolic (Minkowski), and Parabolic (flat) metric components.
- **Dihedral Group Actions & Spatial Torsion:** Dihedral symmetry transformations ($D_n$) tracking discrete spatial torsion and metric rotations.

---

## 🚀 Building & Installing

```bash
idris2 --build FinSc-Dihedron.ipkg
idris2 --install FinSc-Dihedron.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all hypercomplex algebra modules.
- **Discrete 4D Torsion:** Dihedral group actions parameterizing spatial torsion without continuous manifold charts.
- **Zero Floating-Point Drift:** Hypercomplex coefficients evaluated over exact rational numbers (`UnixelFraction`).
