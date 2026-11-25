/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Finite coefficients and geometric categories for the trace formula

Source: Weil blueprint, sec-trace-formula/sk-d-setup, order 2610
(blueprint: sk-d-setup), with the geometric-scope correction recorded in the DAG.

For `F : FiniteFieldDatum`, the base is `Spec (.of F.k)`. Geometric schemes are
objects `X` of `Over (Spec (.of F.k))` with `IsSeparated X.hom`,
`LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`; their structure maps are
`X.hom`, and their maps are the morphisms of this over category. Products mean
`pullback X.hom Y.hom`. These conventions reuse the existing definitions.
Dimension is `topologicalKrullDim X`, reduction is `X.nilradical.subscheme`, and
universal homeomorphisms mean `(topologically IsHomeomorph).universally f`.
No additional geometric hypothesis is imposed by these final-reduction conventions.

The ambient category for every scheme is `Scheme.proEtaleDerivedCategory X A`.
Its bounded constructible finite-Tor property is the existing
`finiteTorConstructible l E n hn X`, defined by intrinsic constructibility and
`Scheme.HasFiniteProEtaleTorAmplitude`, without an invertibility restriction.
The full subcategory is its `FullSubcategory`. For any commutative ring `R`,
`DerivedCategory.IsPerfectRingComplex` defines `Perf(R)` using bounded complexes
of finitely generated projective modules. None of these notions is redefined here.

The package below fixes compactifications for compactifiable geometric maps and
requires precisely triangulatedness, repleteness and the two preservation properties.
The middle scheme of each compactification is geometric via `c.g ≫ Y.hom`:
proper morphisms are separated and of finite type, and these properties compose.
The equality `c.comm` makes its open immersion a map over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The fixed finite-coefficient geometric package at the positive level `n`.
The prime is different from the characteristic prime in the global finite-field datum.
The coefficient ring is the recorded quotient by the chosen uniformizer to power `n`.
The data are actual compactifications, with their open and proper maps, rather than
arbitrary functors. The property uses their actual composite `Rg_* j_!` on the whole
ordinary unbounded category. No compactification-independence assertion is made here;
that assertion has only the bounded-below etale-origin scope of its dependency.
Triangulatedness and repleteness concern only geometric schemes, while the existing
ambient and finite-Tor definitions still apply to all schemes.

Source: Weil blueprint, sec-trace-formula/sk-d-setup, order 2610, as corrected by
the reviewed DAG's geometric-scope restriction (blueprint: sk-d-setup). -/
noncomputable def TraceFormulaCoefficientSetup
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) : Type _ :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  { cs : ∀ (X Y : Over (Spec (.of F.k)))
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (f : X ⟶ Y) [HasCompactification f.left], Compactification f.left //
    (∀ (X : Over (Spec (.of F.k)))
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
      (finiteTorConstructible l E n hn X.left).IsTriangulated ∧
        (finiteTorConstructible l E n hn X.left).IsClosedUnderIsomorphisms) ∧
    (∀ (X Y : Over (Spec (.of F.k)))
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (f : X ⟶ Y) (K : proEtaleDerivedCategory Y.left
        (Padic.coefficientExtensionRing l E n)),
      finiteTorConstructible l E n hn Y.left K →
        finiteTorConstructible l E n hn X.left
          ((sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E n) f.left).obj K)) ∧
    ∀ (X Y : Over (Spec (.of F.k)))
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (f : X ⟶ Y) [HasCompactification f.left]
      (K : proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E n)),
      finiteTorConstructible l E n hn X.left K →
        finiteTorConstructible l E n hn Y.left
          ((sfIntrinsicCompactSupport (cs X Y f) (Padic.coefficientExtensionRing l E n)).obj K) }

end WeilConjectures
