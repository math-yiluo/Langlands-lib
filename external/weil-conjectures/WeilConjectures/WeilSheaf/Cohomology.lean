/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Compactly supported cohomology of Weil complexes

Let `k₀` be a finite field with algebraic closure `k̄` and geometric Galois Frobenius
`σ : Spec k̄ ≅ Spec k̄`. A Weil sheaf on `Spec k₀` is a constructible `ℓ`-adic sheaf `M` on
the pro-étale site of `Spec k̄` with an isomorphism `φ : σ^* M ≅ M`; its global sections
`Γ(Spec k̄, M)` carry the Frobenius

`Γ(Spec k̄, M) ≅ Γ(Spec k̄, σ^* M) --Γ(φ)--> Γ(Spec k̄, M)`

(`AlgebraicGeometry.WeilSheaf.globalSections`). Every pro-étale cover of `Spec k̄` splits, so
`Γ(Spec k̄, -)` is exact and the cohomology `Hʳ(Spec k̄, M)` of a Weil complex `M` on `Spec k₀`
is `Γ(Spec k̄, 𝓗ʳ M)`, the global sections of its `r`-th cohomology sheaf, with this Frobenius.

The compactly supported cohomology of a Weil complex `K` on a `k₀`-scheme `X` with structure
morphism `a : X ⟶ Spec k₀` is the cohomology `H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of its
direct image with compact support (`AlgebraicGeometry.WeilComplex.derivedLowerShriek`), with this
Frobenius.

## Main declarations

- `AlgebraicGeometry.WeilComplex.cohomologyFrobeniusModule`: the cohomology of a Weil complex on
  `Spec k₀` as a Frobenius module.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  with its geometric Frobenius.
- `AlgebraicGeometry.WeilComplex.cohomology` and `AlgebraicGeometry.WeilSheaf.cohomology`:
  ordinary cohomology `Hʳ(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_* K)` with its geometric Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry


variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

/-- The `r`-th cohomology `Hʳ(Spec k̄, M) = Γ(Spec k̄, 𝓗ʳ M)` of a Weil complex `(M, φ)` on
`Spec k₀`, as a Frobenius module: the global sections of its `r`-th cohomology sheaf, with the
Frobenius induced by the Weil structure (`AlgebraicGeometry.WeilSheaf.globalSections`). -/
noncomputable def cohomologyFrobeniusModule (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀)))
    (r : ℤ) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf r).obj M).globalSections

end WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

-- TODO(unify): thm:proetale-weil-perfectness
/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology.

The compactly supported cohomology `H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of a Weil
complex `K` on a separated `k₀`-scheme `a : X ⟶ Spec k₀` of finite type, with its geometric
Frobenius: the cohomology of the direct image with compact support of `K` along `a`, a Weil
complex on `Spec k₀`. Here `Hʳ(Spec k̄, -)` is the evaluation `Fib_s` at the geometric point
followed by `Hʳ` (`AlgebraicGeometry.WeilComplex.cohomologyFrobeniusModule`). The ordinary
cohomology is `AlgebraicGeometry.WeilComplex.cohomology`, the versions for Weil sheaves are
`AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology` and
`AlgebraicGeometry.WeilSheaf.cohomology`, and the constant coefficients `H_c^i(Y, ℚ̄_ℓ)` are
those of the constant Weil sheaf `AlgebraicGeometry.WeilSheaf.adicConstant`. The finite
coefficient stages are `AlgebraicGeometry.Etale.compactlySupportedCohomology` and
`AlgebraicGeometry.Etale.cohomology`. -/
noncomputable def compactlySupportedCohomology (K : WeilComplex k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K).cohomologyFrobeniusModule r

end WeilComplex

section Ordinary

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `def-weil-ordinary-compact-cohomology` (ordinary cohomology).

The ordinary cohomology `Hʳ(Y ⊗ k̄, K) := Hʳ(Spec k̄, Ra_* K)` of a Weil complex `K` on a
`k₀`-scheme `a : Y ⟶ Spec k₀` of finite type, with its geometric Frobenius: the cohomology of the
derived direct image of `K` along `a`, a Weil complex on `Spec k₀`. For `a` proper it agrees with
`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`. -/
noncomputable def WeilComplex.cohomology (K : WeilComplex k₀ l Y) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((derivedLowerStar (Y ↘ Spec (CommRingCat.of k₀))).obj K).cohomologyFrobeniusModule r

/-- The ordinary cohomology `Hʳ(Y ⊗ k̄, F)` of a Weil sheaf, with its geometric Frobenius: that of
the Weil complex `F` concentrated in degree zero. -/
noncomputable def WeilSheaf.cohomology (F : WeilSheaf k₀ l Y) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (toComplex.obj F).cohomology r

end Ordinary

namespace WeilSheaf

/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, F)` of a Weil sheaf, with its geometric
Frobenius: that of the Weil complex `F` concentrated in degree zero. -/
noncomputable def compactlySupportedCohomology (F : WeilSheaf k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (toComplex.obj F).compactlySupportedCohomology r

end WeilSheaf

end AlgebraicGeometry
