/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.FiniteLeray
public import WeilConjectures.WeilSheaf.Finiteness

/-!
# Cohomology in degree zero of a Weil sheaf

The invariance `Γ(Ȳ, φ̄_* F) ≅ Γ(X̄, F)` of global sections under pushforward, as Frobenius
modules (`AlgebraicGeometry.WeilSheaf.globalSectionsLowerStarEquiv`), applied to the structure
morphism `a : X ⟶ Spec k₀`, together with `𝓗⁰(Ra_* F) ≅ a_* F`,
identifies `H⁰(X ⊗ k̄, F)` with the global sections `Γ(X̄, F)`, Frobenius-equivariantly.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.cohomologyZeroEquiv`: `H⁰(X ⊗ k̄, F) ≅ Γ(X̄, F)` as Frobenius
  modules.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology `H⁰(Y ⊗ k̄, G)` of a Weil sheaf is its space of global sections `Γ(Ȳ, G)`,
Frobenius-equivariantly: `H⁰ = Γ(Spec k̄, 𝓗⁰(Ra_* G)) ≅ Γ(Spec k̄, a_* G) ≅ Γ(Ȳ, G)`, by the left
exactness of `a_*` (`AlgebraicGeometry.WeilSheaf.homologySheafZeroDerivedLowerStarIso`) and the
invariance of global sections under pushforward
(`AlgebraicGeometry.WeilSheaf.globalSectionsLowerStarEquiv`).

Used for blueprint `lemma-degree-zero-top-cohomology--1` and `lemma-degree-zero-top-cohomology--2`
(step 3: `H⁰(U, -) = Γ(Ū, -)`). -/
noncomputable def cohomologyZeroEquiv (G : WeilSheaf k₀ l Y) :
    (G.cohomology 0).Equiv G.globalSections :=
  (globalSectionsEquivOfIso
    (homologySheafZeroDerivedLowerStarIso (Y ↘ Spec (CommRingCat.of k₀)) G)).trans
    (globalSectionsLowerStarEquiv (Y ↘ Spec (CommRingCat.of k₀)) G)

end AlgebraicGeometry.WeilSheaf
