/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Exactness of finite pushforwards of `ℓ`-adic and Weil sheaves

The pushforward along a finite morphism of finite presentation is exact on pro-étale sheaves of
modules (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite`). We
transport this to `ℓ`-adic sheaves, the forgetful functor reflecting finite colimits, and to
pro-étale Weil sheaves, whose pushforward along `φ` is that of `ℓ`-adic sheaves along the base
change `φ̄` to `k̄`, with transported Weil structure.

## Main statements

- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isFinite`
- `AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}

/-- The pushforward of `ℓ`-adic sheaves along a finite morphism of finite presentation is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite`). -/
theorem preservesFiniteColimits_adicLowerStar_of_isFinite (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] : PreservesFiniteColimits (f)_*ᵃ[l] := by
  have := preservesFiniteColimits_lowerStar_of_isFinite (ULift.{u + 1} (PadicAlgCl l)) f
  have : PreservesFiniteColimits ((f)_*ᵃ[l] ⋙ AdicSheaf.forget Y) :=
    inferInstanceAs (PreservesFiniteColimits (AdicSheaf.forget X ⋙ (f)_*[WeilCoefficients.{u} l]))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (AdicSheaf.forget Y)

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The pushforward of pro-étale Weil sheaves along a finite morphism of finite presentation is
exact: it is the pushforward of `ℓ`-adic sheaves along the base change to `k̄`, which is again
finite of finite presentation. -/
theorem ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [IsFinite φ] [LocallyOfFinitePresentation φ] :
    PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l φ) := by
  have : IsFinite (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) φ _ ‹_›
  have : LocallyOfFinitePresentation
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
      (P := @LocallyOfFinitePresentation) φ _ ‹_›
  have := ProEtale.preservesFiniteColimits_adicLowerStar_of_isFinite l
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
  exact Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

end AlgebraicGeometry
