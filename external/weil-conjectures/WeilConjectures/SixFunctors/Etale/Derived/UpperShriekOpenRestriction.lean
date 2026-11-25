/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!
# The exceptional inverse image of a closed immersion restricted to an open

Let `i : Z ⟶ X` be a closed immersion and `W ⊆ X` an open subscheme, with `i ∣_ W : Z ∩ W ⟶ W`
the restricted closed immersion. Over a locally noetherian base, `Ri^!` commutes with the
restriction to `W`:

`j_Z^* Ri^! M ≅ R(i ∣_ W)^! j^* M`,

where `j : W ⟶ X` and `j_Z : Z ∩ W ⟶ Z` are the open immersions. Both sides are the exceptional
inverse image along `Z ∩ W ⟶ X`, by the composition law; over a locally noetherian base the
open immersions are quasi-compact, so their exceptional inverse images are the restrictions.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_mapDerivedCategory_upperStar_rightDerivedUpperShriek`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}}

/-- `Ri^!` commutes with the restriction to an open `W ⊆ X`: for the closed immersion
`i ∣_ W : Z ∩ W ⟶ W`, `j_Z^* Ri^! M ≅ R(i ∣_ W)^! j^* M`. Both sides are the exceptional inverse
image along `Z ∩ W ⟶ X` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`),
and the exceptional inverse image along a quasi-compact open immersion is the restriction
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`). -/
theorem nonempty_iso_mapDerivedCategory_upperStar_rightDerivedUpperShriek (i : Z ⟶ X)
    [IsClosedImmersion i] (W : X.Opens) [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((((i ⁻¹ᵁ W).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
        ((R(i)^![Λ]).obj M) ≅
      (R(i ∣_ W)^![Λ]).obj
        (((W.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj M)) := by
  have : HasCompactification (i ⁻¹ᵁ W).ι :=
    (Compactification.ofIsOpenImmersion (i ⁻¹ᵁ W).ι).hasCompactification
  have : HasCompactification W.ι := (Compactification.ofIsOpenImmersion W.ι).hasCompactification
  have : HasCompactification ((i ⁻¹ᵁ W).ι ≫ i) :=
    Compactification.hasCompactification
      { Z := Z, g := i, i := (i ⁻¹ᵁ W).ι, comm := rfl, isProper := inferInstance,
        isOpenImmersion := inferInstance }
  have : HasCompactification ((i ∣_ W) ≫ W.ι) :=
    HasCompactification.of_eq (morphismRestrict_ι i W).symm
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (i ⁻¹ᵁ W).ι i
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (i ∣_ W) W.ι
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq Λ
    (morphismRestrict_ι i W)
  exact ⟨(rightDerivedUpperShriekIsoOfIsOpenImmersion Λ (i ⁻¹ᵁ W).ι).symm.app _ ≪≫
    (e₁.app M).symm ≪≫ (e₃.app M).symm ≪≫ e₂.app M ≪≫
    (R(i ∣_ W)^![Λ]).mapIso
      ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ W.ι).app M)⟩

end Etale

end AlgebraicGeometry
