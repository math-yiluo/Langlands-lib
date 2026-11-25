/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelWeilCoherence

/-!
# Weil sheaves pulled back from the model

Let `k₀` be a finite field, `X₀` a `k₀`-scheme, `p : X̄ ⟶ X₀` the projection of its geometric
fiber and `Fr_X = 𝟙 × σ` the geometric Galois Frobenius of `X̄`. Since `Fr_X ≫ p = p`, the
pullback `p^* H` of an `ℓ`-adic sheaf `H` on `X₀` carries the canonical Weil structure
```
Fr_X^* p^* H = (Fr_X⁻¹)_* p^* H ≅ Fr_X^* p^* H ≅ (Fr_X ≫ p)^* H = p^* H,
```
which makes `p^*` a functor from `ℓ`-adic sheaves on `X₀` to pro-étale Weil sheaves on `X₀`
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`). The pullback of a lisse sheaf is a
lisse, hence constructible, Weil sheaf (`AlgebraicGeometry.WeilSheaf.geometricFiberPullback`).

These are the Weil sheaves that come from étale sheaves on the model; together with the constant
twists (`AlgebraicGeometry.WeilSheaf.constantTwist`) they are the Weil sheaves through which the
comparison with the Weil objects of the trace formula chapter is made.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso`: the invariance
  `p^* ⋙ Fr_X^* ≅ p^*` in the pushforward convention of the Weil sheaves.
- `AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`: `H ↦ (p^* H, can)`.
- `AlgebraicGeometry.WeilSheaf.geometricFiberPullback`: the same for lisse `H`, as Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

namespace ProEtaleWeilSheaf

/-- The pullback `p^*` along the projection `p : X̄ ⟶ X₀` of the geometric fibre is invariant
under the Frobenius pullback `Fr_X^* = (Fr_X⁻¹)_*` of the Weil sheaves:
`p^* ⋙ (Fr_X⁻¹)_* ≅ p^* ⋙ Fr_X^* ≅ (Fr_X ≫ p)^* = p^*`, since `Fr_X ≫ p = p`
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj`). -/
noncomputable def geometricFiberPullbackFrobeniusIso :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l] ⋙
        WeilSheaf.frobeniusPullback k₀ l X ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _
      (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫
    adicUpperStarCongr l
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)

/-- **Weil sheaves pulled back from the model**: an `ℓ`-adic sheaf `H` on `X₀` gives the
pro-étale Weil sheaf `p^* H` on `X₀`, with the canonical Weil structure
`Fr_X^* p^* H ≅ (Fr_X ≫ p)^* H = p^* H`
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso`). -/
noncomputable def geometricFiberPullback : AdicSheaf l X ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.functorOfNatIso _ (geometricFiberPullbackFrobeniusIso k₀ l X)

@[simp]
lemma geometricFiberPullback_obj_carrier (H : AdicSheaf l X) :
    ((geometricFiberPullback k₀ l X).obj H).carrier =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H :=
  rfl

lemma geometricFiberPullback_obj_str (H : AdicSheaf l X) :
    ((geometricFiberPullback k₀ l X).obj H).str =
      (geometricFiberPullbackFrobeniusIso k₀ l X).app H :=
  IsoAlgebra.mk_str _ _

end ProEtaleWeilSheaf

variable {k₀ l X} [Fact (ringChar k₀ ≠ l)]

/-- The Weil sheaf `p^* H` pulled back from a lisse `ℓ`-adic sheaf `H` on the model `X₀`, with
its canonical Weil structure (`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`); it
is lisse (`AlgebraicGeometry.WeilSheaf.isLisse_geometricFiberPullback`). -/
noncomputable def WeilSheaf.geometricFiberPullback {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) : WeilSheaf k₀ l X where
  obj := (ProEtaleWeilSheaf.geometricFiberPullback k₀ l X).obj H
  property := (hH.upperStar _).isAdicConstructibleSheaf

/-- The pullback of a lisse sheaf from the model is a lisse Weil sheaf. -/
theorem WeilSheaf.isLisse_geometricFiberPullback {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) : (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH).IsLisse :=
  hH.upperStar _

end AlgebraicGeometry
