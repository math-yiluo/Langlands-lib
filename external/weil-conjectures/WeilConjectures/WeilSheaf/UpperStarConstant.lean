/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.WeilSheaf.StalkConstantSheaf
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Pullback of the constant Weil sheaf

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pullback `φ^* ℚ̄_ℓ` of the constant Weil sheaf
is the constant Weil sheaf: the canonical isomorphism `φ̄^* ℚ̄_ℓ ≅ ℚ̄_ℓ` of pro-étale sheaves on
the geometric fibers is compatible with the Weil structures, by the cocycle condition for the
canonical morphisms `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.upperStarAdicConstantIso`: `φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

/-- The canonical morphisms `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` commute with an exchange `a ≫ g = g ≫ b`: the
composite `a^* g^* ℚ̄_ℓ ≅ (a ≫ g)^* ℚ̄_ℓ = (g ≫ b)^* ℚ̄_ℓ ≅ g^* b^* ℚ̄_ℓ ⟶ g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is
`a^* g^* ℚ̄_ℓ ⟶ a^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, both being the canonical morphism along `a ≫ g = g ≫ b`. -/
lemma ProEtale.upperStarAdicConstantSheafHom_exchange {l : ℕ} [Fact l.Prime]
    {Z W : Scheme.{u}} (a : Z ⟶ Z) (g : Z ⟶ W) (b : W ⟶ W) (p : a ≫ g = g ≫ b) :
    (ProEtale.upperStarComp _ a g).inv.app (ProEtale.adicConstantSheaf l W) ≫
        (ProEtale.upperStarCongr _ p).hom.app (ProEtale.adicConstantSheaf l W) ≫
        (ProEtale.upperStarComp _ g b).hom.app (ProEtale.adicConstantSheaf l W) ≫
        (g)^*[WeilCoefficients.{u} l].map (ProEtale.upperStarAdicConstantSheafHom l b) ≫
        ProEtale.upperStarAdicConstantSheafHom l g =
      (a)^*[WeilCoefficients.{u} l].map (ProEtale.upperStarAdicConstantSheafHom l g) ≫
        ProEtale.upperStarAdicConstantSheafHom l a := by
  rw [ProEtale.upperStarAdicConstantSheafHom_comp,
    ProEtale.upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom,
    ← ProEtale.upperStarAdicConstantSheafHom_comp, Iso.inv_hom_id_app_assoc]

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- The canonical morphism `φ̄^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` intertwines the Weil structures of `φ^* ℚ̄_ℓ` and of
`ℚ̄_ℓ`, on underlying sheaves. -/
lemma frobeniusStr_upperStar_adicConstant_comp (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ((upperStar φ).obj (adicConstant k₀ l Y)).frobeniusStr ≫
        ProEtale.upperStarAdicConstantSheafHom l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[
        WeilCoefficients.{u} l].map
          (ProEtale.upperStarAdicConstantSheafHom l
            (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))) ≫
        (adicConstant k₀ l X).frobeniusStr := by
  rw [frobeniusStr_upperStar, frobeniusStr_adicConstant, frobeniusStr_adicConstant,
    Category.assoc, Category.assoc, Category.assoc]
  -- `exact` times out in the kernel, unfolding `adicConstant` against `adicConstantSheaf`
  convert ProEtale.upperStarAdicConstantSheafHom_exchange (l := l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ _).symm using 4
  all_goals rfl

/-- **The pullback of the constant Weil sheaf is the constant Weil sheaf**: `φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
for a morphism `φ : X ⟶ Y` of `k₀`-schemes, the canonical isomorphism `φ̄^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.adicUpperStarUnitIso`) being compatible with the Weil
structures. -/
noncomputable def upperStarAdicConstantIso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (upperStar φ).obj (adicConstant k₀ l Y) ≅ adicConstant k₀ l X :=
  ObjectProperty.isoMk _ (IsoAlgebra.isoMk (ProEtale.adicUpperStarUnitIso l
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))) (by
      refine Mod.hom_ext _ _ ?_
      rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
        ← cancel_epi ((ProEtale.upperStarIsoLowerStarInv _
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app _),
        ← (ProEtale.upperStarIsoLowerStarInv _
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.naturality_assoc,
        ← Category.assoc ((ProEtale.upperStarIsoLowerStarInv _
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app _)]
      convert (frobeniusStr_upperStar_adicConstant_comp φ).symm using 2
      all_goals rfl))

end WeilSheaf

end AlgebraicGeometry
