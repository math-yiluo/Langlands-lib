/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStar

/-!
# Pullback of the dual of a lisse Weil sheaf

For a lisse Weil sheaf `G` on `Y` and a morphism `φ : X ⟶ Y` of `k₀`-schemes, the dual of the
pullback is the pullback of the dual (`AlgebraicGeometry.WeilSheaf.upperStarDualIso`), and
pullback of pro-étale Weil sheaves commutes with the internal hom out of the dual
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section DualHelpers

variable {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The underlying pro-étale Weil sheaf of a pullback. -/
lemma WeilSheaf.upperStar_obj_obj (G : WeilSheaf k₀ l Y) :
    ((WeilSheaf.upperStar φ).obj G).obj = (ProEtaleWeilSheaf.upperStar k₀ l φ).obj G.obj :=
  rfl

variable (k₀ l Y) in
/-- The underlying pro-étale Weil sheaf of the constant Weil sheaf. -/
lemma WeilSheaf.adicConstant_obj :
    (WeilSheaf.adicConstant k₀ l Y).obj = ProEtaleWeilSheaf.adicConstant k₀ l Y :=
  rfl

/-- The underlying pro-étale Weil sheaf of the dual. -/
lemma WeilSheaf.dual_obj [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l X) (hG : G.IsLisse) :
    (G.dual hG).obj = (ProEtaleWeilSheaf.ihomFunctor k₀ l X G.obj).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X) :=
  rfl

/-- `φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ` for pro-étale Weil sheaves. -/
noncomputable def ProEtaleWeilSheaf.upperStarAdicConstantIso :
    (ProEtaleWeilSheaf.upperStar k₀ l φ).obj (ProEtaleWeilSheaf.adicConstant k₀ l Y) ≅
      ProEtaleWeilSheaf.adicConstant k₀ l X :=
  eqToIso (by rw [← WeilSheaf.adicConstant_obj, ← WeilSheaf.upperStar_obj_obj]; rfl) ≪≫
    (ObjectProperty.ι _).mapIso (WeilSheaf.upperStarAdicConstantIso φ) ≪≫
    eqToIso (WeilSheaf.adicConstant_obj k₀ l X)

end DualHelpers

/-- The dual of the pullback of a lisse Weil sheaf is the pullback of its dual. -/
noncomputable def WeilSheaf.upperStarDualIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    ((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ≅
      (WeilSheaf.upperStar φ).obj (G.dual hG) :=
  ObjectProperty.isoMk _
    (eqToIso (by rw [WeilSheaf.dual_obj, WeilSheaf.upperStar_obj_obj]) ≪≫
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj G.obj)).mapIso
        (ProEtaleWeilSheaf.upperStarAdicConstantIso φ).symm ≪≫
      ((ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso φ G.obj hG).app
        (ProEtaleWeilSheaf.adicConstant k₀ l Y)).symm ≪≫
      eqToIso (by rw [WeilSheaf.upperStar_obj_obj, WeilSheaf.dual_obj, Functor.comp_obj]))

/-- Pullback of pro-étale Weil sheaves commutes with the internal hom out of the dual of a lisse
Weil sheaf. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    ProEtaleWeilSheaf.ihomFunctor k₀ l Y (G.dual hG).obj ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ ≅
      ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj :=
  ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso φ (G.dual hG).obj hG.dual ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft
      ((ObjectProperty.ι _).mapIso (WeilSheaf.upperStarDualIso φ G hG)))

end AlgebraicGeometry
