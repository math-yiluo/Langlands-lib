/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Dual
import WeilConjectures.CategoryTheory.Monoidal.Mod.IsoAlgebraTensor
import WeilConjectures.WeilSheaf.IhomLisse.UpperStar

/-! # Equivariant balanced tensor restriction

Source: Stacks 03EL, 0E8I and the native open tensor argument, step 2.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory Functor.LaxMonoidal

attribute [local instance] Sheaf.symmetricCategory

-- Keep comparison data behind this wrapper when specializing to geometric Frobenius.
@[irreducible] private noncomputable def tensorStr {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    (b : Y ≅ Y) {M N : AdicSheaf l Y}
    (sM : (b.inv)_*ᵃ[l].obj M ≅ M) (sN : (b.inv)_*ᵃ[l].obj N ≅ N) :
    (b.inv)_*ᵃ[l].obj ((Mod.tensorLeft M).obj N) ≅ (Mod.tensorLeft M).obj N :=
  (adicLowerStarTensorLeftIso l b.inv M).app N ≪≫
    (Mod.tensorLeftMapIso sM).app _ ≪≫ (Mod.tensorLeft M).mapIso sN

private lemma restriction_tensor_comm {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (E : (g)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (g)^*ᵃ[l])
    (θ : (g)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ⟶
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (g)^*[WeilCoefficients.{u} l])
    [NatTrans.IsMonoidal θ]
    (hE : ∀ T : AdicSheaf l Y, (E.hom.app T).hom = θ.app T.X)
    (M N : AdicSheaf l Y) (sM : (b.inv)_*ᵃ[l].obj M ≅ M)
    (sN : (b.inv)_*ᵃ[l].obj N ≅ N) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l g M).hom.app N) ≫
        (tensorStr a (E.app M ≪≫ (g)^*ᵃ[l].mapIso sM) (E.app N ≪≫ (g)^*ᵃ[l].mapIso sN)).hom =
      (E.app _ ≪≫ (g)^*ᵃ[l].mapIso (tensorStr b sM sN)).hom ≫
          (adicUpperStarTensorLeftIso l g M).hom.app N := by
  have : (Mod.mapModComap (G := (a.inv)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l a.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l a.inv
  have : (Mod.mapModComap (G := (b.inv)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l b.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l b.inv
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  have h := Mod.tensorLeftCompMapModComapIso_tensorStr_comm
    (G := (g)^*[WeilCoefficients.{u} l])
    (F := (b.inv)_*[WeilCoefficients.{u} l])
    (F' := (a.inv)_*[WeilCoefficients.{u} l])
    (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
    (adicConstantSheafToLowerStar l b.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _)
    (adicConstantSheafToLowerStar l a.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _)
    θ (fun T ↦ E.hom.app T) M N (hE M) (hE N) (hE _) sM.hom sN.hom
  simpa only [tensorStr, Mod.tensorStrOfIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Mod.tensorLeftMapIso, adicUpperStarTensorLeftIso,
    adicLowerStarTensorLeftIso, adicUpperStar, adicLowerStar,
    Adjunction.modLeft, Adjunction.modRight, Category.assoc] using h

private lemma restriction_tensor_comm_of_eq {l : ℕ} [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (c : a.hom ≫ g = g ≫ b.hom) {M N : AdicSheaf l Y}
    (sM : (b.inv)_*ᵃ[l].obj M ≅ M) (sN : (b.inv)_*ᵃ[l].obj N ≅ N)
    (sMN : (b.inv)_*ᵃ[l].obj ((Mod.tensorLeft M).obj N) ≅ (Mod.tensorLeft M).obj N)
    (tM : (a.inv)_*ᵃ[l].obj ((g)^*ᵃ[l].obj M) ≅ (g)^*ᵃ[l].obj M)
    (tN : (a.inv)_*ᵃ[l].obj ((g)^*ᵃ[l].obj N) ≅ (g)^*ᵃ[l].obj N)
    (tMN : (a.inv)_*ᵃ[l].obj
        ((Mod.tensorLeft ((g)^*ᵃ[l].obj M)).obj ((g)^*ᵃ[l].obj N)) ≅
      (Mod.tensorLeft ((g)^*ᵃ[l].obj M)).obj ((g)^*ᵃ[l].obj N))
    (tS : (a.inv)_*ᵃ[l].obj ((g)^*ᵃ[l].obj ((Mod.tensorLeft M).obj N)) ≅
      (g)^*ᵃ[l].obj ((Mod.tensorLeft M).obj N))
    (hsMN : sMN = tensorStr b sM sN) (htM : tM = upperStarStr l c sM)
    (htN : tN = upperStarStr l c sN) (htMN : tMN = tensorStr a tM tN)
    (htS : tS = upperStarStr l c sMN) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l g M).hom.app N) ≫ tMN.hom =
      tS.hom ≫ (adicUpperStarTensorLeftIso l g M).hom.app N := by
  subst hsMN htM htN htMN htS
  exact restriction_tensor_comm g a b (adicUpperStarExchangeIso l g a b c)
    (upperStarExchangeIso (WeilCoefficients.{u} l) g a b c).hom
    (adicUpperStarExchangeIso_hom_app_hom g a b c) M N sM sN

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
private lemma tensor_str (A B : ProEtaleWeilSheaf k₀ l Z) :
    (tensor k₀ l Z A B).str =
      ProEtale.tensorStr (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
        A.str B.str := by
  unfold ProEtale.tensorStr
  exact Endofunctor.IsoAlgebra.mk_str _ _

-- Retain the existing open-immersion binder of the public interface.
set_option linter.unusedSectionVars false in
/-- The actual balanced restriction/tensor comparison lifts to Weil sheaves.

Source: Stacks Project, sites-modules.tex, Tags 03EL and 0E8I; step 2 of
lem-sf-native-open-sheaf-tensor-existence.
(blueprint: lem-sf-native-open-restriction-tensor).

Proof: the ordinary coefficient pullback is the map on locally finite functions
induced by precomposition. Its balanced tensor comparison sends a pulled-back
pure tensor to the tensor of its two pullbacks. Apply this formula before and
after Frobenius. Both maps pull back the same two sections and then apply their
Weil structures, since j is defined over the finite field. The equality descends
through the balanced quotient and sheafification. Lift this ordinary comparison
and its inverse to the category of invertible Frobenius algebras. The inverse
identities and naturality follow by faithful forgetting from the ordinary ones.
This proves the stated underlying-map normalization as well. The construction
works on the empty open, the identity open and zero inputs without alteration. -/
theorem native_open_restriction_tensor :
    ∃ rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
        tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M),
      ∀ M N, HEq ((rho M N).hom.hom.f)
        ((ProEtale.adicUpperStarTensorLeftIso l
          (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier) := by
  let rho (M N : ProEtaleWeilSheaf k₀ l Z) :
      (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
        tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M) :=
    Endofunctor.IsoAlgebra.isoMk
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).app M.carrier) (by
      rw [← Endofunctor.IsoAlgebra.str_hom, ← Endofunctor.IsoAlgebra.str_hom]
      exact ProEtale.restriction_tensor_comm_of_eq _ _ _
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius j
          (comp_over j (Spec (CommRingCat.of k₀)))).symm N.str M.str _ _ _ _ _
        (tensor_str k₀ l N M) (upperStar_obj_str j N) (upperStar_obj_str j M)
        (tensor_str k₀ l _ _) (upperStar_obj_str j _))
  exact ⟨rho, fun _ _ ↦ HEq.rfl⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
