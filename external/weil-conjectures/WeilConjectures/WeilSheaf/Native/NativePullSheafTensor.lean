/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import WeilConjectures.CategoryTheory.Monoidal.Mod.IsoAlgebraTensor
import WeilConjectures.WeilSheaf.IhomLisse.UpperStar
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorSheafComparisons

/-! # Native sheaf tensor and inverse image for any finite-field morphism -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory Functor.LaxMonoidal
attribute [local instance] Sheaf.symmetricCategory

-- Keep comparison data behind this wrapper when specializing to geometric Frobenius.
@[irreducible] private noncomputable def nativePullTensorStr
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    (b : Y ≅ Y) {M N : AdicSheaf l Y}
    (sM : (b.inv)_*ᵃ[l].obj M ≅ M) (sN : (b.inv)_*ᵃ[l].obj N ≅ N) :
    (b.inv)_*ᵃ[l].obj ((Mod.tensorLeft M).obj N) ≅ (Mod.tensorLeft M).obj N :=
  (adicLowerStarTensorLeftIso l b.inv M).app N ≪≫
    (Mod.tensorLeftMapIso sM).app _ ≪≫ (Mod.tensorLeft M).mapIso sN

private lemma native_pull_tensor_comm {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (E : (g)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (g)^*ᵃ[l])
    (θ : (g)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ⟶
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (g)^*[WeilCoefficients.{u} l])
    [NatTrans.IsMonoidal θ]
    (hE : ∀ T : AdicSheaf l Y, (E.hom.app T).hom = θ.app T.X)
    (M N : AdicSheaf l Y) (sM : (b.inv)_*ᵃ[l].obj M ≅ M)
    (sN : (b.inv)_*ᵃ[l].obj N ≅ N) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l g M).hom.app N) ≫
        (nativePullTensorStr a (E.app M ≪≫ (g)^*ᵃ[l].mapIso sM)
          (E.app N ≪≫ (g)^*ᵃ[l].mapIso sN)).hom =
      (E.app _ ≪≫ (g)^*ᵃ[l].mapIso (nativePullTensorStr b sM sN)).hom ≫
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
  simpa only [nativePullTensorStr, Mod.tensorStrOfIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Mod.tensorLeftMapIso, adicUpperStarTensorLeftIso,
    adicLowerStarTensorLeftIso, adicUpperStar, adicLowerStar,
    Adjunction.modLeft, Adjunction.modRight, Category.assoc] using h

private lemma native_pull_tensor_comm_of_eq {l : ℕ} [Fact l.Prime]
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
    (hsMN : sMN = nativePullTensorStr b sM sN) (htM : tM = upperStarStr l c sM)
    (htN : tN = upperStarStr l c sN) (htMN : tMN = nativePullTensorStr a tM tN)
    (htS : tS = upperStarStr l c sMN) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l g M).hom.app N) ≫ tMN.hom =
      tS.hom ≫ (adicUpperStarTensorLeftIso l g M).hom.app N := by
  subst hsMN htM htN htMN htS
  exact native_pull_tensor_comm g a b (adicUpperStarExchangeIso l g a b c)
    (upperStarExchangeIso (WeilCoefficients.{u} l) g a b c).hom
    (adicUpperStarExchangeIso_hom_app_hom g a b c) M N sM sN

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (p : Z ⟶ Y)
  [p.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
private lemma native_pull_tensor_str (A B : ProEtaleWeilSheaf k₀ l Y) :
    (tensor k₀ l Y A B).str =
      ProEtale.nativePullTensorStr (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
        A.str B.str := by
  unfold ProEtale.nativePullTensorStr
  exact Endofunctor.IsoAlgebra.mk_str _ _

@[irreducible] private def pull_tensor_component (M N : ProEtaleWeilSheaf k₀ l Y) :
    (upperStar k₀ l p).obj (tensor k₀ l Y N M) ≅
      tensor k₀ l Z ((upperStar k₀ l p).obj N) ((upperStar k₀ l p).obj M) :=
  Endofunctor.IsoAlgebra.isoMk
    ((ProEtale.adicUpperStarTensorLeftIso l
      (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
        N.carrier).app M.carrier) (by
    rw [← Endofunctor.IsoAlgebra.str_hom, ← Endofunctor.IsoAlgebra.str_hom]
    exact ProEtale.native_pull_tensor_comm_of_eq _ _ _
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius p
        (comp_over p (Spec (CommRingCat.of k₀)))).symm N.str M.str _ _ _ _ _
      (native_pull_tensor_str k₀ l N M) (upperStar_obj_str p N) (upperStar_obj_str p M)
      (native_pull_tensor_str k₀ l _ _) (upperStar_obj_str p _))

omit [Fact (ringChar k₀ ≠ l)] in
private theorem pull_tensor_component_forget (M N : ProEtaleWeilSheaf k₀ l Y) :
    HEq ((pull_tensor_component k₀ l p M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier) := by
  unfold pull_tensor_component
  rfl

attribute [local irreducible] upperStar Mod.tensorLeft Mod.ihomAdjunction
  tensorIhomAdjunction

private theorem pull_tensor_iso_of_components
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
    (e : ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))) ⋙
          WeilSheaf.frobeniusPullback k₀ l Z ≅
      WeilSheaf.frobeniusPullback k₀ l Y ⋙ ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))))
    (hR : R = Endofunctor.IsoAlgebra.mapOfNatIso e)
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Y,
      R.obj (tensor k₀ l Y N M) ≅ tensor k₀ l Z (R.obj N) (R.obj M))
    (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier)) :
    ∃ r : nativeOpenSheafTensor k₀ l Y ⋙ R ≅
      R.prod R ⋙ nativeOpenSheafTensor k₀ l Z,
    ∀ M N, HEq ((r.hom.app (M, N)).hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier) := by
  exact ⟨sheafRestrictionIso_abstract k₀ l p R e hR rho hrho, hrho⟩

/-- Balanced sheaf inverse image commutes with the native diagonal tensor.
Source: Stacks 07A4 and the coefficient Frobenius precomposition equation.
(blueprint: lem-sf-native-pull-sheaf-tensor).

Proof: the ordinary adic tensor pullback comparison is invertible. Its square
with Frobenius follows from the monoidality of the coefficient exchange map.
The structure isomorphism of a native tensor is exactly tensorStr, and the
structure of inverse image is upperStarStr. The generic restriction_tensor_comm
lifts the ordinary comparison to invertible Frobenius algebras. Naturality in
both inputs follows by faithful forgetting, using the ordinary naturality
and the inverse-mate description of nativeTensorMap. No open-immersion property
is used; zero inputs, identity maps and empty schemes use the same formulas. -/
theorem native_pull_sheaf_tensor :
    ∃ rho : nativeOpenSheafTensor k₀ l Y ⋙ upperStar k₀ l p ≅
      (upperStar k₀ l p).prod (upperStar k₀ l p) ⋙ nativeOpenSheafTensor k₀ l Z,
    ∀ M N, HEq ((rho.hom.app (M, N)).hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier) := by
  exact pull_tensor_iso_of_components k₀ l p (upperStar k₀ l p)
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l p
      (comp_over p (Spec (CommRingCat.of k₀))))
    (upperStar_eq_transport k₀ l p)
    (pull_tensor_component k₀ l p) (pull_tensor_component_forget k₀ l p)

end AlgebraicGeometry.ProEtaleWeilSheaf
