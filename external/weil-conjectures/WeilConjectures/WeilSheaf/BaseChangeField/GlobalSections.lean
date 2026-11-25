/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The Frobenius on global sections of transported Weil sheaves

The global sections `Γ(Ȳ, K)` of a pro-étale Weil sheaf `(K, φ)` carry the Frobenius
`Γ(Ȳ, K) ≅ Γ(Ȳ, Fr^* K) --Γ(φ)--> Γ(Ȳ, K)`
(`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsFrobenius`), as for Weil sheaves
(`AlgebraicGeometry.WeilSheaf.globalSections`). This file shows:

- the Frobenius is natural in `K`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsFrobenius_naturality`);
- the Frobenius through the iterated Weil structure `φ_m : (Frᵐ)^* K ≅ K` is the `m`-th power of
  the Frobenius (`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsFrobeniusPow_succ`);
- along an identification `θ : Ȳ ≅ Ȳ'` of geometric fibres with `θ ≫ Fr' = Frʳ ≫ θ`, the
  Frobenius of the transported Weil sheaf `(θ_* K, θ_* φ_r)` is the `r`-th power of that of `K`
  under `Γ(Ȳ', θ_* K) ≅ Γ(Ȳ, K)`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsFrobenius_transport`);
- hence a Weil sheaf on a `k₀'`-scheme isomorphic to the transport of a Weil sheaf `H` on a
  `k₀`-scheme has the global sections of `H`, with Frobenius `Fʳ`
  (`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_globalSections_of_iso_transport`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace ProEtale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {R S T : Scheme.{u}}

/-- The invariance of global sections under pushforward along equal morphisms, inverted. -/
@[reassoc]
lemma globalSectionsLowerStarIso_inv_app_comp_congr {g g' : S ⟶ R} (h : g = g')
    (G : Sheaf (Scheme.ProEt.topology S) A) :
    (globalSectionsLowerStarIso A g).inv.app G ≫
        (Sheaf.Γ _ A).map ((lowerStarCongr A h).hom.app G) =
      (globalSectionsLowerStarIso A g').inv.app G := by
  subst h
  simp

/-- The invariance of global sections under pushforward is compatible with composition,
inverted. -/
@[reassoc]
lemma globalSectionsLowerStarIso_inv_app_comp_lowerStarComp_inv (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) A) :
    (globalSectionsLowerStarIso A (h₁ ≫ h₂)).inv.app G ≫
        (Sheaf.Γ _ A).map ((lowerStarComp A h₁ h₂).inv.app G) =
      (globalSectionsLowerStarIso A h₁).inv.app G ≫
        (globalSectionsLowerStarIso A h₂).inv.app ((h₁)_*[A].obj G) := by
  have h : (Sheaf.Γ _ A).mapIso ((lowerStarComp A h₁ h₂).app G) ≪≫
      (globalSectionsLowerStarIso A (h₁ ≫ h₂)).app G =
      (globalSectionsLowerStarIso A h₂).app ((h₁)_*[A].obj G) ≪≫
        (globalSectionsLowerStarIso A h₁).app G :=
    Iso.ext (globalSectionsLowerStarIso_comp A h₁ h₂ G)
  exact congrArg Iso.inv h

/-- The invariance of global sections under pushforward is compatible with composition,
inverted, with the composition isomorphism on the other side. -/
@[reassoc]
lemma globalSectionsLowerStarIso_inv_app_comp_lowerStarComp_hom (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) A) :
    (globalSectionsLowerStarIso A h₁).inv.app G ≫
        (globalSectionsLowerStarIso A h₂).inv.app ((h₁)_*[A].obj G) ≫
        (Sheaf.Γ _ A).map ((lowerStarComp A h₁ h₂).hom.app G) =
      (globalSectionsLowerStarIso A (h₁ ≫ h₂)).inv.app G := by
  rw [← globalSectionsLowerStarIso_inv_app_comp_lowerStarComp_inv_assoc]
  exact (congrArg (_ ≫ ·) ((Sheaf.Γ _ A).mapIso ((lowerStarComp A h₁ h₂).app G)).inv_hom_id).trans
    (Category.comp_id _)

end ProEtale

namespace ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius `Γ(Ȳ, K) ≅ Γ(Ȳ, Fr^* K) --Γ(φ)--> Γ(Ȳ, K)` on the global sections of a
pro-étale Weil sheaf `(K, φ)`; for Weil sheaves this is the Frobenius of
`AlgebraicGeometry.WeilSheaf.globalSections`. -/
def globalSectionsFrobenius (K : ProEtaleWeilSheaf k₀ l Y) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X ⟶
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X :=
  (globalSectionsLowerStarIso _
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app K.carrier.X ≫
    (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map K.str.hom)

/-- The Frobenius on global sections is natural. -/
@[reassoc]
lemma globalSectionsFrobenius_naturality {K K' : ProEtaleWeilSheaf k₀ l Y} (f : K ⟶ K') :
    K.globalSectionsFrobenius ≫ (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map f.hom.f) =
      (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map f.hom.f) ≫ K'.globalSectionsFrobenius := by
  rw [globalSectionsFrobenius, globalSectionsFrobenius, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, Endofunctor.IsoAlgebra.str_hom, Endofunctor.IsoAlgebra.str_hom,
    ← f.hom.h, Functor.map_comp, Functor.map_comp]
  exact ((globalSectionsLowerStarIso (WeilCoefficients.{u} l) _).inv.naturality_assoc _ _).symm

/-- The Frobenius `Γ(Ȳ, K) ≅ Γ(Ȳ, (Frᵐ)^* K) --Γ(φ_m)--> Γ(Ȳ, K)` through the iterated Weil
structure `φ_m`. -/
def globalSectionsFrobeniusPow (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X ⟶
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X :=
  (globalSectionsLowerStarIso _
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv).inv.app K.carrier.X ≫
    (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom)

lemma globalSectionsFrobeniusPow_zero (K : ProEtaleWeilSheaf k₀ l Y) :
    K.globalSectionsFrobeniusPow 0 = 𝟙 _ := by
  have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.inv = 𝟙 _ := by
    rw [pow_zero]
    rfl
  have e : (AdicSheaf.forget _).map (K.frobeniusPowIso 0).hom =
      (lowerStarCongr _ h).hom.app K.carrier.X ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom.app K.carrier.X := by
    rw [← adicLowerStarCongr_hom_app_hom, ← adicLowerStarId_hom_app_hom]
    rfl
  rw [globalSectionsFrobeniusPow, e, Functor.map_comp,
    globalSectionsLowerStarIso_inv_app_comp_congr_assoc, ← globalSectionsLowerStarIso_id,
    Iso.inv_hom_id_app]

/-- The Frobenius through `φ_{m+1}` is the Frobenius through `φ_m`, followed by the
Frobenius. -/
lemma globalSectionsFrobeniusPow_succ (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ) :
    K.globalSectionsFrobeniusPow (m + 1) =
      K.globalSectionsFrobeniusPow m ≫ K.globalSectionsFrobenius := by
  have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.inv =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv := by
    rw [pow_succ, Aut.mul_asIso, Iso.trans_inv]
  have e : (AdicSheaf.forget _).map (K.frobeniusPowIso (m + 1)).hom =
      (lowerStarCongr _ h).hom.app K.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l) _ _).inv.app K.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom) ≫
        (AdicSheaf.forget _).map K.str.hom := by
    rw [frobeniusPowIso]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Mod.forget_map,
      Mod.comp_hom', adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom,
      adicLowerStar_map_hom]
  have h₂ : (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app
        ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].obj
          K.carrier.X) ≫
        (Sheaf.Γ _ _).map
          (((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
            ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom)) =
      (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom) ≫
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app K.carrier.X :=
    ((globalSectionsLowerStarIso _ _).inv.naturality _).symm
  rw [globalSectionsFrobeniusPow, globalSectionsFrobeniusPow, globalSectionsFrobenius, e]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [globalSectionsLowerStarIso_inv_app_comp_congr_assoc,
    globalSectionsLowerStarIso_inv_app_comp_lowerStarComp_inv_assoc, reassoc_of% h₂]

/-- The Frobenius through `φ_m` is the `m`-th iterate of the Frobenius, pointwise. -/
lemma globalSectionsFrobeniusPow_apply (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ)
    (x : (WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X)) :
    ((WeilCoefficients.toModuleCat l).map (K.globalSectionsFrobeniusPow m)).hom x =
      (fun y ↦ ((WeilCoefficients.toModuleCat l).map K.globalSectionsFrobenius).hom y)^[m] x := by
  induction m with
  | zero =>
    rw [globalSectionsFrobeniusPow_zero, CategoryTheory.Functor.map_id]
    rfl
  | succ m ih =>
    rw [globalSectionsFrobeniusPow_succ, Functor.map_comp, Function.iterate_succ_apply', ← ih]
    rfl

section Transport

variable {k₀' : Type u} [Field k₀'] [Finite k₀']
  {Y' : Scheme.{u}} [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)

/-- Under the identification `Γ(Ȳ', θ_* K) ≅ Γ(Ȳ, K)`, the Frobenius of the transported Weil
sheaf `(θ_* K, θ_* φ_r)` is the Frobenius of `K` through `φ_r`. -/
lemma globalSectionsFrobenius_transport (K : ProEtaleWeilSheaf k₀ l Y) :
    (globalSectionsLowerStarIso _ θ.hom).inv.app K.carrier.X ≫
        ((transport θ r hθ).obj K).globalSectionsFrobenius ≫
        (globalSectionsLowerStarIso _ θ.hom).hom.app K.carrier.X =
      K.globalSectionsFrobeniusPow r := by
  have e : (AdicSheaf.forget _).map ((transport θ r hθ).obj K).str.hom =
      (lowerStarComp (WeilCoefficients.{u} l) θ.hom
          (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.inv).hom.app K.carrier.X ≫
        (lowerStarCongr _ (hom_comp_geometricGaloisFrobenius_inv θ r hθ)).hom.app K.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l)
          ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.inv
          θ.hom).inv.app K.carrier.X ≫
        (θ.hom)_*[_].map ((AdicSheaf.forget _).map (K.frobeniusPowIso r).hom) := by
    rw [transport_obj_str, transportCommIso]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, NatTrans.comp_app,
      Mod.forget_map, Mod.comp_hom', adicLowerStarComp_hom_app_hom, adicLowerStarCongr_hom_app_hom,
      adicLowerStarComp_inv_app_hom, adicLowerStar_map_hom, Category.assoc]
  rw [globalSectionsFrobenius, e]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [globalSectionsLowerStarIso_inv_app_comp_lowerStarComp_hom_assoc]
  rw [globalSectionsLowerStarIso_inv_app_comp_congr_assoc,
    globalSectionsLowerStarIso_inv_app_comp_lowerStarComp_inv_assoc]
  have h₂ : (globalSectionsLowerStarIso (WeilCoefficients.{u} l) θ.hom).inv.app
        ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.inv)_*[_].obj
          K.carrier.X) ≫
        (Sheaf.Γ _ _).map ((θ.hom)_*[_].map ((AdicSheaf.forget _).map (K.frobeniusPowIso r).hom)) =
      (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map (K.frobeniusPowIso r).hom) ≫
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l) θ.hom).inv.app K.carrier.X :=
    ((globalSectionsLowerStarIso _ θ.hom).inv.naturality _).symm
  rw [reassoc_of% h₂]
  rw [Iso.inv_hom_id_app]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- For `α : K' ≅ θ_* K`, the Frobenius of `K'` corresponds under
`Γ(Ȳ', K') ≅ Γ(Ȳ', θ_* K) ≅ Γ(Ȳ, K)` to the Frobenius of `K` through `φ_r`. -/
lemma globalSectionsFrobenius_comp_of_iso_transport (K : ProEtaleWeilSheaf k₀ l Y)
    {K' : ProEtaleWeilSheaf k₀' l Y'} (α : K' ≅ (transport θ r hθ).obj K) :
    K'.globalSectionsFrobenius ≫ (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map α.hom.hom.f) ≫
        (globalSectionsLowerStarIso _ θ.hom).hom.app K.carrier.X =
      (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map α.hom.hom.f) ≫
        (globalSectionsLowerStarIso _ θ.hom).hom.app K.carrier.X ≫
        K.globalSectionsFrobeniusPow r := by
  rw [globalSectionsFrobenius_naturality_assoc, ← globalSectionsFrobenius_transport θ r hθ K,
    Iso.hom_inv_id_app_assoc]

end Transport

end ProEtaleWeilSheaf

end AlgebraicGeometry
