/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.SectionAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteExtend

/-!
# Pushforward commutes with `F ⊗_E -` for finite subextensions `E ≤ F`

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ̄_ℓ / ℚ_ℓ` and `f : X ⟶ Y` a morphism of
schemes. Choosing a basis `b₁, …, bₙ` of `F` over `E`, the coefficient ring `F_X` is a finite
free `E_X`-module
(`AlgebraicGeometry.ProEtale.isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`),
so that `F_X ⊗_{E_X} M ≅ Mⁿ` for every `E_X`-module `M`, via `(mᵢ) ↦ ∑ bᵢ • (1 ⊗ mᵢ)`
(`CategoryTheory.Mod.isIso_biproductDesc_extendUnitHom_globalSmul`). Hence:

* the underived comparison **(Push)** `F_Y ⊗ f_* M ⟶ f_*(F_X ⊗ M)` is an isomorphism for every
  `E_X`-module `M` (`ProEtale.CondensedRing.isIso_pushHom_padicSubfieldRingObjMap_app`): it is
  compatible with the units of extension of scalars and with the actions of the constant global
  sections `bᵢ`, so it is identified with the canonical isomorphism `(f_* M)ⁿ ≅ f_*(Mⁿ)`;
* the underlying abelian sheaf of `F_X ⊗_{E_X} I` is injective, hence `f_*`-acyclic, for an
  injective `E_X`-module `I`
  (`ProEtale.CondensedRing.rightAcyclic_lowerStar_extendScalars_padicSubfieldRingObjMap`).

Consequently the derived (Push) for `E ⟶ ℚ̄_ℓ` is an isomorphism on bounded below objects for
quasi-compact quasi-separated `f`
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicAlgCl_of_isGE'`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

private lemma biproduct_desc_comp_eq {C : Type*} [Category* C] [HasZeroMorphisms C]
    {J : Type*} {A : J → C} [HasBiproduct A] {B D : C}
    (g : ∀ i, A i ⟶ B) (f : B ⟶ D) :
    biproduct.desc g ≫ f = biproduct.desc (fun i ↦ g i ≫ f) := by
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct.ι_desc_assoc, biproduct.ι_desc]

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] {A : C} [MonObj A]

/-- The action of a global section commutes with morphisms of module objects. -/
@[reassoc]
lemma globalSmul_comp_hom {M N : Mod C A} (g : M ⟶ N) (σ : 𝟙_ C ⟶ A) :
    globalSmul σ M ≫ g.hom = g.hom ≫ globalSmul σ N :=
  sectionAct_comp g.hom σ

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ} (hF : E ≤ F)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The constant global section `t` of `F_Z`, the image under `p_Z^*` of the constant global
section `t` of `F̲`. -/
noncomputable abbrev padicSubfieldConstSection (Z : Scheme.{u}) (t : F) :
    𝟙_ (Sheaf (ProEt.topology Z) Ab.{u + 1}) ⟶ padicSubfieldRingObj Z ℓ F :=
  ε (upperStarFromPoint Z) ≫
    (upperStarFromPoint Z).map (Profinite.continuousMapConstRingHom F t).hom

/-- **(Push) for `E ⟶ F` is an isomorphism**: for finite subextensions `E ≤ F` and every
`E_X`-module `M`, the comparison `F_Y ⊗_{E_Y} f_* M ⟶ f_*(F_X ⊗_{E_X} M)` is an isomorphism. -/
theorem isIso_pushHom_padicSubfieldRingObjMap_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    IsIso ((pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f).app M) := by
  obtain ⟨n, b, h⟩ :=
    Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul.{u} ℓ hF
  let push :
      (Mod.extendScalars (padicSubfieldRingObjMap Y ℓ hF)).obj
          ((f)_*⟦Profinite.continuousMapRingObj E⟧.obj M) ⟶
        (f)_*⟦Profinite.continuousMapRingObj F⟧.obj
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M) :=
    (pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f).app M
  let DX : ⨁ (fun _ : Fin n ↦ M.X) ⟶
      ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M).X :=
    biproduct.desc fun i ↦ Mod.extendUnitHom (padicSubfieldRingObjMap X ℓ hF) M ≫
      Mod.globalSmul (padicSubfieldConstSection ℓ X (b i))
        ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M)
  let DY : ⨁ (fun _ : Fin n ↦ ((f)_*⟦_⟧.obj M).X) ⟶
      ((Mod.extendScalars (padicSubfieldRingObjMap Y ℓ hF)).obj ((f)_*⟦_⟧.obj M)).X :=
    biproduct.desc fun i ↦ Mod.extendUnitHom (padicSubfieldRingObjMap Y ℓ hF) ((f)_*⟦_⟧.obj M) ≫
      Mod.globalSmul (padicSubfieldConstSection ℓ Y (b i))
        ((Mod.extendScalars (padicSubfieldRingObjMap Y ℓ hF)).obj ((f)_*⟦_⟧.obj M))
  have hX : IsIso DX := Mod.isIso_biproductDesc_extendUnitHom_globalSmul
    (padicSubfieldRingObjMap X ℓ hF) (fun i ↦ padicSubfieldConstSection ℓ X (b i))
      (isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul X ℓ hF b h) M
  have hY : IsIso DY := Mod.isIso_biproductDesc_extendUnitHom_globalSmul
    (padicSubfieldRingObjMap Y ℓ hF) (fun i ↦ padicSubfieldConstSection ℓ Y (b i))
      (isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul Y ℓ hF b h) ((f)_*⟦_⟧.obj M)
  have key : DY ≫ push.hom =
      ((f)_*[Ab.{u + 1}].mapBiproduct (fun _ : Fin n ↦ M.X)).inv ≫ (f)_*[Ab.{u + 1}].map DX := by
    refine (biproduct_desc_comp_eq _ _).trans ?_
    refine Eq.trans ?_ (biproduct.mapBiproduct_inv_map_desc ((f)_*[Ab.{u + 1}])
      (fun _ : Fin n ↦ M.X) (fun i ↦
        Mod.extendUnitHom (padicSubfieldRingObjMap X ℓ hF) M ≫
          Mod.globalSmul (padicSubfieldConstSection ℓ X (b i))
            ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M))).symm
    apply congrArg biproduct.desc
    funext i
    rw [Category.assoc, Mod.globalSmul_comp_hom push,
      extendUnitHom_comp_pushHom_app_hom_assoc f (Profinite.padicSubfieldRingObjMap ℓ hF) M]
    have e₃ : Mod.globalSmul (padicSubfieldConstSection ℓ Y (b i))
        ((f)_*⟦_⟧.obj ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M)) =
        (f)_*[Ab.{u + 1}].map (Mod.globalSmul (padicSubfieldConstSection ℓ X (b i))
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj M)) :=
      globalSmul_lowerStar_obj f F (b i) _
    exact (congrArg ((f)_*[Ab.{u + 1}].map
      (Mod.extendUnitHom (padicSubfieldRingObjMap X ℓ hF) M) ≫ ·) e₃).trans
        ((f)_*[Ab.{u + 1}].map_comp _ _).symm
  have : IsIso push.hom := by
    have : IsIso (DY ≫ push.hom) := by
      rw [key]
      exact IsIso.comp_isIso' inferInstance (Functor.map_isIso _ _)
    exact IsIso.of_isIso_comp_left DY _
  have : IsIso ((Mod.forget _).map push) := this
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- For an injective `E_X`-module `I`, the underlying abelian sheaf of `F_X ⊗_{E_X} I` is
injective, being isomorphic to `I.Xⁿ` for `n = [F : E]`. -/
lemma injective_extendScalars_padicSubfieldRingObjMap_obj_X
    (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) [Injective I] :
    Injective ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj I).X := by
  obtain ⟨n, b, h⟩ :=
    Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul.{u} ℓ hF
  have hI := Mod.isIso_biproductDesc_extendUnitHom_globalSmul (padicSubfieldRingObjMap X ℓ hF)
    (fun i ↦ padicSubfieldConstSection ℓ X (b i))
      (isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul X ℓ hF b h) I
  have : Injective I.X := (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (padicSubfieldRingObj X ℓ E)).injective_obj_of_injective (inferInstance : Injective I)
  exact Injective.of_iso (@asIso _ _ _ _ _ hI) inferInstance

/-- For an injective `E_X`-module `I`, the underlying abelian sheaf of `F_X ⊗_{E_X} I` is
`f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_extendScalars_padicSubfieldRingObjMap
    (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) [Injective I] :
    ((f)_*[Ab.{u + 1}]).rightAcyclic
      ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj I).X :=
  have := injective_extendScalars_padicSubfieldRingObjMap_obj_X ℓ hF I
  Functor.rightAcyclic_of_injective _

variable (E) [QuasiCompact f] [QuasiSeparated f]

/-- **(Push) for `E ⟶ ℚ̄_ℓ` on bounded below objects**: for a quasi-compact quasi-separated `f`,
the comparison `ℚ̄_ℓ,Y ⊗ᴸ Rf_* K ⟶ Rf_*(ℚ̄_ℓ,X ⊗ᴸ K)` is an isomorphism for every bounded below
`K ∈ D(E_X)`. -/
theorem isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K) :=
  isIso_derivedPushHom_app_padicAlgCl_of_isGE ℓ E f
    (fun _ hF I _ ↦ isIso_pushHom_padicSubfieldRingObjMap_app ℓ hF f I)
    (fun _ hF I hI ↦
      have := hI
      rightAcyclic_lowerStar_extendScalars_padicSubfieldRingObjMap ℓ hF f I)
    K n

end AlgebraicGeometry.ProEtale.CondensedRing
