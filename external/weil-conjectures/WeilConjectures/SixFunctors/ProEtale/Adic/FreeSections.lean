/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.Adic.SectionAction
public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialDescent

/-!
# Trivialising an `ℓ`-adic sheaf by global sections

Global sections `s₁, …, sᵣ` of a sheaf `F` of `ℚ̄_ℓ,X`-modules define the morphism
`ℚ̄_ℓ,Xʳ ⟶ F`, `(aᵢ) ↦ ∑ aᵢ • sᵢ` (`AlgebraicGeometry.ProEtale.AdicSheaf.ofSections`). It is an
isomorphism as soon as, for every object `U` of `X_proét`, every section of `F` over `U` is
uniquely of the form `∑ aᵢ • sᵢ|_U` with `aᵢ ∈ ℚ̄_ℓ,X(U)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.isIso_ofSections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} (F : AdicSheaf l X) {r : ℕ}
  (s : Fin r → F.X.obj.obj (op (proEtTop X)))

/-- The morphism `ℚ̄_ℓ,Xʳ ⟶ F`, `(aᵢ) ↦ ∑ aᵢ • sᵢ`, attached to global sections `s₁, …, sᵣ`. -/
noncomputable def ofSections : (⨁ fun _ : Fin r ↦ unit l X) ⟶ F :=
  biproduct.desc fun i ↦ sectionHom F (s i)

/-- The map `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U` on sections over `U`. -/
noncomputable def sectionsLinearMap (U : X.ProEtᵒᵖ) :
    (Fin r → (adicConstantSheaf l X).obj.obj U) →ₗ[ULift.{u + 1} (PadicAlgCl l)]
      F.X.obj.obj U where
  toFun a := ∑ i, sectionAct F (a i) (restrictTop F (s i) U)
  map_add' a b := by
    simp only [Pi.add_apply, add_sectionAct, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_sectionAct, Finset.smul_sum, RingHom.id_apply]

lemma sectionsLinearMap_apply (U : X.ProEtᵒᵖ) (a : Fin r → (adicConstantSheaf l X).obj.obj U) :
    sectionsLinearMap F s U a = ∑ i, sectionAct F (a i) (restrictTop F (s i) U) :=
  rfl

/-- On sections over `U`, `ofSections` is `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U`. -/
lemma sectionsFunctor_map_ofSections (U : X.ProEtᵒᵖ) :
    (sectionsFunctor U.unop).map (ofSections F s) =
      ((sectionsFunctor U.unop).mapBiproduct _).hom ≫ (ModuleCat.biproductIsoPi _).hom ≫
        ModuleCat.ofHom (sectionsLinearMap F s U) := by
  rw [ofSections, ← biproduct.mapBiproduct_hom_desc]
  congr 1
  rw [← Iso.inv_comp_eq, biproduct.desc_eq, Preadditive.comp_sum]
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  simp only [← Category.assoc, ModuleCat.biproductIsoPi_inv_comp_π, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
]
  rfl

/-- **Trivialising an `ℓ`-adic sheaf by global sections**: if every section of `F` over every
`U` is uniquely of the form `∑ aᵢ • sᵢ|_U`, then `(aᵢ) ↦ ∑ aᵢ • sᵢ` is an isomorphism
`ℚ̄_ℓ,Xʳ ≅ F`. -/
lemma isIso_ofSections (h : ∀ U, Function.Bijective (sectionsLinearMap F s U)) :
    IsIso (ofSections F s) := by
  have hU (U : X.ProEtᵒᵖ) : IsIso ((ofSections F s).hom.hom.app U) := by
    change IsIso ((sectionsFunctor U.unop).map (ofSections F s))
    rw [sectionsFunctor_map_ofSections]
    have : IsIso (ModuleCat.ofHom (sectionsLinearMap F s U)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (h U)
    infer_instance
  have : ∀ U, IsIso (((sheafToPresheaf _ _).map (ofSections F s).hom).app U) := hU
  have : IsIso ((sheafToPresheaf _ _).map (ofSections F s).hom) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso ((Mod.forget _).map (ofSections F s)) :=
    isIso_of_reflects_iso (ofSections F s).hom (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso _ (Mod.forget _)

lemma ofSections_hom_app (U : X.ProEtᵒᵖ) (x) :
    (ofSections F s).hom.hom.app U x = sectionsLinearMap F s U
      ((ModuleCat.biproductIsoPi _).hom (((sectionsFunctor U.unop).mapBiproduct _).hom x)) := by
  change ((sectionsFunctor U.unop).map (ofSections F s)) x = _
  rw [sectionsFunctor_map_ofSections]
  rfl

/-- **Trivialising an `ℓ`-adic sheaf by global sections**, local form: if `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U`
is injective for every `U`, and every section of `F` is locally of this form, then
`(aᵢ) ↦ ∑ aᵢ • sᵢ` is an isomorphism `ℚ̄_ℓ,Xʳ ≅ F`. -/
lemma isIso_ofSections_of_injective (hinj : ∀ U, Function.Injective (sectionsLinearMap F s U))
    (hsurj : ∀ (U : X.ProEt) (x : F.X.obj.obj (op U)), ∃ S ∈ Scheme.ProEt.topology X U,
      ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), S f →
        ∃ a, sectionsLinearMap F s (op V) a = F.X.obj.map f.op x) :
    IsIso (ofSections F s) := by
  let e (U : X.ProEtᵒᵖ) := ((sectionsFunctor U.unop).mapBiproduct
    (fun _ : Fin r ↦ unit l X)) ≪≫ ModuleCat.biproductIsoPi _
  have hmono : Mono (ofSections F s).hom := Sheaf.mono_of_injective _ fun U x y hxy ↦ by
    rw [ofSections_hom_app, ofSections_hom_app] at hxy
    exact ((ConcreteCategory.bijective_of_isIso (e U).hom).1 (hinj U hxy))
  have : Sheaf.IsLocallySurjective (ofSections F s).hom := ⟨fun {U} x ↦ by
    obtain ⟨S, hS, h⟩ := hsurj U x
    refine (Scheme.ProEt.topology X).superset_covering (fun V f hf ↦ ?_) hS
    obtain ⟨a, ha⟩ := h f hf
    refine ⟨(e (op V)).inv a, ?_⟩
    rw [ofSections_hom_app]
    change sectionsLinearMap F s (op V) ((e (op V)).hom ((e (op V)).inv a)) = _
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply, ha]⟩
  have : IsIso ((Mod.forget _).map (ofSections F s)) :=
    isIso_of_mono_of_epi (ofSections F s).hom
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- The maps `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U` are compatible with restriction. -/
lemma map_sectionsLinearMap {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : Fin r → (adicConstantSheaf l X).obj.obj U) :
    F.X.obj.map f (sectionsLinearMap F s U a) =
      sectionsLinearMap F s V (fun i ↦ (adicConstantSheaf l X).obj.map f (a i)) := by
  simp only [sectionsLinearMap_apply, map_sum, map_sectionAct, map_restrictTop]

end AlgebraicGeometry.ProEtale.AdicSheaf
