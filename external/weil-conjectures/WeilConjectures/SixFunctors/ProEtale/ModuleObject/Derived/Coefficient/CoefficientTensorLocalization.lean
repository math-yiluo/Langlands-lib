/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization

/-! # Localization tensor normalization

This isolates the localization normalization and elementary categorical pasting
lemmas used by the scalar tensor representative argument.
(blueprint: lem-sfb-coefficient-tensor-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

/-- Paste the scalar, tensor, totalization and localization faces of the diagram. -/
private theorem cancel_iso_path {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞}
    (e : A ≅ B) {k : A ⟶ B} (hk : e.hom = k) {f g : B ⟶ C}
    (h : k ≫ f = k ≫ g) : f = g := by
  apply (cancel_epi e.hom).1
  simpa only [hk] using h

private theorem paste_representative_right {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G U U₀ V W X Y Z : 𝒞}
    {a : A ⟶ B}
    {b : B ⟶ C}
    {c : C ⟶ D}
    {d : D ⟶ E}
    {e : E ⟶ F}
    {f : F ⟶ G}
    {u : A ⟶ U}
    {τ : U ⟶ U₀}
    {aa : U₀ ⟶ V}
    {y : V ⟶ X}
    {ab : X ⟶ Y}
    {ac : Y ⟶ G}
    {ad : U₀ ⟶ W}
    {ae : W ⟶ Z}
    {af : C ⟶ W}
    {ag : D ⟶ Z}
    {ah : Z ⟶ Y}
    (hleft : a ≫ b ≫ c ≫ d ≫ e ≫ f = u ≫ τ ≫ aa ≫ y ≫ ab ≫ ac)
    (hpair : aa ≫ y ≫ ab = ad ≫ ae ≫ ah)
    (hderived : u ≫ τ ≫ ad = a ≫ b ≫ af)
    (htnat : c ≫ ag = af ≫ ae) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = a ≫ b ≫ c ≫ ag ≫ ah ≫ ac := by
  rw [hleft, reassoc_of% hpair, reassoc_of% hderived, ← reassoc_of% htnat]

private theorem map_pair_three {A B C : Type*} [Category A] [Category B] [Category C]
    (G : A × B ⥤ C) {x₀ x₁ x₂ x₃ y₁ y₂ : A}
    {z₀ z₁ z₂ z₃ w₁ w₂ : B}
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃}
    {d : x₀ ⟶ y₁} {e : y₁ ⟶ y₂} {f : y₂ ⟶ x₃}
    {a' : z₀ ⟶ z₁} {b' : z₁ ⟶ z₂} {c' : z₂ ⟶ z₃}
    {d' : z₀ ⟶ w₁} {e' : w₁ ⟶ w₂} {f' : w₂ ⟶ z₃}
    (h₁ : a ≫ b ≫ c = d ≫ e ≫ f) (h₂ : a' ≫ b' ≫ c' = d' ≫ e' ≫ f') :
    G.map (Prod.mkHom a a') ≫ G.map (Prod.mkHom b b') ≫ G.map (Prod.mkHom c c') =
      G.map (Prod.mkHom d d') ≫ G.map (Prod.mkHom e e') ≫ G.map (Prod.mkHom f f') := by
  simp only [← G.map_comp, prod_comp]
  exact congrArg G.map (congrArg₂ Prod.mkHom h₁ h₂)

private theorem total_tensor_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {P P' Q Q' : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (ModuleRingedComparison.totalTensor Λ Z).map (Prod.mkHom f g) = f ⊗ₘ g := by
  change (f ▷ _) ≫ (_ ◁ g) = f ⊗ₘ g
  exact (tensorHom_def f g).symm

private theorem cancel_tensor_factor
    {A B C : Type*} [Category A] [Category B] [Category C] (F : A × B ⥤ C)
    {x x' : A} {y y' : B} {v w : C} (e : x ≅ x') (f : y ≅ y')
    (t : v ≅ F.obj (x, y)) (g : v ⟶ w) (q : F.obj (x', y') ⟶ w)
    (h : q = F.map (Prod.mkHom e.inv f.inv) ≫ t.inv ≫ g) :
    t.hom ≫ F.map (Prod.mkHom e.hom f.hom) ≫ q = g := by
  rw [h]
  simp only [← F.map_comp_assoc, prod_comp, Iso.hom_inv_id,
    ← prod_id, F.map_id, Category.id_comp, Iso.hom_inv_id_assoc]

/-- Normalize the section localization tensor map on reconstructed complexes.
Source: Stacks Project, Cohomology on Sites, Tags 06YU and 07A4.
The defining formula for qTensor is conjugation of the localized total comparison
by the two localization isomorphisms and the derived tensor comparison. Compose
with their forward maps and cancel inverse pairs. Finally replace the section
cochain tensor comparison by totalComparison, using their proved equality.
(blueprint: lem-sfb-coefficient-tensor-localization). -/
theorem coefficientTensor_localization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) (P Q : CochainComplex (ModuleRingedComparison.internalModules Λ Z) ℤ) :
    let ER := (ModuleRingedComparison.equivalence Λ Z).functor
    let ED := (ModuleRingedComparison.derivedEquivalence Λ Z).functor
    let ERc := ER.mapHomologicalComplex (.up ℤ)
    let ℓ : DerivedCategory.Q ⋙ ED ≅ ERc ⋙ DerivedCategory.Q :=
      ER.mapDerivedCategoryFactors
    let μ : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q ⟶
        DerivedCategory.Q.obj (P ⊗ Q) :=
      (ModuleRingedComparison.internalLocalizationTensorMap Λ Z).app (P, Q)
    let q : (ModuleRingedComparison.tensor Λ Z).obj
        (DerivedCategory.Q.obj (ERc.obj P), DerivedCategory.Q.obj (ERc.obj Q)) ⟶
        DerivedCategory.Q.obj (ERc.obj P ⊗ ERc.obj Q) :=
      (ModuleRingedComparison.qTensor Λ Z).app (ERc.obj P, ERc.obj Q)
    let r : ERc.obj (P ⊗ Q) ≅ ERc.obj P ⊗ ERc.obj Q :=
      ModuleRingedComparison.totalComparison Λ Z P Q
    (ModuleRingedComparison.tensorComparison Λ Z).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (ModuleRingedComparison.tensor Λ Z).map (Prod.mkHom (ℓ.hom.app P) (ℓ.hom.app Q)) ≫ q =
    ED.map μ ≫ ℓ.hom.app (P ⊗ Q) ≫ DerivedCategory.Q.map r.hom := by
  dsimp only
  trans (ModuleRingedComparison.derivedEquivalence Λ Z).functor.map
      ((ModuleRingedComparison.internalLocalizationTensorMap Λ Z).app (P, Q)) ≫
    ModuleRingedComparison.localizedTotalComparison Λ Z P Q
  · exact cancel_tensor_factor (ModuleRingedComparison.tensor Λ Z)
      (ModuleRingedComparison.sectionLocalizationComparison Λ Z P)
      (ModuleRingedComparison.sectionLocalizationComparison Λ Z Q)
      ((ModuleRingedComparison.tensorComparison Λ Z).app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) _ _
      ((ModuleRingedComparison.qTensor_spec Λ Z).1 P Q)
  · exact congrArg (fun k ↦
      (ModuleRingedComparison.derivedEquivalence Λ Z).functor.map
          ((ModuleRingedComparison.internalLocalizationTensorMap Λ Z).app (P, Q)) ≫
        (ModuleRingedComparison.sectionLocalizationComparison Λ Z (P ⊗ Q)).hom ≫
        DerivedCategory.Q.map k)
      (ModuleRingedComparison.sectionTotalComparison_eq Λ Z P Q)

private theorem tensor_comparison_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {A A' B B' : DerivedCategory (ModuleRingedComparison.internalModules Λ Z)}
    (f : A ⟶ A') (g : B ⟶ B') :
    (ModuleRingedComparison.derivedEquivalence Λ Z).functor.map (f ⊗ₘ g) ≫
        (ModuleRingedComparison.tensorComparison Λ Z).hom.app (A', B') =
      (ModuleRingedComparison.tensorComparison Λ Z).hom.app (A, B) ≫
        (ModuleRingedComparison.tensor Λ Z).map (Prod.mkHom
          ((ModuleRingedComparison.derivedEquivalence Λ Z).functor.map f)
          ((ModuleRingedComparison.derivedEquivalence Λ Z).functor.map g)) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    derivedTensor, curriedTensor_obj_map, curriedTensor_map_app,
    ← MonoidalCategory.tensorHom_def] using
    (ModuleRingedComparison.tensorComparison Λ Z).hom.naturality (Prod.mkHom f g)

private theorem localization_tensor_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {P P' Q Q' : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    let q (K L : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ) :
        (ModuleRingedComparison.tensor Λ Z).obj (DerivedCategory.Q.obj K,
          DerivedCategory.Q.obj L) ⟶ DerivedCategory.Q.obj (K ⊗ L) :=
      (ModuleRingedComparison.qTensor Λ Z).app (K, L)
    (ModuleRingedComparison.tensor Λ Z).map
        (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫ q P' Q' =
      q P Q ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  dsimp only
  have hn := (ModuleRingedComparison.qTensor Λ Z).naturality (Prod.mkHom f g)
  simp only [Functor.comp_map, Functor.prod_map] at hn
  rw [total_tensor_map] at hn
  exact hn

end AlgebraicGeometry.ProEtale.CondensedRing
