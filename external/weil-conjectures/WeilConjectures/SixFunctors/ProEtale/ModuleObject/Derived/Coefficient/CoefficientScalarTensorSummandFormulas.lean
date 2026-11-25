/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses

/-! # Formulas for signed tensor summands

Naturality of termwise comparison maps is checked with abstract additive functors.
The proved private formulas expose the scalar and total comparison summands.
(blueprint: lem-sfb-coefficient-scalar-tensor-summand-naturality)
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
  internalScalarExtension
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  Localization.Monoidal.tensorBifunctor
  ModuleRingedComparison.ordinaryTensorComparison coefficientSectionScalarPure
  Mod.extendRestrictAdjunction

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

private theorem scalar_total_summand (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    let := d.m
    let := d.b.ordinaryAdjunction.isLeftAdjoint
    d.b.extension.map (HomologicalComplex.ιTensorObj P Q p q n hpq) ≫
        (coefficientSectionScalarTotal a Z d.b d.m P Q).f n =
      Functor.OplaxMonoidal.δ d.b.extension (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((d.b.extension.mapHomologicalComplex (.up ℤ)).obj P)
          ((d.b.extension.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq := by
  let := d.m
  let := d.b.ordinaryAdjunction.isLeftAdjoint
  dsimp only [coefficientSectionScalarTotal]
  simp only [eqToHom_refl, HomologicalComplex.comp_f, Category.comp_id]
  erw [(d.b.extension.mapHomologicalComplex (.up ℤ)).map_id]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans d.b.extension) (.up ℤ) P Q p q n hpq

/-- Naturality of a termwise comparison on a tensor summand.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, termwise total tensor maps.
The graded tensor inclusion followed by the tensor of two graded maps equals
that inclusion after the tensor of their two degree components. Apply
GradedObject.Monoidal.ι_tensorHom. The termwise comparison components are exactly
the components of the original functor comparison, giving the formula.
(blueprint: lem-sfb-coefficient-scalar-tensor-summand-naturality). -/
theorem coefficientScalarTensor_summandNaturality (Z : Scheme.{u})
    (F₁ : ModuleRingedComparison.internalModules R Z ⥤
      ModuleRingedComparison.internalModules S Z)
    (F₂ : ModuleRingedComparison.internalModules S Z ⥤ ModuleRingedComparison.modules S Z)
    (G₁ : ModuleRingedComparison.internalModules R Z ⥤ ModuleRingedComparison.modules R Z)
    (G₂ : ModuleRingedComparison.modules R Z ⥤ ModuleRingedComparison.modules S Z)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    let F₁c := F₁.mapHomologicalComplex (.up ℤ)
    let F₂c := F₂.mapHomologicalComplex (.up ℤ)
    let G₁c := G₁.mapHomologicalComplex (.up ℤ)
    let G₂c := G₂.mapHomologicalComplex (.up ℤ)
    let eC : F₁c ⋙ F₂c ≅ G₁c ⋙ G₂c := NatIso.mapHomologicalComplex e (.up ℤ)
    HomologicalComplex.ιTensorObj (F₂c.obj (F₁c.obj P)) (F₂c.obj (F₁c.obj Q)) p q n hpq ≫
      ((eC.hom.app P ⊗ₘ eC.hom.app Q).f n) =
    (e.hom.app (P.X p) ⊗ₘ e.hom.app (Q.X q)) ≫
      HomologicalComplex.ιTensorObj (G₂c.obj (G₁c.obj P)) (G₂c.obj (G₁c.obj Q))
        p q n hpq := by
  dsimp only
  change GradedObject.Monoidal.ιTensorObj _ _ p q n hpq ≫
    GradedObject.Monoidal.tensorHom _ _ n = _
  rw [GradedObject.Monoidal.ι_tensorHom]
  rfl

private theorem section_total_summand
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) (P Q : CochainComplex (ModuleRingedComparison.internalModules Λ Z) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    (ModuleRingedComparison.equivalence Λ Z).functor.map
        (HomologicalComplex.ιTensorObj P Q p q n hpq) ≫
      (ModuleRingedComparison.totalComparison Λ Z P Q).hom.f n =
    (ModuleRingedComparison.ordinaryTensorComparison Λ Z (P.X p) (Q.X q)).hom ≫
      HomologicalComplex.ιTensorObj
        (((ModuleRingedComparison.equivalence Λ Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P)
        (((ModuleRingedComparison.equivalence Λ Z).functor.mapHomologicalComplex
          (.up ℤ)).obj Q) p q n hpq := by
  exact (ModuleRingedComparison.totalComparison_existsUnique Λ Z P Q).exists.choose_spec
    p q n hpq

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
private theorem paste_summand_square
    (E : A ⥤ C) (E' : B ⥤ D) (F : A ⥤ B) (F' : C ⥤ D)
    (a : F ⋙ E' ≅ E ⋙ F') {x T : A} {b B₀ : B} {c C₀ : C} {d d' U V : D}
    (j : x ⟶ T) (i : F.obj T ⟶ B₀) (t : E.obj T ⟶ C₀)
    (t' : E'.obj B₀ ⟶ U) (s : F'.obj C₀ ⟶ V) (e : U ⟶ V)
    (di : F.obj x ⟶ b) (d₀ : E.obj x ⟶ c)
    (d₁ : E'.obj b ⟶ d) (ds : F'.obj c ⟶ d')
    (jF : b ⟶ B₀) (jE : c ⟶ C₀) (jEF : d ⟶ U) (jFE : d' ⟶ V) (v : d ⟶ d')
    (hi : F.map j ≫ i = di ≫ jF) (ht : E.map j ≫ t = d₀ ≫ jE)
    (ht' : E'.map jF ≫ t' = d₁ ≫ jEF) (hs : F'.map jE ≫ s = ds ≫ jFE)
    (he : jEF ≫ e = v ≫ jFE)
    (ho : E'.map di ≫ d₁ ≫ v = a.hom.app x ≫ F'.map d₀ ≫ ds) :
    E'.map (F.map j) ≫ E'.map i ≫ t' ≫ e =
      E'.map (F.map j) ≫ a.hom.app T ≫ F'.map t ≫ s := by
  rw [← E'.map_comp_assoc, hi, E'.map_comp, Category.assoc, reassoc_of% ht', he]
  rw [reassoc_of% (a.hom.naturality j)]
  change _ = a.hom.app x ≫ F'.map (E.map j) ≫ F'.map t ≫ s
  rw [← F'.map_comp_assoc, ht, F'.map_comp, Category.assoc, hs]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ jFE) ho

end

end AlgebraicGeometry.ProEtale.CondensedRing
