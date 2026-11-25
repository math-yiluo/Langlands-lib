/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedCoefficientModel
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed

/-! # Exact scalar extension for coefficients in the scheme universe

All comparisons below are induced by the same isometric field presentation.
The source category consists of ordinary bounded constructible complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NormalizedScalar

variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E] [NormedAlgebra ℚ_[l] E]

/-- The integral coefficient comparison pulled back to the actual scheme.
Source: pullback of the normalized coefficient presentation.
(blueprint: lem-weil-pbc-normalized-coefficient-exact). -/
def FieldModel.integerIso (m : FieldModel l E) (T : Scheme.{u}) :
    condensedRingObj (integralCoeff l m.carrier) T ≅
      condensedRingObj (Profinite.continuousCoefficientRingObj (integers l E)) T :=
  (upperStarFromPoint T).mapIso
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso m.pointIntegerIso)

/-- The field coefficient comparison pulled back to the actual scheme.
Source: pullback of the normalized coefficient presentation.
(blueprint: lem-weil-pbc-normalized-coefficient-exact). -/
def FieldModel.fieldIso (m : FieldModel l E) (T : Scheme.{u}) :
    condensedRingObj (Profinite.continuousMapRingObj m.carrier) T ≅
      condensedRingObj (Profinite.continuousCoefficientRingObj E) T :=
  (upperStarFromPoint T).mapIso
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso m.pointFieldIso)

instance (m : FieldModel l E) (T : Scheme.{u}) : IsMonHom (m.integerIso T).hom := by
  dsimp only [FieldModel.integerIso, CategoryTheory.Functor.mapIso_hom]
  exact CategoryTheory.Functor.map.instIsMonHom (F := upperStarFromPoint T) _ _
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map m.pointIntegerIso.hom)

instance (m : FieldModel l E) (T : Scheme.{u}) : IsMonHom (m.fieldIso T).hom := by
  dsimp only [FieldModel.fieldIso, CategoryTheory.Functor.mapIso_hom]
  exact CategoryTheory.Functor.map.instIsMonHom (F := upperStarFromPoint T) _ _
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map m.pointFieldIso.hom)

/-- The scalar square remains the specified coefficient square after pullback.
Source: functoriality of inverse image.
(blueprint: lem-weil-pbc-normalized-coefficient-exact).
Proof: apply inverse image to the pointwise square of the presentation. -/
theorem FieldModel.scalar_square_scheme (m : FieldModel l E) (T : Scheme.{u}) :
    (m.integerIso T).hom ≫ coefficientMap (scalarMap (l := l) (E := E)) T =
      coefficientMap (integralScalarMap l m.carrier) T ≫ (m.fieldIso T).hom := by
  change (upperStarFromPoint T).map _ ≫ (upperStarFromPoint T).map _ =
    (upperStarFromPoint T).map _ ≫ (upperStarFromPoint T).map _
  simp only [CategoryTheory.Functor.mapIso_hom]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, m.scalar_square]

private theorem exact_iso {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a] :
    PreservesFiniteLimits (Mod.extendScalars a) :=
  preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv a).symm

/-- Exactness of the actual extension from the unit ball to the given field.
Source: Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-normalized-coefficient-exact).

Proof: the isometric small presentation gives an invertible coefficient square.
Factor the large-field scalar map through the inverse integral comparison, the
small scalar map, and the field comparison. Extension along the two isomorphisms
is exact restriction along their inverses. The middle extension is the proved
continuous integral scalar extension. Composition therefore gives exactness. -/
theorem scalar_exact [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (scalarMap (l := l) (E := E)) T)) := by
  obtain ⟨m⟩ := fieldModel_nonempty l E
  let a := m.integerIso T
  let b := m.fieldIso T
  let φ := coefficientMap (integralScalarMap l m.carrier) T
  let ψ := coefficientMap (scalarMap (l := l) (E := E)) T
  have ha : IsMonHom a.hom := inferInstance
  have hai : IsMonHom a.inv := inferInstance
  have hb : IsMonHom b.hom := inferInstance
  have hw : a.inv ≫ φ ≫ b.hom = ψ := by
    rw [← m.scalar_square_scheme T, Iso.inv_hom_id_assoc]
  have : PreservesFiniteLimits (Mod.extendScalars a.inv) := exact_iso a.inv
  have : PreservesFiniteLimits (Mod.extendScalars b.hom) := exact_iso b.hom
  have : PreservesFiniteLimits (Mod.extendScalars φ) :=
    integralScalarExtension_exact l m.carrier T
  let e : Mod.extendScalars ψ ≅
      (Mod.extendScalars a.inv ⋙ Mod.extendScalars φ) ⋙ Mod.extendScalars b.hom :=
    Mod.extendScalarsIsoOfEq (by simpa only [Category.assoc] using hw.symm) ≪≫
      Mod.extendScalarsComp (a.inv ≫ φ) b.hom ≪≫
        CategoryTheory.Functor.isoWhiskerRight (Mod.extendScalarsComp a.inv φ) _
  exact preservesFiniteLimits_of_natIso e.symm

private theorem bounded_comap {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) S))
    (hK : boundedConstructible S K) :
    boundedConstructible R ((Mod.comap a).mapDerivedCategory.obj K) := by
  refine ⟨(Mod.comap a).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact constructible_of_iso
    (((Mod.comap a).mapDerivedCategoryHomologyFunctorIso n).app K)
    (constructible_comap a (hK.2 n))

private theorem bounded_comap_iff {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) S)) :
    boundedConstructible R ((Mod.comap a).mapDerivedCategory.obj K) ↔
      boundedConstructible S K := by
  refine ⟨fun h ↦ ?_, bounded_comap a K⟩
  let i : 𝟭 (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) S) ≅
      Mod.comap a ⋙ Mod.comap (asIso a).inv :=
    (Mod.comapId S).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapComp (asIso a).inv a
  let e := (CategoryTheory.Functor.mapDerivedCategoryIdIso _).symm ≪≫
    CategoryTheory.Functor.mapDerivedCategoryNatIso i ≪≫
      (CategoryTheory.Functor.mapDerivedCategoryCompIso _ _).symm
  have hK := bounded_comap (asIso a).inv _ h
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso (e.app K).symm hK.1,
    fun n ↦ constructible_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso (e.app K).symm) (hK.2 n)⟩

/-- Ordinary bounded constructible integral complexes form a triangulated subcategory
for a finite normed extension in the scheme universe.
Source: the integral constructible Serre theorem and coefficient transport.
(blueprint: lem-weil-pbc-normalized-coefficient-exact).

Proof: exact restriction along the integral coefficient isomorphism preserves
boundedness and identifies constructibility in both directions. Thus the property
is the inverse image of the small coefficient's triangulated property under a
triangulated functor. Inverse images of triangulated properties are triangulated. -/
theorem integral_triangulated [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    [TopologicalSpace.NoetherianSpace T] :
    ObjectProperty.IsTriangulated (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj (integers l E)) T)) := by
  obtain ⟨m⟩ := fieldModel_nonempty l E
  obtain ⟨hk, hc, he⟩ := integralConstructible_serre l m.carrier T
  have : (boundedConstructible (condensedRingObj (integralCoeff l m.carrier) T)).IsTriangulated :=
    isTriangulated_boundedConstructible_of_serre _
      (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
        ObjectProperty.prop_cokernel _ f hM hN⟩)
      (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)
  have h : boundedConstructible
        (condensedRingObj (Profinite.continuousCoefficientRingObj (integers l E)) T) =
      (boundedConstructible (condensedRingObj (integralCoeff l m.carrier) T)).inverseImage
        (Mod.comap (m.integerIso T).hom).mapDerivedCategory := by
    funext K
    exact propext (bounded_comap_iff (m.integerIso T).hom K).symm
  rw [h]
  infer_instance

end WeilConjectures.NormalizedScalar
