/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Point.PointSectionsFiniteness
public import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdQbarCategory
public import Mathlib.Algebra.Category.ModuleCat.Ulift

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexCohomologySplitting
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientComplexRationalization

/-!
# Finite-stage point fibres and their common-stage representative

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: def-weil-point-fibre-stage-constructions).

Evaluation is the recorded final-object sections functor. Integral coefficients act
through the constant-to-completion map. Rationalization tensors sections with the
fraction field. The small point target is connected to the section universe by the
fully faithful module universe lift, restricted to bounded finite-dimensional objects.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u r s v w z

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

attribute [-instance] coefficientComplexModuleDerived

attribute [local irreducible] limit

private theorem pointDerived_semilinear {R : Type v} {S : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S)
    (F : ModuleCat.{v} R ⥤ ModuleCat.{w} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ (M N : ModuleCat.{v} R) (a : R) (f : M ⟶ N),
      F.map (a • f) = φ a • F.map f)
    (X Y : DerivedCategory (ModuleCat.{v} R)) (a : R) (f : X ⟶ Y) :
    F.mapDerivedCategory.map (a • f) = φ a • F.mapDerivedCategory.map f := by
  let G := F.mapDerivedCategory
  have hQ (C : CochainComplex (ModuleCat.{v} R) ℤ) :
      G.map (a • 𝟙 (DerivedCategory.Q.obj C)) = φ a • 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_id DerivedCategory.Q, ← CategoryTheory.Functor.map_smul]
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app C)).mp
    change F.mapDerivedCategory.map (DerivedCategory.Q.map (a • 𝟙 C)) ≫ _ = _
    rw [F.mapDerivedCategoryFactors_hom_naturality]
    have hc : (F.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 C) =
        φ a • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj C) := by
      apply HomologicalComplex.Hom.ext
      funext i
      change F.map (a • 𝟙 (C.X i)) = φ a • 𝟙 (F.obj (C.X i))
      rw [hF, F.map_id]
    rw [hc, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    congr 1
    exact Category.comp_id _
  have hX : G.map (a • 𝟙 X) = φ a • 𝟙 _ := by
    let e := DerivedCategory.Q.objObjPreimageIso X
    have he : a • 𝟙 X = e.inv ≫ (a • 𝟙 _) ≫ e.hom := by simp
    rw [he, G.map_comp, G.map_comp, hQ]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    rw [← G.map_comp, e.inv_hom_id, G.map_id]
  calc
    G.map (a • f) = G.map ((a • 𝟙 X) ≫ f) := by rw [Linear.smul_comp, Category.id_comp]
    _ = G.map (a • 𝟙 X) ≫ G.map f := G.map_comp _ _
    _ = φ a • G.map f := by rw [hX, Linear.smul_comp, Category.id_comp]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointComplete_of_iso {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) {X Y : DerivedCategory (ModuleCat.{u + 1} R)} (e : X ≅ Y)
    (hX : DerivedCategory.IsDerivedComplete.{u + 1, u + 1, u + 1} I X) :
    DerivedCategory.IsDerivedComplete.{u + 1, u + 1, u + 1} I Y := by
  intro a ha _ T hT
  let : HasProduct (fun _ : ℕ ↦ X) :=
    hasProduct_of_equiv_of_iso (fun _ : ℕ ↦ Y) (fun _ : ℕ ↦ X)
      (Equiv.refl ℕ) (fun _ ↦ e)
  let E : (∏ᶜ fun _ : ℕ ↦ Y) ≅ (∏ᶜ fun _ : ℕ ↦ X) :=
    HasLimit.isoOfNatIso (Discrete.natIso
      (F := Discrete.functor (fun _ : ℕ ↦ Y))
      (G := Discrete.functor (fun _ : ℕ ↦ X)) (fun _ ↦ e.symm))
  obtain ⟨p, δ, ht⟩ := hT
  have hE : E.hom ≫ towerTransitionEndomorphism (fun _ : ℕ ↦ a • 𝟙 X) =
      towerTransitionEndomorphism (fun _ : ℕ ↦ a • 𝟙 Y) ≫ E.hom := by
    apply Pi.hom_ext
    intro n
    simp [E, towerTransitionEndomorphism, towerProductShift,
      HasLimit.isoOfNatIso_hom_π, Linear.comp_smul, Linear.smul_comp]
  apply hX a ha T
  refine ⟨p ≫ E.hom, E.inv ≫ δ, ?_⟩
  exact (CategoryTheory.Pretriangulated.distinguished_iff_of_iso
    (CategoryTheory.Pretriangulated.Triangle.isoMk
      (CategoryTheory.Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism (fun _ : ℕ ↦ a • 𝟙 Y)) δ)
      (CategoryTheory.Pretriangulated.Triangle.mk (p ≫ E.hom)
        (towerTransitionEndomorphism (fun _ : ℕ ↦ a • 𝟙 X)) (E.inv ≫ δ))
      (Iso.refl _) E E (by simp) hE.symm (by simp))).mp ht

private theorem pointFinite_of_iso {R : Type (u + 1)} [CommRing R]
    {X Y : DerivedCategory (ModuleCat.{u + 1} R)} (e : X ≅ Y)
    (hX : DerivedCategory.pointFiniteCohomology R X) :
    DerivedCategory.pointFiniteCohomology R Y := by
  obtain ⟨⟨s, hs⟩, hf⟩ := hX
  refine ⟨⟨s, fun i hi ↦ (hs i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_⟩
  intro i
  let := hf i
  exact Finite.of_equiv _ ((DerivedCategory.homologyFunctor _ i).mapIso e).toLinearEquiv.toEquiv

private theorem pointFg_of_iso {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    {X Y : DerivedCategory (ModuleCat.{u + 1} R)} (e : X ≅ Y)
    (hX : DerivedCategory.pointFgComplete R I X) : DerivedCategory.pointFgComplete R I Y := by
  obtain ⟨⟨s, hs⟩, hf, hc⟩ := hX
  refine ⟨⟨s, fun i hi ↦ (hs i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_, pointComplete_of_iso I e hc⟩
  intro i
  exact (Module.Finite.equiv_iff
    ((DerivedCategory.homologyFunctor _ i).mapIso e).toLinearEquiv).mp (hf i)

private theorem pointFd_of_iso {F : Type (u + 1)} [Field F]
    {X Y : DerivedCategory (ModuleCat.{u + 1} F)} (e : X ≅ Y)
    (hX : DerivedCategory.pointFiniteDimensional F X) :
    DerivedCategory.pointFiniteDimensional F Y := by
  obtain ⟨⟨s, hs⟩, hf⟩ := hX
  refine ⟨⟨s, fun i hi ↦ (hs i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_⟩
  intro i
  exact (Module.Finite.equiv_iff
    ((DerivedCategory.homologyFunctor _ i).mapIso e).toLinearEquiv).mp (hf i)

/-- The chosen geometric base field is algebraically closed.
Source: blueprint global finite-field datum, order 411
(blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreBaseIsAlgClosed : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The fully faithful change of coefficient and module size, with the same scalar action.
Source: blueprint order 1509, point targets
(blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable abbrev pointFibreModuleLift (F : Type u) [Field F] :
    ModuleCat.{u} F ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} F) :=
  ModuleCat.uliftFunctor.{u + 1, u} F ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom

/-- Exactness and additivity of the carrier lift with its coefficient transport.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: carrier lift preserves kernels and cokernels by the module equivalence on
underlying elements. Restriction along the coefficient ring equivalence preserves
all limits and colimits; both operations add morphisms pointwise. -/
theorem pointFibreModuleLift_exact (F : Type u) [Field F] :
    (pointFibreModuleLift F).Additive ∧
      PreservesFiniteLimits (pointFibreModuleLift F) ∧
      PreservesFiniteColimits (pointFibreModuleLift F) := by
  let h₁ : PreservesFiniteLimits (ModuleCat.uliftFunctor.{u + 1, u} F) := inferInstance
  let h₂ : PreservesFiniteColimits (ModuleCat.uliftFunctor.{u + 1, u} F) := inferInstance
  let h₃ : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u}
        (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom) := inferInstance
  let h₄ : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u}
        (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of the explicit universe lift.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreModuleLiftAdditive (F : Type u) [Field F] :
    (pointFibreModuleLift F).Additive := (pointFibreModuleLift_exact F).1

/-- Preservation of kernels by the explicit universe lift.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreModuleLiftLimits (F : Type u) [Field F] :
    PreservesFiniteLimits (pointFibreModuleLift F) := (pointFibreModuleLift_exact F).2.1

/-- Preservation of cokernels by the explicit universe lift.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreModuleLiftColimits (F : Type u) [Field F] :
    PreservesFiniteColimits (pointFibreModuleLift F) := (pointFibreModuleLift_exact F).2.2

/-- Universe lift preserves the bounded finite-dimensional predicate.
Source: blueprint order 1509, target categories
(blueprint: lemma-perfect-complexes-geometric-point).
Proof: exact universe lift commutes with homology. Its module equivalence identifies
cohomology spaces and preserves their dimensions and the same finite support. -/
theorem pointFibreModuleLift_mem (F : Type u) [Field F]
    (K : (DerivedCategory.pointFiniteDimensional F).FullSubcategory) :
    DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)
      ((pointFibreModuleLift F).mapDerivedCategory.obj K.obj) := by
  obtain ⟨⟨s, hs⟩, hfd⟩ := K.property
  let e (i : ℤ) := (pointFibreModuleLift F).mapDerivedCategoryHomologyFunctorIso i |>.app K.obj
  refine ⟨⟨s, ?_⟩, ?_⟩
  · intro i hi
    exact ((pointFibreModuleLift F).map_isZero (hs i hi)).of_iso (e i).symm
  · intro i
    let := hfd i
    let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).obj K.obj
    have hfin : FiniteDimensional (ULift.{u + 1, u} F)
        ((pointFibreModuleLift F).obj H) :=
      Module.Finite.of_surjective
        (show H →ₛₗ[(ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom]
            ((pointFibreModuleLift F).obj H) from
          { toFun := ULift.up
            map_add' := by intros; rfl
            map_smul' := by intros; rfl })
        (fun x ↦ ⟨x.down, rfl⟩)
    exact (Module.Finite.equiv_iff (e i).toLinearEquiv).mp hfin

/-- The actual universe lift on the point's bounded finite-dimensional target.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreSizeLift (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional F).FullSubcategory ⥤
      (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).FullSubcategory :=
  (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).lift
    ((DerivedCategory.pointFiniteDimensional F).ι ⋙ (pointFibreModuleLift F).mapDerivedCategory)
    (pointFibreModuleLift_mem F)

/-- The restricted universe lift is an equivalence, rather than an extra size assumption.
Source: blueprint order 1509, work in a universe containing the point categories
(blueprint: lemma-perfect-complexes-geometric-point).
Proof: over a field every complex is isomorphic in the derived category to its graded
cohomology with zero differential. Bounded finite-dimensional cohomology therefore has
a bounded representative of finite-dimensional spaces, all of which are small. This
proves essential surjectivity. Maps between these representatives are their graded
linear maps; the universe lift is fully faithful on those maps. -/
theorem pointFibreSizeLift_equivalence (F : Type u) [Field F] :
    (pointFibreSizeLift F).IsEquivalence := by
  classical
  let U := pointFibreModuleLift F
  let H (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} F) i
  let H' (i : ℤ) := DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} F)) i
  have bij := (DerivedCategory.field_complex_cohomology_splitting F).2.2.1
  have bij' := (DerivedCategory.field_complex_cohomology_splitting (ULift.{u + 1, u} F)).2.2.1
  have hn {X Y : DerivedCategory (ModuleCat.{u} F)} (f : X ⟶ Y) (i : ℤ) :
      (H' i).map (U.mapDerivedCategory.map f) =
        (U.mapDerivedCategoryHomologyFunctorIso i).inv.app X ≫
          U.map ((H i).map f) ≫ (U.mapDerivedCategoryHomologyFunctorIso i).hom.app Y := by
    have h := (U.mapDerivedCategoryHomologyFunctorIso i).hom.naturality f
    dsimp only [CategoryTheory.Functor.comp_map] at h
    simpa only [H, H', ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
      congrArg (fun z ↦ (U.mapDerivedCategoryHomologyFunctorIso i).inv.app X ≫ z) h.symm
  have faithful : (pointFibreSizeLift F).Faithful := by
    constructor
    intro X Y f g hfg
    apply ObjectProperty.hom_ext
    apply (bij X.obj Y.obj).injective
    funext i
    apply U.map_injective
    have hh := congrArg (fun t ↦ (H' i).map t.hom) hfg
    change (H' i).map (U.mapDerivedCategory.map f.hom) =
      (H' i).map (U.mapDerivedCategory.map g.hom) at hh
    simpa only [hn, cancel_epi, cancel_mono] using hh
  have full : (pointFibreSizeLift F).Full := by
    constructor
    intro X Y g
    let φ (i : ℤ) : (H i).obj X.obj ⟶ (H i).obj Y.obj :=
      U.preimage ((U.mapDerivedCategoryHomologyFunctorIso i).hom.app X.obj ≫
        (H' i).map g.hom ≫ (U.mapDerivedCategoryHomologyFunctorIso i).inv.app Y.obj)
    obtain ⟨f, hf⟩ := (bij X.obj Y.obj).surjective φ
    refine ⟨ObjectProperty.homMk f, ?_⟩
    apply ObjectProperty.hom_ext
    apply (bij' _ _).injective
    funext i
    change (H' i).map (U.mapDerivedCategory.map f) = _
    rw [hn, show (H i).map f = φ i from congrFun hf i]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simp only [φ, CategoryTheory.Functor.map_preimage, Category.assoc,
        Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
  have ess : (pointFibreSizeLift F).EssSurj := by
    constructor
    intro K
    obtain ⟨C, a, b, hd, hH, hge, hle, hfd, ⟨eK⟩⟩ :=
      ((DerivedCategory.field_complex_cohomology_splitting
        (ULift.{u + 1, u} F)).2.2.2.1 K.obj K.property).1
    let V (i : ℤ) := (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom).obj (C.X i)
    have hV (i : ℤ) : FiniteDimensional F (V i) := by
      let := hfd i
      exact Module.Finite.of_surjective
        (show C.X i →ₛₗ[(ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom] V i from
          { toFun := id
            map_add' := by intros; rfl
            map_smul' := by intros; rfl }) Function.surjective_id
    let smallV (i : ℤ) : Small.{u} (V i) :=
      let := hV i
      Module.Finite.small F (V i)
    let A (i : ℤ) : ModuleCat.{u} F := ModuleCat.of F (Shrink.{u} (V i))
    let M : CochainComplex (ModuleCat.{u} F) ℤ := { X := A, d := fun _ _ ↦ 0 }
    let f (i : ℤ) : U.obj (A i) →ₗ[ULift.{u + 1, u} F] C.X i :=
      { toFun := fun x ↦ Shrink.linearEquiv F (V i) x.down
        map_add' := by
          intro x y
          exact (Shrink.linearEquiv F (V i)).map_add x.down y.down
        map_smul' := by
          intro r x
          exact (Shrink.linearEquiv F (V i)).map_smul r.down x.down }
    let e (i : ℤ) : U.obj (A i) ≅ C.X i :=
      (LinearEquiv.ofBijective (f i)
        ((Shrink.linearEquiv F (V i)).bijective.comp ULift.down_bijective)).toModuleIso
    let eC : (U.mapHomologicalComplex (.up ℤ)).obj M ≅ C :=
      HomologicalComplex.Hom.isoOfComponents e (by
        intro i j hij
        change (e i).hom ≫ C.d i j = U.map 0 ≫ (e j).hom
        rw [hd, U.map_zero, comp_zero, zero_comp])
    let eD : U.mapDerivedCategory.obj (DerivedCategory.Q.obj M) ≅ K.obj :=
      U.mapDerivedCategoryFactors.app M ≪≫ DerivedCategory.Q.mapIso eC ≪≫ eK.symm
    have hM : DerivedCategory.pointFiniteDimensional F (DerivedCategory.Q.obj M) := by
      obtain ⟨⟨s, hs⟩, hf⟩ := K.property
      refine ⟨⟨s, ?_⟩, ?_⟩
      · intro i hi
        let eH := (U.mapDerivedCategoryHomologyFunctorIso i).app
          (DerivedCategory.Q.obj M) ≪≫ (H' i).mapIso eD
        have hz := (hs i hi).of_iso eH
        exact IsZero.of_full_of_faithful_of_isZero U _ hz
      · intro i
        let eH := (U.mapDerivedCategoryHomologyFunctorIso i).app
          (DerivedCategory.Q.obj M) ≪≫ (H' i).mapIso eD
        have hfU := (Module.Finite.equiv_iff eH.toLinearEquiv).mpr (hf i)
        let : RingHomSurjective
            (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom :=
          ⟨ULift.up_surjective⟩
        exact (LinearMap.finite_iff_of_bijective
          (show (H i).obj (DerivedCategory.Q.obj M) →ₛₗ[
              (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom]
              U.obj ((H i).obj (DerivedCategory.Q.obj M)) from
            { toFun := ULift.up
              map_add' := by intros; rfl
              map_smul' := by intros; rfl }) ULift.up_bijective).mpr hfU
    exact ⟨⟨DerivedCategory.Q.obj M, hM⟩, ⟨ObjectProperty.isoMk _ eD⟩⟩
  exact ⟨faithful, full, ess⟩

/-- The inverse of the specified universe lift, determined by its equivalence counit.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreSizeDescent (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).FullSubcategory ⥤
      (DerivedCategory.pointFiniteDimensional F).FullSubcategory :=
  letI := pointFibreSizeLift_equivalence F
  (pointFibreSizeLift F).asEquivalence.inverse

private noncomputable instance pointFibreSizeLift_additive (F : Type u) [Field F] :
    (pointFibreSizeLift F).Additive := by
  constructor
  intro X Y f g
  apply ObjectProperty.hom_ext
  exact (pointFibreModuleLift F).mapDerivedCategory.map_add

private noncomputable instance pointFibreSizeDescent_additive (F : Type u) [Field F] :
    (pointFibreSizeDescent F).Additive := by
  let := pointFibreSizeLift_equivalence F
  have : (pointFibreSizeLift F).asEquivalence.functor.Additive :=
    pointFibreSizeLift_additive F
  exact (pointFibreSizeLift F).asEquivalence.inverse_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointFibreSizeDescent_smul (F : Type u) [Field F]
    (X Y : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).FullSubcategory)
    (a : F) (f : X ⟶ Y) :
    (pointFibreSizeDescent F).map (ULift.up a • f) =
      a • (pointFibreSizeDescent F).map f := by
  let := pointFibreSizeLift_equivalence F
  let U := pointFibreSizeLift F
  let G := pointFibreSizeDescent F
  let ε := U.asEquivalence.counitIso
  have hn (g : X ⟶ Y) : U.map (G.map g) = ε.hom.app X ≫ g ≫ ε.inv.app Y := by
    exact CategoryTheory.Functor.fun_inv_map U X Y g
  have hU (V W : (DerivedCategory.pointFiniteDimensional F).FullSubcategory)
      (g : V ⟶ W) : U.map (a • g) = ULift.up a • U.map g := by
    apply ObjectProperty.hom_ext
    exact pointDerived_semilinear
      (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom
      (pointFibreModuleLift F) (by intros; rfl) _ _ a g.hom
  apply U.map_injective
  rw [hU, hn, hn]
  simp only [Linear.comp_smul, Linear.smul_comp]

section PointRationalConstruction

attribute [local irreducible] pointFibreSizeDescent integralCoefficientLinear

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exactness of evaluation after restriction along constant sections.
Source: blueprint order 1509, evaluation paragraph
(blueprint: lemma-perfect-complexes-geometric-point).
Proof: point_proEtale_sections_exact makes evaluation at the final object exact.
Restriction of scalars preserves kernels and cokernels on underlying groups, hence
the composite preserves finite limits and finite colimits. -/
theorem pointFibreFinite_exact (A : Type u) [CommRing A] :
    PreservesFiniteLimits (pointFiniteSections D.k A) ∧
      PreservesFiniteColimits (pointFiniteSections D.k A) := by
  let A' := (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))
  let : IsAlgClosed D.k := pointFibreBaseIsAlgClosed D
  let : PreservesFiniteLimits (pointModuleSections D.k A') :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A').1
  let : PreservesFiniteColimits (pointModuleSections D.k A') :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A').2.1
  change
    PreservesFiniteLimits
        (pointModuleSections D.k A' ⋙
          ModuleCat.restrictScalars (pointConstantSectionMap D.k A)) ∧
      PreservesFiniteColimits
        (pointModuleSections D.k A' ⋙
          ModuleCat.restrictScalars (pointConstantSectionMap D.k A))
  exact ⟨inferInstance, inferInstance⟩

/-- Kernel preservation for exact point sections.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreFiniteLimits (A : Type u) [CommRing A] :
    PreservesFiniteLimits (pointFiniteSections D.k A) :=
  (pointFibreFinite_exact D A).1

/-- Cokernel preservation for exact point sections.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreFiniteColimits (A : Type u) [CommRing A] :
    PreservesFiniteColimits (pointFiniteSections D.k A) :=
  (pointFibreFinite_exact D A).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact integral evaluation and flat fraction-field tensor in the recorded lift.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: evaluation is exact by point_proEtale_sections_exact; restriction along the
constant-section map is exact on underlying groups. The coefficient field is the
localization of its integer ring at the uniformizer, hence flat. ULift transports
these rings and tensor without altering the actions, kernels or cokernels. -/
theorem pointFibreIntegral_exact :
    PreservesFiniteLimits (pointIntegralSections l E D.k) ∧
      PreservesFiniteColimits (pointIntegralSections l E D.k) := by
  let : IsAlgClosed D.k := pointFibreBaseIsAlgClosed D
  let A := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))
  let : PreservesFiniteLimits (pointModuleSections D.k A) :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A).1
  let : PreservesFiniteColimits (pointModuleSections D.k A) :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A).2.1
  change
    PreservesFiniteLimits
        (pointModuleSections D.k A ⋙
          ModuleCat.restrictScalars (pointIntegralSectionMap l E D.k)) ∧
      PreservesFiniteColimits
        (pointModuleSections D.k A ⋙
          ModuleCat.restrictScalars (pointIntegralSectionMap l E D.k))
  exact ⟨inferInstance, inferInstance⟩

/-- Flatness of the lifted fraction-field coefficient map.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: E is the localization of O_E at its uniformizer. Localization is flat,
so tensor preserves kernels; its adjunction preserves cokernels. -/
theorem pointFibreFraction_exact :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)) := by
  have hloc : IsLocalization.Away (Padic.coefficientExtensionUniformizer l E) E :=
    (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).1
  have hflat : (algebraMap (Padic.coefficientExtensionIntegers l E) E).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat E (Submonoid.powers (Padic.coefficientExtensionUniformizer l E)))
  have hf : (pointIntegralToField l E).Flat :=
    ((RingHom.Flat.of_bijective
      (ULift.ringEquiv : ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l E) ≃+*
          Padic.coefficientExtensionIntegers l E).bijective).comp hflat).comp
      (RingHom.Flat.of_bijective
        (ULift.ringEquiv : ULift.{u + 1, u} E ≃+* E).symm.bijective)
  refine ⟨ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf, ?_⟩
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).leftAdjoint_preservesColimits
  infer_instance

/-- Kernel preservation for completed-coefficient evaluation.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreIntegralLimits :
    PreservesFiniteLimits (pointIntegralSections l E D.k) :=
  (pointFibreIntegral_exact D l E).1

/-- Cokernel preservation for completed-coefficient evaluation.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreIntegralColimits :
    PreservesFiniteColimits (pointIntegralSections l E D.k) :=
  (pointFibreIntegral_exact D l E).2

/-- Kernel preservation for the fraction-field tensor.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreFractionLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)) := (pointFibreFraction_exact l E).1

/-- Cokernel preservation for the fraction-field tensor.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreFractionColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)) := (pointFibreFraction_exact l E).2

/-- Integral derived sections with the recorded canonical coefficient action.
Source: blueprint order 1509, clause 2
(blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable abbrev pointFibreIntegralAmbient :=
  (pointIntegralSections l E D.k).mapDerivedCategory

/-- Rational derived sections, tensoring with E after exact integral evaluation.
Source: blueprint order 1509, clause 3
(blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable abbrev pointFibreRationalAmbient :
    DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
  pointFibreIntegralAmbient D l E ⋙
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory

include hl in
/-- The three section functors land in the recorded point targets.
Source: blueprint order 1509, clauses 1--3
(blueprint: lemma-perfect-complexes-geometric-point).
Proof: represent the derived object by a cochain complex. Exact evaluation and flat
fraction-field tensor have the mapDerivedCategoryFactors comparison with termwise
sections. Apply all three clauses of lem-weil-point-sections-finiteness. Transport
along these isomorphisms and the canonical ULift coefficient equivalences. This
preserves finite support, finiteness, finite generation and derived completeness. -/
theorem pointFibre_sections_mem (n : ℕ) (hn : 1 ≤ n) :
    (∀ K : (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).FullSubcategory,
      DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
          K.obj)) ∧
    (∀ K : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
        ((pointFibreIntegralAmbient D l E).obj K.obj) ∧
      DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
        ((pointFibreRationalAmbient D l E).obj K.obj)) := by
  have h := point_sections_finiteness D l hl E n hn
  constructor
  · intro K
    let C := DerivedCategory.Q.objPreimage K.obj
    let e := DerivedCategory.Q.objObjPreimageIso K.obj
    let : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    have : (intrinsicFiniteTorsionConstructible l E n hn
        (Spec (.of D.k))).IsClosedUnderIsomorphisms :=
      (proEtale_bounded_constructible_isTriangulated
        (Spec (.of D.k)) (Padic.coefficientExtensionRing l E n)).1
    have hC := h.1 C ((intrinsicFiniteTorsionConstructible l E n hn
      (Spec (.of D.k))).prop_of_iso e.symm K.property)
    apply pointFinite_of_iso _ hC
    exact ((pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E n)).mapDerivedCategoryFactors.app C).symm ≪≫
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.mapIso e
  · intro K
    let C := DerivedCategory.Q.objPreimage K.obj
    let e := DerivedCategory.Q.objObjPreimageIso K.obj
    have hC := h.2 C ((sfIntegralConstructible l E (Spec (.of D.k))).prop_of_iso e.symm K.property)
    let eI := ((pointIntegralSections l E D.k).mapDerivedCategoryFactors.app C).symm ≪≫
      (pointIntegralSections l E D.k).mapDerivedCategory.mapIso e
    refine ⟨pointFg_of_iso _ eI hC.1, ?_⟩
    apply pointFd_of_iso _ hC.2
    exact ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategoryFactors.app
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.mapIso eI

/-- Clause 2: sections of completed integral modules, with their actual O_E action.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointIntegralFibre :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      (DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory :=
  (DerivedCategory.pointFgComplete
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).lift
      ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreIntegralAmbient D l E)
      (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).1)

/-- O_E-linearity of the integral fibre on every derived morphism.
Source: blueprint order 1509, clause 2 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: the constant-to-completion map defines the source and section-module actions.
Evaluation is linear on chain maps. The equality survives localization on roofs, since
composition and inversion of quasi-isomorphisms commute with the coefficient action. -/
theorem pointIntegralFibre_linear
    (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (a : Padic.coefficientExtensionIntegers l E) (f : K ⟶ M) :
    ((pointIntegralFibre D l hl E).map (a • f)).hom =
      ULift.up a • ((pointIntegralFibre D l hl E).map f).hom := by
  let Y := Spec (.of D.k)
  let S := pointIntegralSections l E D.k
  let A := S.mapDerivedCategory
  let ν : 𝟭 (DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))) ⟶ 𝟭 _ :=
    { app := fun X ↦ ULift.up a • 𝟙 X
      naturality := by
        intro X Z g
        change g ≫ (ULift.up a • 𝟙 Z) = (ULift.up a • 𝟙 X) ≫ g
        rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] }
  have hμ (X : DerivedCategory (scalarReductionSource l E Y)) :
      A.map ((integralScalarDerivedAction l E Y a).app X) = ULift.up a • 𝟙 _ := by
    apply IntegralScalarAux.action_descent
      (DerivedCategory.Q : CochainComplex (scalarReductionSource l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (scalarReductionSource l E Y) (.up ℤ))
      (S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      A S.mapDerivedCategoryFactors
      (integralScalarDerivedAction l E Y a) ν
      (fun C ↦ (integralScalarChainAction l E Y a).app C)
      (integralScalarDerivedAction_app_Q l E Y a) (fun C ↦ ?_) X
    have he : (S.mapHomologicalComplex (.up ℤ)).map
        ((integralScalarChainAction l E Y a).app C) =
        ULift.up a • 𝟙 ((S.mapHomologicalComplex (.up ℤ)).obj C) := by
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        rw [integralScalarChainAction_termwise]
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (C.X i).val.obj (Opposite.op (Scheme.ProEt.mk (𝟙 Y))) at x
        change integralScalarConstant l E Y (Opposite.op (Scheme.ProEt.mk (𝟙 Y))) a • x =
          pointIntegralSectionMap l E D.k (ULift.up a) • x
        rw [← pointCompletedConstant_eq]
        rfl
    dsimp only [CategoryTheory.Functor.comp_map, ν]
    simp only [he, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    with_unfolding_all rfl
  have hf := (sfIntegralConstructible_linear l E Y).1 a K.obj M.obj f.hom
  change A.map (a • f.hom) = ULift.up a • A.map f.hom
  simp only [hf, A.map_comp, hμ]
  change (ULift.up a • 𝟙 (A.obj K.obj)) ≫ A.map f.hom = ULift.up a • A.map f.hom
  rw [Linear.smul_comp, Category.id_comp]

/-- Integral sections tensored with E, followed by the canonical descent of module size.
Source: blueprint order 1509, clause 3
(blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointIntegralRationalFibre :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).lift
    ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreRationalAmbient D l E)
    (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2) ⋙
      pointFibreSizeDescent E

private noncomputable instance pointIntegralRationalFibre_additive :
    (pointIntegralRationalFibre D l hl E).Additive := by
  constructor
  intro K M f g
  let J := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).lift
    ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreRationalAmbient D l E)
    (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2)
  with_unfolding_all
    change (pointFibreSizeDescent E).map (J.map (f + g)) =
      (pointFibreSizeDescent E).map (J.map f) + (pointFibreSizeDescent E).map (J.map g)
  have hJ : J.map (f + g) = J.map f + J.map g := by
    apply ObjectProperty.hom_ext
    exact (pointFibreRationalAmbient D l E).map_add
  rw [hJ]
  exact (pointFibreSizeDescent E).map_add

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension sends scalar multiples of maps to the corresponding
scalar multiples over the target ring, by the balanced tensor relation. -/
private theorem pointExtendScalars_semilinear
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    (φ : R →+* S) (M N : ModuleCat.{v} R) (a : R) (f : M ⟶ N) :
    (ModuleCat.extendScalars φ).map (a • f) = φ a • (ModuleCat.extendScalars φ).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
      change b ⊗ₜ[R, φ] (a • f.hom x) = _
      rw [TensorProduct.tmul_smul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem pointIntegralRationalFibre_smul
    (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (a : Padic.coefficientExtensionIntegers l E) (f : K ⟶ M) :
    (pointIntegralRationalFibre D l hl E).map (a • f) =
      (algebraMap (Padic.coefficientExtensionIntegers l E) E a) •
        (pointIntegralRationalFibre D l hl E).map f := by
  let T := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)
  have hT := pointDerived_semilinear (pointIntegralToField l E) T
    (fun M N a f ↦ pointExtendScalars_semilinear (pointIntegralToField l E) M N a f)
  let J := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).lift
    ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreRationalAmbient D l E)
    (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2)
  change (pointFibreSizeDescent E).map (J.map (a • f)) = _
  have hJ : J.map (a • f) = ULift.up (algebraMap
      (Padic.coefficientExtensionIntegers l E) E a) • J.map f := by
    apply ObjectProperty.hom_ext
    change T.mapDerivedCategory.map ((pointFibreIntegralAmbient D l E).map (a • f.hom)) = _
    rw [show (pointFibreIntegralAmbient D l E).map (a • f.hom) =
      ULift.up a • (pointFibreIntegralAmbient D l E).map f.hom from
        pointIntegralFibre_linear D l hl E K M a f]
    rw [hT]
    rfl
  rw [hJ]
  exact pointFibreSizeDescent_smul E _ _ _ _

attribute [local irreducible] pointIntegralRationalFibre

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Balanced extension of an integral functor to the raw tensor morphisms.
The proof is kept abstract so coefficient-category definitions do not enter its
identity, composition, and generator calculations. -/
private theorem pointScalarExtension_existsUnique
    {R : Type r} [CommRing R] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear R C] (t : R)
    {E : Type u} [Field E] [Algebra R E] {B : Type s} [Category.{z} B]
    [Preadditive B] [Linear E B] (I : C ⥤ B) [I.Additive]
    (c : Localization.Away t →ₐ[R] E)
    (hI : ∀ (K M : C) (a : R) (f : K ⟶ M),
      I.map (a • f) = algebraMap R E a • I.map f) :
    ∃! F : ScalarLocalization R C t ⥤ B,
      (∀ K, F.obj K = I.obj K.obj) ∧
      (∀ (K M : C) (f : K ⟶ M) (a : Localization.Away t),
        HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk M))
          (c a • I.map f)) := by
  classical
  let β (K M : C) : Localization.Away t →+ (K ⟶ M) →+ (I.obj K ⟶ I.obj M) :=
    { toFun := fun a ↦
        { toFun := fun f ↦ c a • I.map f
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      map_zero' := by ext f; simp
      map_add' := by intros; ext f; simp [add_smul] }
  have hb (K M : C) (r : R) (a : Localization.Away t) (f : K ⟶ M) :
      β K M (r • a) f = β K M a (r • f) := by
    dsimp [β]
    rw [Algebra.smul_def, map_mul, AlgHom.commutes,
      hI, smul_smul, mul_comm]
  let k (K M : C) : Localization.Away t ⊗[R] (K ⟶ M) →+ (I.obj K ⟶ I.obj M) :=
    TensorProduct.liftAddHom (β K M) (hb K M)
  let F : ScalarLocalization R C t ⥤ B :=
    { obj := fun K ↦ I.obj K.obj
      map := fun {K M} f ↦ k K.obj M.obj f
      map_id := by intro K; change c 1 • I.map (𝟙 K.obj) = _; simp
      map_comp := by
        intro K M N f g
        change k K.obj N.obj
          (ScalarLocalization.composition R C t K.obj M.obj N.obj g f) =
            k K.obj M.obj f ≫ k M.obj N.obj g
        induction g using TensorProduct.inductionOn with
        | tmul b g =>
            induction f using TensorProduct.inductionOn with
            | tmul a f =>
                rw [ScalarLocalization.composition_tmul]
                change c (b * a) • I.map (f ≫ g) =
                  (c a • I.map f) ≫ (c b • I.map g)
                simp [map_mul, I.map_comp, smul_smul]
            | add f f' hf hf' => simp [map_add, hf, hf', Preadditive.add_comp]
        | add g g' hg hg' =>
            simp [map_add, hg, hg', Preadditive.comp_add] }
  have hF (K M : C) (f : K ⟶ M) (a : Localization.Away t) :
      F.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk M) =
        c a • I.map f := rfl
  refine ⟨F, ⟨fun _ ↦ rfl, fun K M f a ↦ heq_of_eq (hF K M f a)⟩,
    ?_⟩
  intro J hJ
  refine CategoryTheory.Functor.ext hJ.1 ?_
  intro K M f
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers t) (K.obj ⟶ M.obj)
  have he (z : LocalizedModule (Submonoid.powers t) (K.obj ⟶ M.obj)) :
      J.map (e z) = eqToHom (hJ.1 K) ≫ F.map (e z) ≫ eqToHom (hJ.1 M).symm := by
    induction z using LocalizedModule.induction_on with
    | h g b =>
        rw [LocalizedModule.equivTensorProduct_apply_mk]
        apply (conj_eqToHom_iff_heq _ _ (hJ.1 K) (hJ.1 M)).2
        exact (hJ.2 K.obj M.obj g (Localization.mk 1 b)).trans
          (heq_of_eq (hF K.obj M.obj g (Localization.mk 1 b)).symm)
  simpa using he (e.symm f)

private theorem pointHom_heq {C : Type v} [Category.{w} C] (P : ObjectProperty C)
    {A B A' B' : P.FullSubcategory} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f.hom g.hom) : HEq f g := by
  subst A'
  subst B'
  exact heq_of_eq (ObjectProperty.hom_ext P (eq_of_heq h))

private theorem pointHom_hom_heq {C : Type v} [Category.{w} C]
    (P : ObjectProperty C) {A B A' B' : P.FullSubcategory}
    (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'}
    (h : HEq f g) : HEq f.hom g.hom := by
  subst A'
  subst B'
  exact heq_of_eq (congrArg (fun f : A ⟶ B ↦ f.hom) (eq_of_heq h))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unique extension to the raw rational Hom tensor groups, fixed on all pure tensors.
Source: blueprint order 1509, clause 3
(blueprint: lemma-perfect-complexes-geometric-point).
Proof: exact sections are O_E-linear, and tensor with E converts integral scalar action
into multiplication in E. Extend each Hom map by the tensor universal property, using
the canonical localization-field equivalence. Identities and composition hold on pure
tensors and then by additivity. Objects and every pure-tensor image are specified, so
the tensor generators and functor extensionality prove uniqueness. -/
theorem pointRationalFibre_existsUnique :
    ∃! F : sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
        (DerivedCategory.pointFiniteDimensional E).FullSubcategory,
      (∀ K, F.obj K = (pointIntegralRationalFibre D l hl E).obj K.obj) ∧
      (∀ (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (f : K ⟶ M) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K ⟶
            (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj M)).hom
          ((sfRationalCoefficientEquiv l E a) •
            ((pointIntegralRationalFibre D l hl E).map f).hom)) := by
  let I := pointIntegralRationalFibre D l hl E
  obtain ⟨F, hF, huniq⟩ := pointScalarExtension_existsUnique
    (Padic.coefficientExtensionUniformizer l E) I (sfRationalCoefficientEquiv l E)
    (fun K M a f ↦ pointIntegralRationalFibre_smul D l hl E K M a f)
  refine ⟨F, ⟨hF.1, ?_⟩, ?_⟩
  · intro K M f a
    exact pointHom_hom_heq _ (hF.1 _) (hF.1 _) (hF.2 K M f a)
  · intro J hJ
    apply huniq J
    refine ⟨hJ.1, ?_⟩
    intro K M f a
    apply pointHom_heq _ (hJ.1 _) (hJ.1 _)
    exact hJ.2 K M f a

/-- Clause 3: the rational point fibre, with the specified tensor-Hom action.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointRationalFibre :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
      (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (pointRationalFibre_existsUnique D l hl E).exists.choose

end PointRationalConstruction

/-- The inverse coefficient-ring identification, without changing the module carrier.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable abbrev pointFibreCoefficientDown (F : Type u) [Field F] :
    ModuleCat.{u + 1} (ULift.{u + 1, u} F) ⥤ ModuleCat.{u + 1} F :=
  ModuleCat.restrictScalars.{u + 1, u, u + 1}
    (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom

/-- Coefficient identification is exact.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: the inverse coefficient identification is an equivalence, acting identically
on underlying additive groups and on maps. It preserves kernels and cokernels. -/
theorem pointFibreCoefficientDown_exact (F : Type u) [Field F] :
    PreservesFiniteLimits (pointFibreCoefficientDown F) ∧
      PreservesFiniteColimits (pointFibreCoefficientDown F) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Exactness at kernels for coefficient identification.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreCoefficientDownLimits (F : Type u) [Field F] :
    PreservesFiniteLimits (pointFibreCoefficientDown F) :=
  (pointFibreCoefficientDown_exact F).1

/-- Exactness at cokernels for coefficient identification.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable instance pointFibreCoefficientDownColimits (F : Type u) [Field F] :
    PreservesFiniteColimits (pointFibreCoefficientDown F) :=
  (pointFibreCoefficientDown_exact F).2

/-- Cancelling the coefficient lift is uniquely fixed on every module element.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: both carriers are ULift M. Send up x to up x; the two coefficient actions
are equal since the inverse ring identifications cancel. This is a linear
bijection natural in M. Every carrier element is up x, giving uniqueness. -/
theorem pointFibreLiftDown_existsUnique (F : Type u) [Field F] :
    ∃! e : pointFibreModuleLift F ⋙ pointFibreCoefficientDown F ≅
        ModuleCat.uliftFunctor.{u + 1, u} F,
      ∀ (M : ModuleCat.{u} F) (x : M), e.hom.app M (ULift.up x) = ULift.up x := by
  let e : pointFibreModuleLift F ⋙ pointFibreCoefficientDown F ≅
      ModuleCat.uliftFunctor.{u + 1, u} F :=
    CategoryTheory.Functor.associator _ _ _ ≪≫
      CategoryTheory.Functor.isoWhiskerLeft _
        ((ModuleCat.restrictScalarsComp' _ _ _
          (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom_comp_symm_toRingHom.symm).symm
          ≪≫ ModuleCat.restrictScalarsId F) ≪≫
      CategoryTheory.Functor.rightUnitor _
  refine ⟨e, ?_, ?_⟩
  · intro M x
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    exact he' M x

/-- The normalized cancellation of the two coefficient identifications in D(F).
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreLiftDownIso (F : Type u) [Field F] :
    (pointFibreModuleLift F).mapDerivedCategory ⋙
        (pointFibreCoefficientDown F).mapDerivedCategory ≅
      (ModuleCat.uliftFunctor.{u + 1, u} F).mapDerivedCategory :=
  CategoryTheory.Functor.mapDerivedCategoryCompIso _ _ ≪≫
    CategoryTheory.Functor.mapDerivedCategoryNatIso
      (pointFibreLiftDown_existsUnique F).exists.choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A tensor map induced by a ring homomorphism respects multiplication on
its first tensor factor. Keeping this proof abstract avoids repeated coefficient
and section-functor reductions. -/
private theorem tensorMap_smul
    {R' : Type r} {R : Type s} {A : Type u} {B : Type v}
    {M : Type w} {N : Type z} [CommRing R'] [CommRing R]
    [CommRing A] [CommRing B] [Algebra R' A] [Algebra R B]
    [AddCommGroup M] [AddCommGroup N] [Module R' M] [Module R N]
    (σ : R' →+* R) (eA : A →ₛₗ[σ] B) (eM : M →ₛₗ[σ] N)
    (τ : A →+* B) (hτ : ∀ a, eA a = τ a) (a : A) (x : A ⊗[R'] M) :
    TensorProduct.map eA eM (a • x) = τ a • TensorProduct.map eA eM x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
      simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, hτ, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rational coefficient transport is fixed by its formula on all pure tensors.
Source: blueprint order 1509, clause 3 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: the underlying integral section module is the same in both encodings.
The balanced map sends up a tensor n to a tensor n, and its inverse lifts a.
These formulas respect balancing because both constant coefficient maps are the
same after ULift. They are inverse, natural linear maps. Pure tensors generate,
so the natural isomorphism is unique. -/
theorem pointFibreRationalDown_existsUnique :
    ∃! e : pointIntegralSections l E D.k ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
        pointFibreCoefficientDown E ≅
      pointCompletedSections D.k l E ⋙ pointModuleRationalization l E,
      ∀ (M : scalarReductionSource.{u, u} l E (Spec (.of D.k)))
        (a : E) (x : (pointIntegralSections l E D.k).obj M),
        e.hom.app M (ULift.up a ⊗ₜ[ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E), pointIntegralToField l E] x) =
            a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (@id ((pointCompletedSections D.k l E).obj M) x) := by
  let R := Padic.coefficientExtensionIntegers l E
  let R' := ULift.{u + 1, u} R
  let E' := ULift.{u + 1, u} E
  let : Algebra R' E' := (pointIntegralToField l E).toAlgebra
  let S := pointIntegralSections l E D.k
  let T := pointCompletedSections D.k l E
  let A := S ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E) ⋙ pointFibreCoefficientDown E
  let B := T ⋙ pointModuleRationalization l E
  let σ := (ULift.ringEquiv : R' ≃+* R).toRingHom
  let τ := (ULift.ringEquiv : R' ≃+* R).symm.toRingHom
  let : RingHomInvPair σ τ := RingHomInvPair.of_ringEquiv (ULift.ringEquiv : R' ≃+* R)
  let : RingHomInvPair τ σ := RingHomInvPair.of_ringEquiv_symm (ULift.ringEquiv : R' ≃+* R)
  let eF : E' ≃ₛₗ[σ] E :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eM (M : scalarReductionSource l E (Spec (.of D.k))) :
      S.obj M ≃ₛₗ[σ] T.obj M :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eR (M : scalarReductionSource l E (Spec (.of D.k))) :=
    TensorProduct.congr eF (eM M)
  let e (M : scalarReductionSource l E (Spec (.of D.k))) : A.obj M ≃ₗ[E] B.obj M :=
    { (eR M).toAddEquiv with
      map_smul' := by
        intro a x
        exact tensorMap_smul
          (ULift.ringEquiv : R' ≃+* R).toRingHom eF.toLinearMap (eM M).toLinearMap
          (ULift.ringEquiv : E' ≃+* E).toRingHom (fun _ ↦ rfl)
          (ULift.up.{u + 1, u} a) x }
  let η : A ≅ B := NatIso.ofComponents (fun M ↦ (e M).toModuleIso) (by
    intro M N h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy])
  refine ⟨η, fun _ _ _ ↦ rfl, ?_⟩
  intro η' hη'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x => exact hη' M a.down x
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical identification of the two rational section encodings.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreRationalDownIso :
    pointFibreRationalAmbient D l E ⋙
        (pointFibreCoefficientDown E).mapDerivedCategory ≅
      pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E :=
  letI := pointCompletedSectionsAdditive D.k l E
  letI := pointCompletedSectionsLimits D.k l E
  letI := pointCompletedSectionsColimits D.k l E
  letI := pointModuleRationalizationAdditive l E
  letI := pointModuleRationalizationLimits l E
  letI := pointModuleRationalizationColimits l E
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft _
      (CategoryTheory.Functor.mapDerivedCategoryCompIso _ _) ≪≫
    CategoryTheory.Functor.mapDerivedCategoryCompIso _ _ ≪≫
    CategoryTheory.Functor.mapDerivedCategoryNatIso
      (pointFibreRationalDown_existsUnique D l E).exists.choose ≪≫
    (CategoryTheory.Functor.mapDerivedCategoryCompIso _ _).symm

/-- The common-lift rational object before descending its size.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreRationalLarge
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).FullSubcategory :=
  ⟨(pointFibreRationalAmbient D l E).obj K.obj,
    ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2⟩

/-- The specified size-descent counit identifies the small fibre with actual sections.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointIntegralRationalNormalization
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj
        ((pointIntegralRationalFibre D l hl E).obj K).obj ≅
      (pointModuleDerivedRationalization l E).obj
        ((pointCompletedDerivedSections D.k l E).obj K.obj) :=
  letI := pointFibreSizeLift_equivalence E
  (pointFibreLiftDownIso E).symm.app ((pointIntegralRationalFibre D l hl E).obj K).obj ≪≫
    (pointFibreCoefficientDown E).mapDerivedCategory.mapIso
      ((DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι.mapIso
        ((pointFibreSizeLift E).asEquivalence.counitIso.app
          (pointFibreRationalLarge D l hl E K))) ≪≫
    (pointFibreRationalDownIso D l E).app K.obj

/-- The object identity fixed by rationalization's defining universal property.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointRationalFibreObjIso
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj K ≅ (pointIntegralRationalFibre D l hl E).obj K.obj :=
  eqToIso ((pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 K)

/-- Rational normalization with the specified raw-localization object equality inserted.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointRationalNormalization
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj
        ((pointRationalFibre D l hl E).obj K).obj ≅
      (pointModuleDerivedRationalization l E).obj
        ((pointCompletedDerivedSections D.k l E).obj K.obj.obj) :=
  (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional E).ι.mapIso (pointRationalFibreObjIso D l hl E K)) ≪≫
      pointIntegralRationalNormalization D l hl E K.obj

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar tensor commutes with carrier lift by the prescribed pure-tensor map.
Source: blueprint order 1509, clause 4 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: send up (a tensor x) to a tensor up x. Balancing is unchanged and the
inverse sends a tensor up x to up (a tensor x). The formulas commute with all
module maps. Pure tensors generate, giving uniqueness. -/
theorem pointFibreTensorLift_existsUnique :
    ∃! e : ModuleCat.extendScalars.{u, u, u} ι.toRingHom ⋙
        ModuleCat.uliftFunctor.{u + 1, u} L ≅
      ModuleCat.uliftFunctor.{u + 1, u} E ⋙
        ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom,
      ∀ (M : ModuleCat.{u} E) (a : L) (x : M),
        e.hom.app M (ULift.up (a ⊗ₜ[E, ι.toRingHom] x)) =
          a ⊗ₜ[E, ι.toRingHom] ULift.up x := by
  let := ι.toRingHom.toAlgebra
  let e (M : ModuleCat.{u} E) :
      ULift.{u + 1, u} (L ⊗[E] M) ≃ₗ[L] L ⊗[E] ULift.{u + 1, u} M :=
    ULift.moduleEquiv ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
        ULift.moduleEquiv.symm
  let η : ModuleCat.extendScalars.{u, u, u} ι.toRingHom ⋙
        ModuleCat.uliftFunctor.{u + 1, u} L ≅
      ModuleCat.uliftFunctor.{u + 1, u} E ⋙
        ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom :=
    NatIso.ofComponents (fun M ↦ (e M).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x⟩ := x
      induction x using TensorProduct.inductionOn with
      | tmul a x => rfl
      | add x y hx hy =>
          rw [show ULift.up (x + y) =
            (ULift.up x + ULift.up y : ULift.{u + 1} (L ⊗[E] M)) from rfl]
          simp only [map_add, hx, hy])
  refine ⟨η, ?_, ?_⟩
  · intro M a x
    rfl
  · intro η' hη'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    induction x using TensorProduct.inductionOn with
    | tmul a x => exact hη' M a x
    | add x y hx hy =>
        rw [show ULift.up (x + y) =
          (ULift.up x + ULift.up y : ULift.{u + 1} (L ⊗[E] M)) from rfl]
        simp only [map_add, hx, hy]

/-- The canonical tensor/lift comparison descended through localization.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreTensorLiftIso :
    DerivedCategory.fieldDerivedScalarExtension ι.toRingHom ⋙
        (ModuleCat.uliftFunctor.{u + 1, u} L).mapDerivedCategory ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory ⋙
        pointCoefficientFieldDerivedTensor l E L ι :=
  CategoryTheory.Functor.mapDerivedCategoryCompIso _ _ ≪≫
    CategoryTheory.Functor.mapDerivedCategoryNatIso
      (pointFibreTensorLift_existsUnique l E L ι).exists.choose ≪≫
    (CategoryTheory.Functor.mapDerivedCategoryCompIso _ _).symm

attribute [local irreducible] pointIntegralRationalFibre pointFibreSizeDescent
  pointFibreLiftDownIso pointFibreRationalDownIso
  pointRationalNormalization pointIntegralRationalNormalization

attribute [local irreducible] pointFibreTensorLiftIso

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private noncomputable abbrev pointFdCarrierLift (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional F).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u + 1} F) :=
  (DerivedCategory.pointFiniteDimensional F).ι ⋙
    (ModuleCat.uliftFunctor.{u + 1, u} F).mapDerivedCategory

@[irreducible] private noncomputable def pointIntegralRationalNormalizationIso :
    pointIntegralRationalFibre D l hl E ⋙ pointFdCarrierLift E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E := by
  let := pointFibreSizeLift_equivalence E
  let J := (DerivedCategory.pointFiniteDimensional E).ι
  let J' := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι
  let V := (pointFibreCoefficientDown E).mapDerivedCategory
  let A := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).lift
    ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreRationalAmbient D l E)
    (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2)
  with_unfolding_all
    change (A ⋙ (pointFibreSizeLift E).asEquivalence.inverse) ⋙ pointFdCarrierLift E ≅ _
  exact Functor.isoWhiskerLeft
      ((A ⋙ (pointFibreSizeLift E).asEquivalence.inverse) ⋙ J)
      (pointFibreLiftDownIso E).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft A (pointFibreSizeLift E).asEquivalence.counitIso) (J' ⋙ V) ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible l E (Spec (.of D.k))).ι
      (pointFibreRationalDownIso D l E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def pointRationalLocalizationIso :
    sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙ pointRationalFibre D l hl E ≅
      pointIntegralRationalFibre D l hl E := by
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let R := pointRationalFibre D l hl E
  let I := pointIntegralRationalFibre D l hl E
  have h := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec
  refine NatIso.ofComponents (fun K ↦ pointRationalFibreObjIso D l hl E (Q.obj K)) ?_
  intro K M f
  have he : HEq (R.map (Q.map f)) (I.map f) := by
    apply pointHom_heq _ (h.1 (Q.obj K)) (h.1 (Q.obj M))
    simpa only [R, Q, I, pointRationalFibre, sfRationalConstructibleLocalization,
      ScalarLocalization.localization, map_one, one_smul] using h.2 K M f 1
  have he' := (conj_eqToHom_iff_heq _ _ (h.1 (Q.obj K)) (h.1 (Q.obj M))).2 he
  change R.map (Q.map f) ≫ eqToHom (h.1 (Q.obj M)) =
    eqToHom (h.1 (Q.obj K)) ≫ I.map f
  rw [he']
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

@[irreducible] private noncomputable def pointRationalNormalizationIso :
    sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙
        pointRationalFibre D l hl E ⋙ pointFdCarrierLift E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E :=
  Functor.isoWhiskerRight (pointRationalLocalizationIso D l hl E) (pointFdCarrierLift E) ≪≫
    pointIntegralRationalNormalizationIso D l hl E

section PointNormalizationComponents

private theorem pointRationalNormalizationIso_hom_app
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalNormalizationIso D l hl E).hom.app K =
      (pointRationalNormalization D l hl E
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).hom := by
  with_unfolding_all rfl

end PointNormalizationComponents

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def pointRationalScalarLocalizationIso :
    sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙
        sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k)) ⋙
        sfRationalConstructibleLocalization l L (Spec (.of D.k)) := by
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let Q' := sfRationalConstructibleLocalization l L (Spec (.of D.k))
  let T := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))
  let S := sfRationalScalarExtension l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  have h := (sfRationalScalarExtension_existsUnique l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  refine NatIso.ofComponents (fun K ↦ eqToIso (h.2.1 (Q.obj K))) ?_
  intro K M f
  have he : HEq (S.map (Q.map f)) (Q'.map (T.map f)) := by
    simpa only [Q, Q', T, S, sfRationalScalarExtension,
      sfRationalConstructibleLocalization, ScalarLocalization.localization, map_one]
      using h.2.2 K M f 1
  have he' := (conj_eqToHom_iff_heq _ _ (h.2.1 (Q.obj K)) (h.2.1 (Q.obj M))).2 he
  change S.map (Q.map f) ≫ eqToHom (h.2.1 (Q.obj M)) =
    eqToHom (h.2.1 (Q.obj K)) ≫ Q'.map (T.map f)
  rw [he']
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

@[irreducible] private noncomputable def pointIntegralScalarSectionsIso :
    sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k)) ⋙
        (sfIntegralConstructible l L (Spec (.of D.k))).ι ⋙
        pointCompletedDerivedSections D.k l L ⋙ pointModuleDerivedRationalization l L ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E ⋙
        pointCoefficientFieldDerivedTensor l E L ι :=
  NatIso.ofComponents (fun K ↦ pointRationalSectionsScalarExtensionIso l E L ι D hl K.obj
    ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)) (by
      intro K M f
      exact pointRationalSectionsNatural l E L ι D hl K.obj M.obj
        ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)
        ((pointIntegralConstructible_iff l E D hl M.obj).mpr M.property) f.hom)

@[irreducible] private noncomputable def pointRationalScalarIntegralLargeIso :
    sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙
        (sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ pointRationalFibre D l hl L) ⋙
        pointFdCarrierLift L ≅
      sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙
        (pointRationalFibre D l hl E ⋙ DerivedCategory.pointFdScalarExtension ι.toRingHom) ⋙
        pointFdCarrierLift L := by
  let U := pointFdCarrierLift L
  let T := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let R := pointRationalFibre D l hl E
  let V := pointCoefficientFieldDerivedTensor l E L ι
  exact Functor.isoWhiskerRight (pointRationalScalarLocalizationIso D l E L ι)
      (pointRationalFibre D l hl L ⋙ U) ≪≫
    Functor.isoWhiskerLeft T (pointRationalNormalizationIso D l hl L) ≪≫
    pointIntegralScalarSectionsIso D l hl E L ι ≪≫
    Functor.isoWhiskerRight (pointRationalNormalizationIso D l hl E).symm V ≪≫
    Functor.isoWhiskerLeft (Q ⋙ R ⋙ (DerivedCategory.pointFiniteDimensional E).ι)
      (pointFibreTensorLiftIso l E L ι).symm

/-- The rational scalar comparison is uniquely fixed by the recorded sections comparison.
Source: blueprint order 1509, clause 4 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: identify the carrier-only lift with the fully faithful size lift followed by
coefficient restriction. On integral objects, compose the normalized sections scalar
comparison with the size-descent counits and the tensor/lift comparison. Cancel the
fully faithful carrier lift, then extend the resulting natural isomorphism uniquely
through raw scalar localization. The scalar-one tensor specifications identify the
restricted rational functors with the integral functors. Cancelling the normalization
isomorphisms proves the required equation. This equation determines every lifted
component, so full faithfulness proves uniqueness. The redundant characteristic
parameter is fixed to zero, as in the general common-stage category. -/
theorem pointRationalFibreScalar_existsUnique :
    ∃! e : sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ pointRationalFibre D l hl L ≅
      pointRationalFibre D l hl E ⋙ DerivedCategory.pointFdScalarExtension ι.toRingHom,
      ∀ K : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
        HEq
          ((ModuleCat.uliftFunctor.{u + 1, u} L).mapDerivedCategory.map
              ((e.hom.app ((sfRationalConstructibleLocalization l E
                (Spec (.of D.k))).obj K)).hom) ≫
            (pointFibreTensorLiftIso l E L ι).hom.app
              ((pointRationalFibre D l hl E).obj
                ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).obj ≫
            (pointCoefficientFieldDerivedTensor l E L ι).map
              (pointRationalNormalization D l hl E
                ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).hom)
          ((pointIntegralRationalNormalization D l hl L
              ((sfConstructibleIntegralScalarExtension 0 l
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj K)).hom ≫
            (pointRationalSectionsScalarExtensionIso l E L ι D hl K.obj
              ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)).hom) := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let C := sfIntegralConstructibleCategory l E (Spec (.of D.k))
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let A := sfRationalScalarExtension l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ pointRationalFibre D l hl L
  let B := pointRationalFibre D l hl E ⋙ DerivedCategory.pointFdScalarExtension ι.toRingHom
  let U := pointFdCarrierLift L
  let ff : U.FullyFaithful := by
    let := pointFibreSizeLift_equivalence L
    let J := (DerivedCategory.pointFiniteDimensional L).ι
    let J' := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} L)).ι
    let V := (pointFibreCoefficientDown L).mapDerivedCategory
    let W := pointFibreSizeLift L ⋙ J' ⋙ V
    have : V.IsEquivalence := inferInstance
    have hW : W.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
    exact hW.ofIso (Functor.isoWhiskerLeft J (pointFibreLiftDownIso L))
  have : U.Full := ff.full
  have : U.Faithful := ff.faithful
  let e₀ : Q ⋙ A ≅ Q ⋙ B := Functor.fullyFaithfulCancelRight U
    (pointRationalScalarIntegralLargeIso D l hl E L ι)
  obtain ⟨e, he, _⟩ := ScalarLocalization.naturalIso_of_integral R C t A B e₀
  have hs : ∀ K : C, HEq
      (U.map (e.hom.app (Q.obj K)) ≫
        (pointFibreTensorLiftIso l E L ι).hom.app ((pointRationalFibre D l hl E).obj
          (Q.obj K)).obj ≫
        (pointCoefficientFieldDerivedTensor l E L ι).map
          (pointRationalNormalization D l hl E (Q.obj K)).hom)
      ((pointIntegralRationalNormalization D l hl L
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj K)).hom ≫
        (pointRationalSectionsScalarExtensionIso l E L ι D hl K.obj
          ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)).hom) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      intro K
      have hek : e.hom.app (Q.obj K) = e₀.hom.app K := he K
      erw [hek]
      have hm : U.map (e₀.hom.app K) =
          (pointRationalScalarIntegralLargeIso D l hl E L ι).hom.app K := by
        exact U.map_preimage _
      rw [hm]
      dsimp only [A, B, U, Q]
      erw [← pointRationalNormalizationIso_hom_app D l hl E K]
      simp only [pointRationalScalarIntegralLargeIso, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
      erw [Iso.inv_hom_id_app_assoc]
      erw [← Functor.map_comp, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.comp_id]
      erw [pointRationalNormalizationIso_hom_app]
      simp only [pointRationalNormalization, Iso.trans_hom, Functor.mapIso_hom,
        pointIntegralScalarSectionsIso, NatIso.ofComponents_hom_app,
        pointRationalScalarLocalizationIso,
        pointRationalFibreObjIso, eqToIso.hom, Functor.comp_map, eqToHom_map,
        Category.assoc, eqToHom_comp_heq_iff]
      rfl
  refine ⟨e, hs, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨K⟩ := K
  apply U.map_injective
  apply (cancel_mono
    ((pointFibreTensorLiftIso l E L ι).hom.app
        ((pointRationalFibre D l hl E).obj (Q.obj K)).obj ≫
      (pointCoefficientFieldDerivedTensor l E L ι).map
        (pointRationalNormalization D l hl E (Q.obj K)).hom)).mp
  exact eq_of_heq ((he' K).trans (hs K).symm)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The normalized rational scalar comparison used on common-stage representatives.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointRationalFibreScalarIso :=
  (pointRationalFibreScalar_existsUnique D l hl E L ι).exists.choose

/-- The tensor tower comparison restricted to the recorded finite-dimensional targets.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointFibreFdTensorTower {F G H : Type u}
    [Field F] [Field G] [Field H] (f : F →+* G) (g : G →+* H) :
    DerivedCategory.pointFdScalarExtension f ⋙ DerivedCategory.pointFdScalarExtension g ≅
      DerivedCategory.pointFdScalarExtension (g.comp f) :=
  ((DerivedCategory.pointFiniteDimensional H).fullyFaithfulι.whiskeringRight _).preimageIso
    (CategoryTheory.Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional F).ι
      (DerivedCategory.fieldScalarTower f g))

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The point fibre at a finite stage, with the recorded Shrink coefficient identification.
Source: blueprint order 1509, clause 4 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointStageFibre (F : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F ⥤
      (DerivedCategory.pointFiniteDimensional F.val).FullSubcategory :=
  pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ⋙
    DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom

/-- The small coefficient models give the same inclusion square as the actual subfields.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: coefficientInclusion is defined by conjugating the actual inclusion with the
Shrink algebra equivalences. Cancelling the equivalence with its inverse gives the
equality of ring maps, including repeated fields and identity inclusions. -/
theorem pointStageCoefficientSquare (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    (Shrink.algEquiv ℚ_[l] G.val).toRingHom.comp
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom =
      (IntermediateField.inclusion h).toRingHom.comp
        (Shrink.algEquiv ℚ_[l] F.val).toRingHom := by
  have : IsAlgClosure ℚ_[l] Ω := inferInstance
  ext x
  simp [AlgebraicallyClosedCoefficients.coefficientInclusion]

/-- The coefficient-square comparison, made from the canonical tensor tower isomorphisms.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointStageTensorSquare
    (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom ⋙
        DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom ≅
      DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom :=
  pointFibreFdTensorTower _ _ ≪≫
    eqToIso (congrArg DerivedCategory.pointFdScalarExtension
      (pointStageCoefficientSquare l Ω F G h)) ≪≫
    (pointFibreFdTensorTower _ _).symm

section PointStageScalarConstruction

attribute [local irreducible] pointStageTensorSquare
  pointRationalFibre pointRationalFibreScalarIso

/-- The finite-stage sections comparison with both recorded coefficient transports.
Its inverse is the beta used to send common-stage representatives to the target.
Source: blueprint order 1509, clause 4 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointStageFibreScalarIso
    (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h ⋙
        pointStageFibre D l hl Ω G ≅
      pointStageFibre D l hl Ω F ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom :=
  (CategoryTheory.Functor.associator
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h)
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.isoWhiskerRight
          (eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
            l Ω (Spec (.of D.k))).exists.choose_spec.1 F G h))
          (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)) ≪≫
        pointRationalFibreScalarIso D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom) ≪≫
    CategoryTheory.Functor.associator
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
      (DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom)
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft _ (pointStageTensorSquare l Ω F G h) ≪≫
    (CategoryTheory.Functor.associator
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom)
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom)).symm

end PointStageScalarConstruction

/-- The algebraically closed fibre keeps the finite coefficient stage of its object.
Source: blueprint order 1509, clause 4 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointQbarFibreObj
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    DerivedCategory.PointFdQbar l Ω :=
  ⟨A.stage, (pointStageFibre D l hl Ω A.stage).obj A.obj⟩

/-- The image of a common-stage representative: conjugate its fibre by phi and phi inverse.
Source: blueprint order 1509, clause 4
(blueprint: def-weil-point-fibre-stage-constructions). -/
noncomputable def pointQbarFibreRepresentative
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (F : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ F) (hB : B.stage ≤ F)
    (f : A.toStage hA ⟶ B.toStage hB) :
    pointQbarFibreObj D l hl Ω A ⟶ pointQbarFibreObj D l hl Ω B :=
  (DerivedCategory.pointFdQbarStageComp l Ω hA).inv.app
      ((pointStageFibre D l hl Ω A.stage).obj A.obj) ≫
    (DerivedCategory.pointFdQbarStage l Ω F).map
      ((pointStageFibreScalarIso D l hl Ω A.stage F hA).inv.app A.obj ≫
        (pointStageFibre D l hl Ω F).map f ≫
          (pointStageFibreScalarIso D l hl Ω B.stage F hB).hom.app B.obj) ≫
    (DerivedCategory.pointFdQbarStageComp l Ω hB).hom.app
      ((pointStageFibre D l hl Ω B.stage).obj B.obj)

end WeilConjectures
