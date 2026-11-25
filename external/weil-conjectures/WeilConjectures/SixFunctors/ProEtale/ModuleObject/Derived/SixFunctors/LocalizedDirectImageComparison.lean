/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationHomology
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-!
# Localization of coefficients and bounded-below direct image

Source: Hemo--Richarz--Scholbach, Lemmas 5.3(1) and 5.6; Bhatt--Scholze,
Remark 6.8.15 (blueprint: lem-sfb-localized-direct-image-comparison).

The map is the published coefficient-change mate on the ambient module categories.
Its flatness argument is supplied by the existing localization theorem, rather than
assumed of the complex or of the scheme morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Elaborate the two scalar derived functors and their geometric adjunction mate.
/-- The canonical coefficient-change/direct-image arrow. The inclusion is pulled back
from the point. The published `derivedPushHom` is the mate of the canonical restriction
comparison; equivalently it is adjoint to scalar extension of the geometric counit,
after the canonical pullback/tensor identification. Its required scalar exactness is
the last assertion of `padicIntegers_invertEll`, not an additional hypothesis.
Source: HRS Lemma 5.3(1), natural comparison (5.4), and Stacks 07A6, 07A4
(blueprint: lem-sfb-localized-direct-image-comparison). -/
def localizedDirectImageComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    (Mod.extendScalars (padicIntegersToPadicSubfield Y ℓ E)).leftDerivedFunctor.obj
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.1) f).obj C) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) f).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj C) :=
  letI : ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) Z)) :=
    fun Z ↦ (padicIntegers_invertEll Z ℓ E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
  (derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app C

set_option backward.isDefEq.respectTransparency false in
private theorem mate_unit_comap
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    (adjX : LX ⊣ UX) (adjY : LY ⊣ UY) {G : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ UY ≅ UX ⋙ G) (K : A) :
    adjY.unit.app (G.obj K) ≫
        (UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) ≫
          κ.hom.app (LX.obj K)) = G.map (adjX.unit.app K) := by
  have h := unit_mateEquiv_symm adjX adjY (TwoSquare.mk _ _ _ _ κ.inv) K
  change G.map (adjX.unit.app K) ≫ κ.inv.app (LX.obj K) =
    adjY.unit.app (G.obj K) ≫
      UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) at h
  have hh := congrArg (fun z ↦ z ≫ κ.hom.app (LX.obj K)) h.symm
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  exact hh.trans (Category.comp_id (G.map (adjX.unit.app K)))

set_option backward.isDefEq.respectTransparency false in
private theorem localization_comparison_zero (ℓ : ℕ)
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    [UX.Additive] [UY.Additive] (adjX : LX ⊣ UX) (adjY : LY ⊣ UY)
    (G : A ⥤ C) [G.Additive] (K : A)
    [IsIso (ℓ • 𝟙 (LX.obj K))] [IsIso (ℓ • 𝟙 (LY.obj (G.obj K)))]
    (g : UY.obj (LY.obj (G.obj K)) ⟶ G.obj (UX.obj (LX.obj K)))
    (hg : adjY.unit.app (G.obj K) ≫ g = G.map (adjX.unit.app K)) :
    (scalarLocalizationUnitCocone ℓ adjY (G.obj K)).ι.app 0 ≫ g =
      ((Cocone.precompose (Mod.smulSequenceCompIso G K ℓ).inv).obj
        (G.mapCocone (scalarLocalizationUnitCocone ℓ adjX K))).ι.app 0 := by
  simp only [scalarLocalizationUnitCocone, Functor.comp_obj, Functor.const_obj_obj, pow_zero,
    End.one_asHom, CategoryTheory.Functor.map_id, Category.comp_id, Mod.smulSequenceCompIso,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Cocone.precompose_obj_pt, Functor.mapCocone_pt,
    Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app]
  change adjY.unit.app (G.obj K) ≫ g = 𝟙 _ ≫ G.map (adjX.unit.app K)
  exact hg.trans (Category.id_comp (G.map (adjX.unit.app K))).symm

set_option backward.isDefEq.respectTransparency false in
-- Keep the internal localization argument abstract in the coefficient field.
private theorem bounded_integralScalarPushHom_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    IsIso ((derivedPushHom (integralScalarMap ℓ E) f).app K) := by
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  -- Cache the tensor exactness instances used by the scalar derived adjunctions.
  let : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X))),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  let : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X))),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  let : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X))),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  let : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y))),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  let : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y))),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  let : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y))),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  let a := integralScalarMap ℓ E
  let G := (lowerStar (integralCoeff ℓ E) f).rightDerivedFunctor
  let U := (Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap a Y)).mapDerivedCategory
  let UX := (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap a X)).mapDerivedCategory
  let LX := (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)
  let κ := derivedComapLowerStarIso a f
  let β : (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj (G.obj K) ⟶
      (lowerStar (Profinite.continuousMapRingObj E) f).rightDerivedFunctor.obj
        (LX.obj K) := (derivedPushHom a f).app K
  have : G.Additive := inferInstance
  have hGK : DerivedCategory.TStructure.t.plus (G.obj K) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      ((lowerStar (integralCoeff ℓ E) f).rightDerivedFunctorPlusCompatibility.app ⟨K, hK⟩)
      ((lowerStar (integralCoeff ℓ E) f).rightDerivedFunctorPlus.obj ⟨K, hK⟩).property
  let cX := integralLocalizationCocone ℓ E X K
  let cY := integralLocalizationCocone ℓ E Y (G.obj K)
  let σ := Mod.smulSequenceCompIso G K ℓ
  let d := (Cocone.precompose σ.inv).obj (G.mapCocone cX)
  let g : cY.pt ⟶ d.pt := U.map β ≫ κ.hom.app (LX.obj K)
  have : IsIso (ℓ • 𝟙 d.pt) := by
    have := derived_nsmul_isIso ℓ E X (LX.obj K)
    have h : IsIso (G.map (UX.map (ℓ • 𝟙 (LX.obj K)))) := inferInstance
    change IsIso (ℓ • 𝟙 (G.obj (UX.obj (LX.obj K))))
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using h
  have := derived_nsmul_isIso ℓ E X (LX.obj K)
  have := derived_nsmul_isIso ℓ E Y
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj (G.obj K))
  have hzero : cY.ι.app 0 ≫ g = d.ι.app 0 := by
    exact localization_comparison_zero ℓ adjX adjY G K g
      (mate_unit_comap adjX adjY κ K)
  have hU : U.ReflectsIsomorphisms := by
    let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (coefficientMap a Y)
    have : V.ReflectsIsomorphisms := by
      refine ⟨fun {M N} z hz ↦ ?_⟩
      have : IsIso z.hom := by
        change IsIso ((Mod.forget _).map (V.map z))
        infer_instance
      have : IsIso ((Mod.forget _).map z) := by
        change IsIso z.hom
        infer_instance
      exact isIso_of_reflects_iso z (Mod.forget _)
    refine ⟨fun z _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro q
    have : IsIso (V.map ((DerivedCategory.homologyFunctor _ q).map z)) :=
      (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso q) z).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ V
  have : IsIso (U.map β) := by
    have hgg : IsIso g := by
      rw [DerivedCategory.isIso_iff]
      intro q
      let H := DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) Y)) q
      obtain ⟨hc⟩ := integralLocalization_homology_isColimit ℓ E Y (G.obj K) hGK q
      obtain ⟨hd⟩ := integralLocalization_push_homology_isColimit ℓ E f K hK q
      apply integralLocalization_cocone_map_isIso ℓ cY d g hzero H hc
      let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
      let e := Functor.isoWhiskerRight (Functor.isoWhiskerLeft J σ) H
      refine (IsColimit.precomposeHomEquiv e _) ?_
      apply hd.ofIsoColimit
      exact Cocone.ext (Iso.refl _) (by
        intro n
        simp only [Functor.comp_obj, Mod.smulSequenceCompIso, NatIso.ofComponents_hom_app,
          Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
          Cocone.precompose_obj_pt, Functor.mapCocone_pt, Cocone.whisker_pt,
          Functor.mapCocone_ι_app, Functor.comp_map, Iso.refl_hom, Category.comp_id,
          Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.const_obj_obj,
          Functor.whiskerRight_app, Functor.whiskerLeft_app,
          CategoryTheory.Functor.map_id, Cocone.whisker_ι, Functor.whiskerLeft_comp,
          Functor.map_comp, e, σ, d]
        change H.map (G.map (cX.ι.app n.down)) =
          𝟙 _ ≫ H.map (𝟙 _) ≫ H.map (G.map (cX.ι.app n.down))
        rw [H.map_id, Category.id_comp, Category.id_comp])
    exact IsIso.of_isIso_comp_right (U.map β) (κ.hom.app (LX.obj K))
  exact isIso_of_reflects_iso β U

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Transport coefficient data before forming the derived module categories.
private theorem bounded_integralScalarPushHom_isIso_of_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (a : Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})))
    [IsCommMonObj a.left.toMon.X] [IsCommMonObj a.right.toMon.X]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap a.hom.hom.hom Z))]
    (ha : a = Arrow.mk (show CommMon.mk (integralCoeff ℓ E) ⟶
        CommMon.mk (Profinite.continuousMapRingObj E) from
      CommMon.homMk (Mon.Hom.mk (integralScalarMap ℓ E))))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj a.left.X X)))
    (hC : DerivedCategory.TStructure.t.plus C) :
    IsIso ((derivedPushHom a.hom.hom.hom f).app C) := by
  subst a
  exact bounded_integralScalarPushHom_isIso ℓ E f C hC

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 120000 in
-- Identify the equal coefficient data before specializing its derived functors.
-- The ambient derived category retains the full module tensor-resolution structure.
/-- Localization of coefficients commutes with ordinary ambient derived direct image
for every bounded-below complex; completeness, constructibility and finite Tor
amplitude are not required.
Source: HRS Lemmas 5.3(1), 5.6; Bhatt--Scholze Remark 6.8.15
(blueprint: lem-sfb-localized-direct-image-comparison).

Proof:
1. Equip E with the norm induced from the fixed algebraic closure. The continuous
integral coefficient ring and its inclusion into E are definitionally the published
padic coefficient ring and inclusion. Bundle this equality at the coefficient-map
level before constructing the derived module categories.
2. Use the internal scalar extension/restriction adjunctions and the published
restriction/direct-image isomorphism κ. For the specified mate β, the general mate
unit identity gives η ≫ (U β ≫ κ) = Rf_*(η).
3. The right derived direct image preserves a cohomological lower bound, by its
bounded-below compatibility. Form the localization-unit cocone of C, its image under
Rf_*, and the localization-unit cocone of Rf_* C. The scalar sequence comparison
identifies their base diagrams; the mate identity identifies their zeroth legs.
4. The existing integral localization homology and pushforward continuity theorems
make both lifted cocones colimits after each cohomology functor. Multiplication by ℓ
is invertible on their localized vertices, so the localization cocone comparison
criterion proves every cohomology map of U β ≫ κ invertible.
5. Cohomology detects isomorphisms, κ is invertible, and exact scalar restriction
reflects isomorphisms, again by cohomology and its faithful underlying forgetful
functor. Therefore the specified β is invertible. -/
theorem localizedDirectImageComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hC : DerivedCategory.TStructure.t.plus C) :
    IsIso (localizedDirectImageComparison ℓ E f C) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let a := Arrow.mk (show CommMon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.1) ⟶
      CommMon.mk (Profinite.continuousMapRingObj E.1) from
    CommMon.homMk (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ℓ E)))
  have : IsCommMonObj a.left.toMon.X := a.left.comm
  have : IsCommMonObj a.right.toMon.X := a.right.comm
  have : ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap a.hom.hom.hom Z)) :=
    fun Z ↦ (padicIntegers_invertEll Z ℓ E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
  have ha : a = Arrow.mk (show CommMon.mk (integralCoeff ℓ E.1) ⟶
      CommMon.mk (Profinite.continuousMapRingObj E.1) from
    CommMon.homMk (Mon.Hom.mk (integralScalarMap ℓ E.1))) := rfl
  have h := bounded_integralScalarPushHom_isIso_of_eq ℓ E.1 a ha f C hC
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
