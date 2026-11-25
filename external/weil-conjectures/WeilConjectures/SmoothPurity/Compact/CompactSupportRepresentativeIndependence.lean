/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarExtensionLaws
import WeilConjectures.SmoothPurity.Compact.CompactSupportRoosTriangleUniqueness
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportConstructible
import Mathlib.LinearAlgebra.TensorProduct.Tower
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-!
# Compact support and specified rational identifications

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations, order 1494;
main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field, order 1853
(blueprint: lem-weil-compact-support-representative-independence).

The comparison is a single simultaneous family indexed by specified input
isomorphisms, realized by the scalar extension of an integral linear functor with
the prescribed compact-support values. The integral functor is naturally identified
with the coherent strict tower followed by total derived inverse limit; that comparison
preserves the projections of the chosen Roos vertex. Its tensor-Hom formula fixes
the rational extension.
The presentation clause records its cocycle for a common rational
object. It does not assert uniqueness of an isomorphism between bare objects.
-/

@[expose] public section

set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct

namespace WeilConjectures

private noncomputable def rationalExtension
    {R : Type*} [CommRing R] (p : R)
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [Linear R A] [Linear R B] (F : A ⥤ B) [F.Additive] [F.Linear R] :
    ScalarLocalization R A p ⥤ ScalarLocalization R B p where
  obj K := ⟨F.obj K.obj⟩
  map {K L} := (F.mapLinearMap R).baseChange (Localization.Away p)
  map_id K := (compactSupportScalarExtensionLaws p F).1 K.obj
  map_comp {K L M} f g := (compactSupportScalarExtensionLaws p F).2 K.obj L.obj M.obj f g

private noncomputable instance rationalExtension_linear
    {R : Type*} [CommRing R] (p : R)
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [Linear R A] [Linear R B] (F : A ⥤ B) [F.Additive] [F.Linear R] :
    (rationalExtension p F).Linear (Localization.Away p) where
  map_smul {_K _L} f a := ((F.mapLinearMap R).baseChange _).map_smul a f

private noncomputable def canonicalDerivedUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  let π := HomotopyCategory.quotient A (.up ℤ)
  let e := Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
    Functor.associator _ _ _
  e.hom ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) F.rightDerivedFunctor).hom

private theorem canonicalDerivedUnit_isDerived
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.rightDerivedFunctor.IsRightDerivedFunctor (canonicalDerivedUnit F)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
    Functor.associator _ _ _
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    intro I J f hf
    have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
      (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
    have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
      (CochainComplex.KInjectives.toHomotopyCategory.map f)
    have hmap' : IsIso ((π ⋙ H).map f.hom) := hmap
    have heq : (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom =
        e.hom.app I.obj ≫ (π ⋙ H).map f.hom ≫ e.inv.app J.obj := by
      rw [← e.hom.naturality_assoc]
      simp
    change IsIso ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom)
    rw [heq]
    infer_instance
  have hi (I : CochainComplex A ℤ) [I.IsKInjective] :
      IsIso ((canonicalDerivedUnit F).app I) := by
    dsimp [canonicalDerivedUnit]
    infer_instance
  exact h.isRightDerivedFunctor_of_isIso (canonicalDerivedUnit F) (fun I ↦ by
    have := I.property
    exact hi I.obj)

private theorem canonicalDerivedUnit_objIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    (canonicalDerivedUnit F).app I ≫ (F.rightDerivedFunctorObjQIso I).hom = 𝟙 _ := by
  dsimp only [canonicalDerivedUnit, Functor.rightDerivedFunctorObjQIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, asIso_inv, Iso.app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app]
  have hi : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I = 𝟙 _ := rfl
  simp [Functor.whiskerRight_app, hi]

private theorem constantScalar_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (U : W.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    compactSupportConstantScalar l E W U a = integralScalarConstant l E W U a := by
  apply (integralScalarConstant_existsUnique l E W U a).unique
    (y₂ := integralScalarConstant l E W U a)
    ?_ (integralScalarConstant_existsUnique l E W U a).exists.choose_spec
  intro n
  have hp := congrArg (fun v ↦ (v.hom.app U).hom
      (((toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u}
            (Padic.coefficientExtensionIntegers l E))))).app U) (ULift.up a)))
    (limit.lift_π (integralConstantCoefficientCone l E W) (op n))
  change ((limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U)
    (compactSupportConstantScalar l E W U a) = _ at hp
  rw [hp]
  let q : CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).ulift
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map q)) U) (ULift.up a)).symm

private theorem normalizedDerivedLinear
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (s : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E W))
    (hs : @IsCompactSupportScalarAction l _ E _ _ _ W s) :
    (letI := s
     DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
       (scalarReductionSource l E W)) = sfIntegralCoefficientLinear l E W := by
  let := s
  let := DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
    (scalarReductionSource l E W)
  apply (integralCoefficientLinear_existsUnique l E W).unique ?_
    (integralCoefficientLinear_existsUnique l E W).exists.choose_spec
  intro a K L f
  let τ : 𝟭 (DerivedCategory (scalarReductionSource l E W)) ⟶ 𝟭 _ :=
    { app := fun K ↦ a • 𝟙 K
      naturality := by intros; simp }
  have ht : τ = integralScalarDerivedAction l E W a := by
    apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
      (DerivedCategory (scalarReductionSource l E W))).map_injective
    apply NatTrans.ext
    funext P
    change a • 𝟙 (DerivedCategory.Q.obj P) =
      (integralScalarDerivedAction l E W a).app (DerivedCategory.Q.obj P)
    rw [integralScalarDerivedAction_app_Q, ← DerivedCategory.Q.map_id,
      ← DerivedCategory.Q.map_smul]
    congr 1
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a • 𝟙 (P.X i)).val.app U x = _
    rw [hs]
    change compactSupportConstantScalar l E W U a • x = _
    rw [constantScalar_eq]
    exact ((integralScalarChainAction_existsUnique l E W a).exists.choose_spec P i U x).symm
  change a • f = _
  rw [← ht]
  change a • f = (a • 𝟙 K) ≫ f
  simp

private theorem linearOfFaithful
    {R : Type*} [Semiring R]
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Linear R A] [Linear R B] [Linear R C]
    (F : A ⥤ B) (G : B ⥤ C) [G.Faithful] [G.Linear R] [(F ⋙ G).Linear R] :
    F.Linear R where
  map_smul v a := G.map_injective (by
    rw [G.map_smul, ← Functor.comp_map, (F ⋙ G).map_smul]
    rfl)

private theorem derivedLimitIso
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    {K : ℕ → D} [HasProduct K] (t : ∀ n, K (n + 1) ⟶ K n)
    {L L' : D} (p : L ⟶ ∏ᶜ K) (q : L' ⟶ ∏ᶜ K)
    (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧) (δ' : ∏ᶜ K ⟶ L'⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle t L p δ) (hq : IsDerivedLimitTriangle t L' q δ') :
    ∃ e : L ≅ L', e.hom ≫ q = p := by
  exact compactSupportRoosTriangleUniqueness t p q δ δ' hp hq

private theorem productProjection
    {D : Type*} [Category D] [HasCountableProducts D]
    {K K' : ℕ → D} {L : D} (p : ∀ n, L ⟶ K n) (e : ∀ n, K n ≅ K' n) (n : ℕ) :
    (Pi.lift p ≫ (Pi.mapIso e).hom) ≫ Pi.π K' n = p n ≫ (e n).hom := by
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]

private theorem transportLimitTriangle
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {K K' : ℕ → D} [HasCountableProducts D]
    (t : ∀ n, K (n + 1) ⟶ K n) (t' : ∀ n, K' (n + 1) ⟶ K' n)
    (e : ∀ n, K n ≅ K' n)
    (he : ∀ n, (e (n + 1)).hom ≫ t' n = t n ≫ (e n).hom)
    {L : D} (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle t L p δ) :
    ∃ δ', IsDerivedLimitTriangle t' L (p ≫ (Pi.mapIso e).hom) δ' := by
  let E := Pi.mapIso e
  refine ⟨E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism t) δ)
      (Pretriangulated.Triangle.mk (p ≫ E.hom)
        (towerTransitionEndomorphism t') (E.inv ≫ δ))
      (Iso.refl _) E E (by simp)
      (towerTransitionEndomorphism_natural_backward t t' (fun n ↦ (e n).hom) he).symm
      (by simp))).mp h

private theorem compactSupportSuccessorTransition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    compactSupportRestrictedTransition l E c (n + 1) n n.le_succ K =
      sfCompactSupportTransition l E c K n := by
  rfl

private theorem compactSupportAB4Star
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    CountableAB4Star (scalarReductionSource l E W) := by
  let A := scalarReductionSource l E W
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (Scheme.ProEt.countableProducts_exact.{u, u, 0} W
          (completedIntegralCommRingSheafUnrestricted l E W)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat A

private theorem normalizedLimitTriangle
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A] [CountableAB4Star A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] [EnoughInjectives A]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    [HasCountableProducts (DerivedCategory A)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ))]
    (π : ∀ n : ℕ, RF ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory)
    (hπ : ∀ n (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
          (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors).hom.app I =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I))
    (Z : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    ∃ δ, IsDerivedLimitTriangle (fun n ↦ (trD A n).app Z) (RF.obj Z)
      (Pi.lift (fun n : ℕ ↦ (π n).app Z)) δ := by
  let U := (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  have := canonicalDerivedUnit_isDerived U
  let ρ := Functor.rightDerivedUnique RF U.rightDerivedFunctor η
    (canonicalDerivedUnit U) (HomologicalComplex.quasiIso _ (.up ℤ))
  let π₀ (n : ℕ) := ρ.inv ≫ π n
  have hρ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      (canonicalDerivedUnit U).app I ≫ ρ.inv.app (DerivedCategory.Q.obj I) = η.app I := by
    simp [ρ, Functor.rightDerivedNatIso, Functor.rightDerivedNatTrans]
  have hp₀ (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      (π₀ n).app (DerivedCategory.Q.obj I) ≫ (evF A n).hom.app I =
        (U.rightDerivedFunctorObjQIso I).hom ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
    have : IsIso ((canonicalDerivedUnit U).app I) := by
      dsimp [canonicalDerivedUnit]; infer_instance
    apply (cancel_epi ((canonicalDerivedUnit U).app I)).mp
    rw [← Category.assoc, ← Category.assoc, canonicalDerivedUnit_objIso, Category.id_comp]
    change ((canonicalDerivedUnit U).app I ≫
      (ρ.inv.app _ ≫ (π n).app _)) ≫ _ = _
    rw [← Category.assoc, hρ]
    simpa only [Category.assoc] using hπ n I
  obtain ⟨δ, hδ⟩ := derivedLimitTriangle A inferInstance π₀ hp₀ Z
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map (ρ.inv.app Z), ?_⟩
  change Pretriangulated.Triangle.mk _ _ _ ∈ _
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (Pi.lift (fun n : ℕ ↦ (π₀ n).app Z))
        (towerTransitionEndomorphism (fun n ↦ (trD A n).app Z)) δ)
      (Pretriangulated.Triangle.mk (Pi.lift (fun n : ℕ ↦ (π n).app Z))
        (towerTransitionEndomorphism (fun n ↦ (trD A n).app Z)) _)
      (ρ.app Z).symm (Iso.refl _) (Iso.refl _)
      (by
        change Pi.lift (fun n : ℕ ↦ (π₀ n).app Z) ≫ 𝟙 _ =
          ρ.inv.app Z ≫ Pi.lift (fun n : ℕ ↦ (π n).app Z)
        simp only [Category.comp_id]
        apply Pi.hom_ext
        intro n
        simp [π₀])
      (by simp) (by simp))).mp hδ

attribute [local irreducible] compactSupportRestrictedTransition sfCompactSupportTransition

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- The coherence proof unfolds the restricted transitions at every finite level.
/-- Specified rational identifications induce coherent compact-support comparisons.
The compactification c is fixed at every finite coefficient level, exactly as in
sfIntegralCompactSupportValue. The index of each reduction is the positive exponent n+1.
Source: Weil blueprint, order 1494, and main-20261015, order 1853
(blueprint: lem-weil-compact-support-representative-independence).

Proof (the five steps of the DAG):
1. Use the supplied compactification c and the exact choices of the coherent tower
T, its evaluation comparisons e, and the total right derived limit RF with unit η.
Descend the ordinary limit projections through the universal property of RF. This
normalizes the resulting projections on every complex. Compare RF with the standard
right derived inverse limit and apply the proved canonical Roos-triangle construction.
2. Identify the tower theorem's scalar action with the published integral action by
its constant finite residues, then by localization and uniqueness of the derived
scalar action. Ordinary inverse limit is linear by its projections. The existing
K-injective right-derived-linearity proof applies to its standard derived functor;
uniqueness transfers linearity and additivity to the prescribed RF.
3. The tower's successor transitions are exactly sfCompactSupportTransition. Transport
its normalized Roos triangle by e. Rotate this triangle and the chosen triangle in
sfIntegralCompactSupportValue; an isomorphism extending the identity on the common
transition arrow gives an isomorphism of vertices preserving projections. Conjugate
maps of T followed by RF by these vertex isomorphisms to obtain F with exactly the
prescribed objects. Cancellation proves functoriality, and bilinearity proves
additivity and linearity. Constructibility is already part of those object values.
4. Extend this integral functor on the raw tensor Hom groups of
 def-weil-rationalization-karoubi and def-weil-linear-scalar-localization by
 u tensor e mapping to F(u) tensor e. The tensor balancing of
 def-weil-module-base-change follows from integral linearity. Functoriality follows
 on pure tensors from F(vu)=F(v)F(u) and F(1)=1, then on sums by bilinearity.
 Any linear extension has that pure-tensor formula, so the extension is unique
 for the fixed integral functor. Its object values are sfRationalCompactSupportValue.
5. Take beta(alpha) to be the image of alpha, with inverse the image of its inverse.
 The functor laws give the identity and composition clauses. For presentations
 a and a' of M the input is a followed by the inverse of a', hence the comparison
 is beta(a followed by inverse a'). Cancelling the middle presentation gives the
 final cocycle. No choice-independent comparison of bare isomorphism classes is used. -/
theorem exists_compactSupportRepresentativeComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (X Y : Scheme.{u})
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (fun [hproducts : HasCountableProducts
        (DerivedCategory (scalarReductionSource l E Y))] ↦
    ∃ (T : DerivedCategory (scalarReductionSource l E X) ⥤
        DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)))
      (e : ∀ n : ℕ,
        T ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
          compactSupportRestrictedLevel l E c n),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
            (exists_compactSupportReductionTower l E K₀ X Y f hl c))).2.2 ∧
      HEq e (Classical.choose (Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (exists_compactSupportReductionTower l E K₀ X Y f hl c))).2.2).2).2) ∧
      ∃ (RF : DerivedCategory
          (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ⥤
            DerivedCategory (scalarReductionSource l E Y))
        (η : (lim : pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y) ⥤
            scalarReductionSource l E Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF),
        RF = Classical.choose
          (@ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
            Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
            ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
            (fun U a b ↦ @mul_comm
              ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
            (scalarReductionSourceDerived l E Y)
            (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))) ∧
        HEq η (Classical.choose (Classical.choose_spec
          (@ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
            Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
            ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
            (fun U a b ↦ @mul_comm
              ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
            (scalarReductionSourceDerived l E Y)
            (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))))) ∧
        ∃ π : ∀ n : ℕ,
            RF ⟶ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n,
          (∀ (n : ℕ)
            (I : CochainComplex
              (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ℤ),
            η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
                (Functor.mapDerivedCategoryFactors
                  ((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))).hom.app I =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)) ∧
          ∃ F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y,
      F.Additive ∧ F.Linear (Padic.coefficientExtensionIntegers l E) ∧
      (∀ K : sfIntegralConstructibleCategory l E X,
        F.obj K = sfIntegralCompactSupportValue l E K₀ hl c K) ∧
      (∃ γ : F ⋙ (sfIntegralConstructible l E Y).ι ≅
          (sfIntegralConstructible l E X).ι ⋙ T ⋙ RF,
        ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
          HEq (γ.hom.app K ≫ (π n).app (T.obj K.obj) ≫ (e n).hom.app K.obj)
            (Classical.choose (Classical.choose_spec
                (exists_isDerivedLimit_and_iso
                  (sfCompactSupportTerm l E c K.obj)
                  (sfCompactSupportTransition l E c K.obj)).1) ≫
              Pi.π (sfCompactSupportTerm l E c K.obj) n)) ∧
      ∃ G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y,
        G.Linear (Localization.Away (Padic.coefficientExtensionUniformizer l E)) ∧
        (∀ K : sfIntegralConstructibleCategory l E X,
          G.obj ((sfRationalConstructibleLocalization l E X).obj K) =
            sfRationalCompactSupportValue l E K₀ hl c K) ∧
        (∀ (K K' : sfIntegralConstructibleCategory l E X) (v : K ⟶ K')
          (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (G.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] v :
            (sfRationalConstructibleLocalization l E X).obj K ⟶
              (sfRationalConstructibleLocalization l E X).obj K'))
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map v :
              (sfRationalConstructibleLocalization l E Y).obj (F.obj K) ⟶
                (sfRationalConstructibleLocalization l E Y).obj (F.obj K'))) ∧
        ∃ beta : ∀ (K K' : sfIntegralConstructibleCategory l E X),
        ((sfRationalConstructibleLocalization l E X).obj K ≅
          (sfRationalConstructibleLocalization l E X).obj K') →
        (sfRationalCompactSupportValue l E K₀ hl c K ≅
          sfRationalCompactSupportValue l E K₀ hl c K'),
      (∀ (K K' : sfIntegralConstructibleCategory l E X)
        (alpha : (sfRationalConstructibleLocalization l E X).obj K ≅
          (sfRationalConstructibleLocalization l E X).obj K'),
        HEq (beta K K' alpha) (G.mapIso alpha)) ∧
      (∀ K : sfIntegralConstructibleCategory l E X,
        beta K K (Iso.refl _) = Iso.refl _) ∧
      (∀ (K K' K'' : sfIntegralConstructibleCategory l E X)
        (alpha : (sfRationalConstructibleLocalization l E X).obj K ≅
          (sfRationalConstructibleLocalization l E X).obj K')
        (alpha' : (sfRationalConstructibleLocalization l E X).obj K' ≅
          (sfRationalConstructibleLocalization l E X).obj K''),
        beta K K'' (alpha ≪≫ alpha') = beta K K' alpha ≪≫ beta K' K'' alpha') ∧
      (∀ (M : sfRationalConstructibleCategory l E X)
        (K K' K'' : sfIntegralConstructibleCategory l E X)
        (a : (sfRationalConstructibleLocalization l E X).obj K ≅ M)
        (a' : (sfRationalConstructibleLocalization l E X).obj K' ≅ M)
        (a'' : (sfRationalConstructibleLocalization l E X).obj K'' ≅ M),
        beta K K' (a ≪≫ a'.symm) ≪≫ beta K' K'' (a' ≪≫ a''.symm) =
          beta K K'' (a ≪≫ a''.symm)))
      (hproducts := integralOperationsDerivedCountableProducts l E Y) := by
  classical
  have hT := exists_compactSupportReductionTower l E K₀ X Y f hl c
  let T : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) :=
    hT.choose_spec.choose_spec.2.2.choose
  let e : ∀ n : ℕ,
      T ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
        compactSupportRestrictedLevel l E c n :=
    hT.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.2.choose
  let ek (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
      (pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n).obj
          (T.obj K) ≅ sfCompactSupportTerm l E c K n := (e n).app K
  have hR := @ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
    Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
    ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
    (fun U a b ↦ @mul_comm
      ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
    (scalarReductionSourceDerived l E Y)
    (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))
  let RF : DerivedCategory
      (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ⥤
        DerivedCategory (scalarReductionSource l E Y) := hR.choose
  let η : (lim : pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y) ⥤
      scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF := hR.choose_spec.choose
  have hRF := hR.choose_spec.choose_spec.1
  let := hRF
  let π (n : ℕ) : RF ⟶
      pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n :=
    RF.rightDerivedDesc η (HomologicalComplex.quasiIso _ (.up ℤ)) _
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ))
        DerivedCategory.Q ≫
          (Functor.mapDerivedCategoryFactors
            ((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))).inv)
  have hπ : ∀ (n : ℕ)
      (I : CochainComplex
        (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ℤ),
      η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
          (Functor.mapDerivedCategoryFactors
            ((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))).hom.app I =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
    intro n I
    have h := RF.rightDerived_fac_app η
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n)
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ))
        DerivedCategory.Q ≫
          (Functor.mapDerivedCategoryFactors
            ((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n))).inv) I
    change η.app I ≫ (π n).app (DerivedCategory.Q.obj I) = _ at h
    rw [← Category.assoc, h]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  have hTa : T.Additive := by
    let : T.CommShift ℤ := hT.choose_spec.choose_spec.2.2.choose_spec.2.choose
    have : T.IsTriangulated :=
      hT.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.1
    infer_instance
  let := hTa
  have hRa : RF.Additive := by
    let U := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y)
    have := canonicalDerivedUnit_isDerived U
    exact Functor.additive_of_iso (Functor.rightDerivedUnique RF U.rightDerivedFunctor η
      (canonicalDerivedUnit U) (HomologicalComplex.quasiIso _ (.up ℤ))).symm
  let := hRa
  have hH : (T ⋙ RF).Linear (Padic.coefficientExtensionIntegers l E) := by
    let sX := hT.choose
    let sY := hT.choose_spec.choose
    let := sX
    let := sY
    let := DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
      (scalarReductionSource l E X)
    let := DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
      (scalarReductionSource l E Y)
    let := DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
      (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y))
    have : T.Linear (Padic.coefficientExtensionIntegers l E) :=
      hT.choose_spec.choose_spec.2.2.choose_spec.1
    let U := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y)
    have : U.Linear (Padic.coefficientExtensionIntegers l E) := by
      constructor
      intro M N v a
      apply limit.hom_ext
      intro n
      simp only [U, lim_map, limMap_π, Linear.smul_comp]
      change _ ≫ (a • v.app n) = _
      simp only [Linear.comp_smul]
    have := compactSupportRightDerivedLinear (Padic.coefficientExtensionIntegers l E) U
    have := canonicalDerivedUnit_isDerived U
    have : RF.Linear (Padic.coefficientExtensionIntegers l E) :=
      Functor.linear_of_iso _ (Functor.rightDerivedUnique RF U.rightDerivedFunctor η
        (canonicalDerivedUnit U) (HomologicalComplex.quasiIso _ (.up ℤ))).symm
    have hh : (T ⋙ RF).Linear (Padic.coefficientExtensionIntegers l E) := inferInstance
    change @Functor.Linear (Padic.coefficientExtensionIntegers l E) _ _ _ _ _ _ _
      (DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
        (scalarReductionSource l E X))
      (DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
        (scalarReductionSource l E Y)) (T ⋙ RF) at hh
    rw [normalizedDerivedLinear l E X sX hT.choose_spec.choose_spec.1,
      normalizedDerivedLinear l E Y sY hT.choose_spec.choose_spec.2.1] at hh
    exact hh
  let := hH
  let : HasCountableProducts (DerivedCategory (scalarReductionSource l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  let := compactSupportAB4Star l E Y
  let : IsGrothendieckAbelian.{u+1} (scalarReductionSource l E Y) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  have hlim (K : DerivedCategory (scalarReductionSource l E X)) :
      ∃ δ, IsDerivedLimitTriangle (sfCompactSupportTransition l E c K)
        (RF.obj (T.obj K))
        ((Pi.lift (fun n : ℕ ↦ (π n).app (T.obj K))) ≫
          (Pi.mapIso (ek K)).hom) δ := by
    obtain ⟨δ, hδ⟩ := normalizedLimitTriangle (A := scalarReductionSource l E Y) RF η π hπ (T.obj K)
    apply transportLimitTriangle (fun n ↦ (trD (scalarReductionSource l E Y) n).app (T.obj K))
      (sfCompactSupportTransition l E c K)
      (ek K) _ _ δ hδ
    intro n
    have he :
        (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
          (n + 1) n n.le_succ).app (T.obj K) ≫ (e n).hom.app K =
        (e (n + 1)).hom.app K ≫
          compactSupportRestrictedTransition l E c (n + 1) n n.le_succ K :=
      hT.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.2.choose_spec.1
        (n + 1) n n.le_succ K
    change (e (n + 1)).hom.app K ≫ sfCompactSupportTransition l E c K n =
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
        (n + 1) n n.le_succ).app (T.obj K) ≫ (e n).hom.app K
    exact (congrArg (fun v ↦ (e (n + 1)).hom.app K ≫ v)
      (compactSupportSuccessorTransition l E c K n)).symm.trans he.symm
  have hi (K : sfIntegralConstructibleCategory l E X) :
      ∃ i : (sfIntegralCompactSupportValue l E K₀ hl c K).obj ≅ RF.obj (T.obj K.obj),
        ∀ n, i.hom ≫ (π n).app (T.obj K.obj) ≫ (e n).hom.app K.obj =
          Classical.choose (Classical.choose_spec
            (exists_isDerivedLimit_and_iso (sfCompactSupportTerm l E c K.obj)
              (sfCompactSupportTransition l E c K.obj)).1) ≫
                Pi.π (sfCompactSupportTerm l E c K.obj) n := by
    let M : DerivedCategory (scalarReductionSource l E Y) :=
      (sfIntegralCompactSupportValue l E K₀ hl c K).obj
    have hm : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) M :=
      Classical.choose_spec
        (exists_isDerivedLimit_and_iso (sfCompactSupportTerm l E c K.obj)
          (sfCompactSupportTransition l E c K.obj)).1
    let p : M ⟶ ∏ᶜ (sfCompactSupportTerm l E c K.obj) := hm.choose
    let δ : ∏ᶜ (sfCompactSupportTerm l E c K.obj) ⟶ M⟦(1 : ℤ)⟧ :=
      hm.choose_spec.choose
    have hp : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K.obj) M p δ :=
      hm.choose_spec.choose_spec
    obtain ⟨δ', hδ'⟩ := hlim K.obj
    obtain ⟨i, hi⟩ := derivedLimitIso (L := M) (L' := RF.obj (T.obj K.obj))
      (sfCompactSupportTransition l E c K.obj) p _ δ δ' hp hδ'
    refine ⟨i, fun n ↦ ?_⟩
    have hh := congrArg (fun v ↦ v ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n) hi
    have hq := productProjection (fun n : ℕ ↦ (π n).app (T.obj K.obj)) (ek K.obj) n
    have hq' := congrArg (fun v ↦ i.hom ≫ v) hq
    exact hq'.symm.trans ((Category.assoc _ _ _).symm.trans hh)
  let i : ∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralCompactSupportValue l E K₀ hl c K).obj ≅ RF.obj (T.obj K.obj) :=
    fun K ↦ (hi K).choose
  let F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
    { obj := sfIntegralCompactSupportValue l E K₀ hl c
      map := fun {K L} v ↦ ⟨(i K).hom ≫ (T ⋙ RF).map v.hom ≫ (i L).inv⟩
      map_id := by intro K; ext; simp
      map_comp := by intro K L M v w; ext; simp }
  let γ : F ⋙ (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ T ⋙ RF :=
    NatIso.ofComponents i (by intro K L v; dsimp [F]; simp)
  have hFa : F.Additive := by
    have : (F ⋙ (sfIntegralConstructible l E Y).ι).Additive :=
      Functor.additive_of_iso γ.symm
    exact Functor.additive_of_comp_faithful F (sfIntegralConstructible l E Y).ι
  let := hFa
  have hFl : F.Linear (Padic.coefficientExtensionIntegers l E) := by
    have : ((sfIntegralConstructible l E X).ι ⋙ (T ⋙ RF)).Linear
        (Padic.coefficientExtensionIntegers l E) := inferInstance
    have : (F ⋙ (sfIntegralConstructible l E Y).ι).Linear
        (Padic.coefficientExtensionIntegers l E) :=
      Functor.linear_of_iso (Padic.coefficientExtensionIntegers l E) γ.symm
    exact linearOfFaithful (R := Padic.coefficientExtensionIntegers l E)
      F (sfIntegralConstructible l E Y).ι
  let := hFl
  let G := rationalExtension (Padic.coefficientExtensionUniformizer l E) F
  refine ⟨T, e, rfl, HEq.rfl, RF, η, rfl, HEq.rfl, π, hπ,
    F, hFa, hFl, fun K ↦ rfl, ⟨γ, ?_⟩, G, inferInstance,
    fun K ↦ rfl, ?_, fun K K' α ↦ G.mapIso α, fun K K' α ↦ HEq.rfl, ?_, ?_, ?_⟩
  · intro K n
    exact heq_of_eq ((hi K).choose_spec n)
  · intro K L v a
    apply heq_of_eq
    exact LinearMap.baseChange_tmul _ _ _
  · intro K
    exact G.mapIso_refl _
  · intro K L M α β
    exact G.mapIso_trans α β
  · intro M K L N a b c
    change G.mapIso (a ≪≫ b.symm) ≪≫ G.mapIso (b ≪≫ c.symm) =
      G.mapIso (a ≪≫ c.symm)
    exact (G.mapIso_trans (a ≪≫ b.symm) (b ≪≫ c.symm)).symm.trans
      (congrArg G.mapIso (by simp))

end WeilConjectures
