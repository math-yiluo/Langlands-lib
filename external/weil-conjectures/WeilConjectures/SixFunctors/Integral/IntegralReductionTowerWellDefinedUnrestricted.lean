/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerWellDefinedUnrestricted

/-! # Canonical resolution comparisons without an auxiliary finite-field datum

Source: Stacks Project, sites-cohomology.tex, Tags 06YS/06YT/06YY; derived.tex,
Tags 05RT/06XN; Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

This is the unrestricted interface to the same augmented reduction tower.
It uses the published completed sheaf and scalarReductionExtension, its universal
derived counit, and the canonical localization factorization. Index n means
exponent n+1. The site and coefficient universes remain independent.

## Main definitions and statements

- `unrestrictedTowerResolutionIso`: computation through the universal derived counit.
- `unrestrictedTowerFiniteComparison`: canonical comparison of two resolutions.
- `unrestrictedTowerUnit`: the uniquely normalized unit chain map.
- `unrestrictedTowerTransition`: the published canonical transition at P.
- `unrestrictedReductionTowerWellDefined`: invariance of the augmented derived tower.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})







/-- A pure tensor, followed by sheafification, in the recorded finite reduction.
Transport uses the object equality in the defining change-of-rings witness.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerTensorSection (n : ℕ)
    (M : scalarReductionSource l E Y)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((scalarReductionExtension l E Y n).obj M).val.obj U :=
  unrestrictedIntegralTensorSection l E Y n M U s x

/-- The universal derived counit computes scalar reduction on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined).
Proof: specialize the K-flat computation conjunct of the universal
change-of-rings witness defining scalarReductionDerivedExistence to P and hP.
The selected functor and counit are precisely its projections. -/
theorem unrestrictedTowerCounit_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P) :
    IsIso ((scalarReductionCounit l E Y n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  simpa only [scalarReductionCounit] using
    ((scalarReductionDerivedExistence l E Y n).choose_spec.choose_spec.2.2 P hP)

/-- The canonical computation by a resolution, expressed using complexes rather than
homotopy representatives. Both transports are the standard quotient comparison.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerResolutionIso (n : ℕ)
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) :
    (scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P) :=
  letI : QuasiIso q := hq.1
  (scalarReductionDerivedExtension l E Y n).mapIso (asIso (DerivedCategory.Q.map q)).symm ≪≫
    (scalarReductionDerivedExtension l E Y n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    @asIso _ _ _ _ ((scalarReductionCounit l E Y n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
      (unrestrictedTowerCounit_isIso l E Y n P hq.2) ≪≫
    DerivedCategory.Qh.mapIso
      (((scalarReductionExtension l E Y n).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E Y n)).app
      (unrestrictedTowerFiniteComplex l E Y n P)

/-- The finite comparison is defined through the common derived reduction of K.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerFiniteComparison (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q') :
    DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
      DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P') :=
  (unrestrictedTowerResolutionIso l E Y n q hq).symm ≪≫
    unrestrictedTowerResolutionIso l E Y n q' hq'

/-- Restrict the canonical finite comparison, using the canonical localization
factorization to express its endpoints by the restricted complexes.
Source: Stacks Tags 03DA/06YY
(blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerComparison (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q') :
    DerivedCategory.Q.obj (unrestrictedTowerComplex l E Y n P) ≅
      DerivedCategory.Q.obj (unrestrictedTowerComplex l E Y n P') :=
  ((scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.app _).symm ≪≫
    (scalarReductionRestriction l E Y n).mapDerivedCategory.mapIso
      (unrestrictedTowerFiniteComparison l E Y n q q' hq hq') ≪≫
    (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.app _

/-- The unit maps are specified on local sections by x ↦ 1 ⊗ x and sheafification.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
def unrestrictedTowerUnitCondition
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (γ : ∀ n : ℕ, P ⟶ unrestrictedTowerComplex l E Y n P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : (P.X i).val.obj U),
    ((γ n).f i).val.app U x = unrestrictedTowerTensorSection l E Y n (P.X i) U 1 x


/-- The constructed unit has the prescribed sectionwise pure-tensor formula.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined).
Proof: the unit of the scalar-extension adjunction sends x to 1 tensor x;
the chain map is defined degreewise by exactly that unit. -/
theorem unrestrictedTowerUnit_condition
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    unrestrictedTowerUnitCondition l E Y P (unrestrictedTowerUnit l E Y P) := by
  intro n i U x
  change ((scalarReductionExtension_adjunction l E Y n).choose.unit.app
    (P.X i)).val.app U x = _
  rw [(scalarReductionExtension_adjunction l E Y n).choose_spec]
  rfl

/-- The chain-level reduction id⊗ρ: the published canonical transition of
def-weil-integral-reduction-tower, uniquely determined on sheafified pure tensors
(`unrestrictedIntegralTransition_existsUnique`), evaluated at P.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerTransition
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    unrestrictedTowerComplex l E Y (n + 1) P ⟶ unrestrictedTowerComplex l E Y n P :=
  (unrestrictedIntegralTransition l E Y n).app P

/-- The image of the resolution augmentation is invertible in the derived category.
Source: Stacks Tag 06YS (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerAugmentationIso
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) :
    DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
  letI : QuasiIso q := hq.1
  asIso (DerivedCategory.Q.map q)

private noncomputable def towerCounit (n : ℕ) :
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension l E Y n ⟶
      (scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) (scalarReductionCounit l E Y n) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight
      ((scalarReductionExtension l E Y n).mapHomotopyCategoryFactors (.up ℤ)) _).hom ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)).hom

private theorem towerCounit_app (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    (towerCounit l E Y n).app P =
      (scalarReductionDerivedExtension l E Y n).map
        ((DerivedCategory.quotientCompQhIso _).app P).inv ≫
      (scalarReductionCounit l E Y n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        (((scalarReductionExtension l E Y n).mapHomotopyCategoryFactors (.up ℤ)).app P).hom ≫
      ((DerivedCategory.quotientCompQhIso _).app
        (unrestrictedTowerFiniteComplex l E Y n P)).hom := by
  simp [towerCounit]

attribute [local irreducible] towerCounit

private theorem towerCounit_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P) :
    IsIso ((towerCounit l E Y n).app P) := by
  let := unrestrictedTowerCounit_isIso l E Y n P hP
  rw [towerCounit_app]
  infer_instance

private theorem towerResolution_hom (n : ℕ)
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ} (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) :
    (scalarReductionDerivedExtension l E Y n).map (DerivedCategory.Q.map q) ≫
      (unrestrictedTowerResolutionIso l E Y n q hq).hom =
        (towerCounit l E Y n).app P := by
  let : QuasiIso q := hq.1
  rw [towerCounit_app]
  simp [unrestrictedTowerResolutionIso]

attribute [local irreducible] unrestrictedTowerResolutionIso

private theorem towerFinite_roof (n : ℕ)
    {T P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (a : T ⟶ P) (b : T ⟶ P') (q : P ⟶ K) (q' : P' ⟶ K)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) T)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q')
    (h : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q =
      DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q') :
    DerivedCategory.Q.map
        (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).map a) ≫
      (unrestrictedTowerFiniteComparison l E Y n q q' hq hq').hom =
    DerivedCategory.Q.map
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).map b) := by
  let := towerCounit_isIso l E Y n T hT
  apply (cancel_epi ((towerCounit l E Y n).app T)).1
  change _ ≫ (_ ≫ _) = _
  have ha := (towerCounit l E Y n).naturality a
  change _ = _ ≫ DerivedCategory.Q.map _ at ha
  rw [← Category.assoc, ← ha]
  rw [← towerResolution_hom l E Y n q hq]
  simp only [unrestrictedTowerFiniteComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc, towerResolution_hom]
  exact (towerCounit l E Y n).naturality b

attribute [local irreducible] unrestrictedTowerFiniteComparison

private noncomputable abbrev towerFunctor (n : ℕ) :=
  (scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ) ⋙
    (scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)

attribute [local irreducible] unrestrictedTowerUnit

private theorem towerUnit_naturality (n : ℕ)
    {P P' : CochainComplex (scalarReductionSource l E Y) ℤ} (a : P ⟶ P') :
    a ≫ unrestrictedTowerUnit l E Y P' n =
      unrestrictedTowerUnit l E Y P n ≫ (towerFunctor l E Y n).map a := by
  unfold unrestrictedTowerUnit
  ext i : 1
  change a.f i ≫ (scalarReductionExtension_adjunction l E Y n).choose.unit.app (P'.X i) =
    (scalarReductionExtension_adjunction l E Y n).choose.unit.app (P.X i) ≫
      (scalarReductionRestriction l E Y n).map
        ((scalarReductionExtension l E Y n).map (a.f i))
  simpa only [Functor.comp_map, Functor.id_map] using
    (scalarReductionExtension_adjunction l E Y n).choose.unit.naturality (a.f i)

private theorem towerRoof
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K) (hq : QuasiIso q) (hq' : QuasiIso q') :
    ∃ (T : CochainComplex (scalarReductionSource l E Y) ℤ)
      (a : T ⟶ P) (b : T ⟶ P'),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E Y) T ∧
      QuasiIso a ∧ QuasiIso b ∧
        DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q =
          DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q' := by
  let : QuasiIso q := hq
  let : QuasiIso q' := hq'
  let H := HomotopyCategory.quotient (scalarReductionSource l E Y) (.up ℤ)
  let W := HomotopyCategory.quasiIso (scalarReductionSource l E Y) (.up ℤ)
  let : W.HasRightCalculusOfFractions :=
    (HomotopyCategory.quasiIso_saturated_triangulated (scalarReductionSource l E Y)).2.1
  obtain ⟨z, hz⟩ :=
    (MorphismProperty.LeftFraction.mk (H.map q) (H.map q')
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff q').2 hq')).exists_rightFraction
  obtain ⟨V, hV⟩ := HomotopyCategory.quotient_obj_surjective z.X'
  obtain ⟨a₀, ha₀⟩ := H.map_surjective (eqToHom hV ≫ z.s)
  obtain ⟨b₀, hb₀⟩ := H.map_surjective (eqToHom hV ≫ z.f)
  have ha₀q : QuasiIso a₀ :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff a₀).1 (by
      rw [ha₀]
      exact W.comp_mem _ _ (MorphismProperty.of_isIso W _) z.hs)
  have hab : H.map (a₀ ≫ q) = H.map (b₀ ≫ q') := by
    simpa only [Functor.map_comp, ha₀, hb₀, Category.assoc] using
      congrArg (fun f ↦ eqToHom hV ≫ f) hz
  have hb₀q : QuasiIso b₀ := by
    have := ha₀q
    have : QuasiIso (a₀ ≫ q) := inferInstance
    have : QuasiIso (b₀ ≫ q') :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
        (hab ▸ (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 this)
    exact quasiIso_of_comp_right b₀ q'
  have := ha₀q
  have := hb₀q
  obtain ⟨T, r, hT, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) V
  have := hr
  refine ⟨T, r ≫ a₀, r ≫ b₀, hT, inferInstance, inferInstance, ?_⟩
  have heq : H.map ((r ≫ a₀) ≫ q) = H.map ((r ≫ b₀) ≫ q') := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg (H.map r ≫ ·) hab
  have hh := congrArg (DerivedCategory.Qh.map) heq
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app T)).1
  simpa only [← Functor.map_comp, ← DerivedCategory.quotientCompQhIso_hom_naturality] using
    congrArg (· ≫ (DerivedCategory.quotientCompQhIso _).hom.app K) hh

private theorem towerComparison_roof (n : ℕ)
    {T P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (a : T ⟶ P) (b : T ⟶ P') (q : P ⟶ K) (q' : P' ⟶ K)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) T)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q')
    (h : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q =
      DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q') :
    DerivedCategory.Q.map ((towerFunctor l E Y n).map a) ≫
      (unrestrictedTowerComparison l E Y n q q' hq hq').hom =
    DerivedCategory.Q.map ((towerFunctor l E Y n).map b) := by
  let F := scalarReductionExtension l E Y n
  let R := scalarReductionRestriction l E Y n
  let e := R.mapDerivedCategoryFactors
  apply (cancel_epi (e.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj T))).1
  have ha := e.hom.naturality ((F.mapHomologicalComplex (.up ℤ)).map a)
  have hb := e.hom.naturality ((F.mapHomologicalComplex (.up ℤ)).map b)
  simp only [Functor.comp_map] at ha hb
  dsimp only [towerFunctor, Functor.comp_map]
  rw [← Category.assoc, ← ha]
  dsimp only [F, R, e] at *
  simp only [unrestrictedTowerComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, unrestrictedTowerFiniteComplex, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, towerFinite_roof l E Y n a b q q' hT hq hq' h]
  exact hb

private theorem towerReduction_quasiIso (n : ℕ)
    {T P : CochainComplex (scalarReductionSource l E Y) ℤ} (a : T ⟶ P)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) T)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P)
    (ha : QuasiIso a) :
    QuasiIso ((towerFunctor l E Y n).map a) := by
  have hfinite : QuasiIso
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).map a) := by
    simpa only [scalarReductionExtension] using
      ((scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.1
        a hT hP ha)
  change QuasiIso (((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map
    (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).map a))
  infer_instance

attribute [local irreducible] unrestrictedTowerComparison

/-- The finite canonical comparisons give an isomorphism of the two augmented towers.
The unit and transition maps are the unique maps with the specified pure-tensor formulas.
The comparison is the recorded derived counit comparison.
Source: Stacks Tags 06YS/06YT/06YY and derived.tex Tags 05RT/06XN;
Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

Proof:
1. Apply the common-roof property for quasi-isomorphisms in the homotopy category
(lem-pur-quasi-isos-saturated-triangulated) to q and q'. Resolve its source V by
lem-pc-kflat-resolution, obtaining K-flat T and quasi-isomorphisms a:T→P, b:T→P'
with qa=q'b in the homotopy category. No direct chain map P→P' is assumed.
2. Termwise tensoring preserves these quasi-isomorphisms by clause (1) of
lem-pur-derived-change-of-rings. Naturality of its universal counit, invertible on
T,P,P', identifies the canonical comparison with [a_n]⁻¹ ≫ [b_n]. This is also the
comparison defined through integralDerivedReductionResolutionIso; the quotient and
restriction factorization isomorphisms merely express the same objects by complexes.
3. On local sections, a_n γ_T = γ_P a and b_n γ_T = γ_P' b, since both sides
send x to 1⊗a(x), respectively 1⊗b(x). Sheafification and localization preserve
these identities. Cancel [a_n], [b_n] and use qa=q'b to obtain clause (1).
4. Similarly a_n τ_T = τ_P a_(n+1) and b_n τ_T = τ_P' b_(n+1), since both
sides send s⊗x to ρ_n(s)⊗a(x), respectively ρ_n(s)⊗b(x). The projection
identity makes these maps linear over the completed sheaf. Sheafify, localize and
cancel to obtain clause (2). The components are isomorphisms by construction;
rearranging clause (2) gives compatibility of their inverses, hence the asserted
isomorphism of inverse systems, and clause (1) respects the augmentations. -/
theorem unrestrictedReductionTowerWellDefined
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q')
    :
    (∀ n : ℕ,
      (unrestrictedTowerAugmentationIso l E Y q hq).inv ≫
        DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P n) ≫
        (unrestrictedTowerComparison l E Y n q q' hq hq').hom =
      (unrestrictedTowerAugmentationIso l E Y q' hq').inv ≫
        DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P' n)) ∧
    (∀ n : ℕ,
      DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P n) ≫
        (unrestrictedTowerComparison l E Y n q q' hq hq').hom =
      (unrestrictedTowerComparison l E Y (n + 1) q q' hq hq').hom ≫
        DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P' n)) := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  classical
  let : QuasiIso q := hq.1
  let : QuasiIso q' := hq'.1
  obtain ⟨T, a, b, hT, ha, hb, h⟩ := towerRoof l E Y q q' hq.1 hq'.1
  let : QuasiIso a := ha
  let : QuasiIso b := hb
  have hc (n : ℕ) := towerComparison_roof l E Y n a b q q' hT hq hq' h
  have hu (n : ℕ) {A B : CochainComplex (scalarReductionSource l E Y) ℤ}
      (f : A ⟶ B) :
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (unrestrictedTowerUnit l E Y B n) =
        DerivedCategory.Q.map (unrestrictedTowerUnit l E Y A n) ≫
          DerivedCategory.Q.map ((towerFunctor l E Y n).map f) := by
    simpa only [Functor.map_comp] using
      congrArg (DerivedCategory.Q.map) (towerUnit_naturality l E Y n f)
  have ht (n : ℕ) {A B : CochainComplex (scalarReductionSource l E Y) ℤ}
      (f : A ⟶ B) :
      DerivedCategory.Q.map ((towerFunctor l E Y (n + 1)).map f) ≫
          DerivedCategory.Q.map (unrestrictedTowerTransition l E Y B n) =
        DerivedCategory.Q.map (unrestrictedTowerTransition l E Y A n) ≫
          DerivedCategory.Q.map ((towerFunctor l E Y n).map f) := by
    let τ : towerFunctor l E Y (n + 1) ⟶ towerFunctor l E Y n :=
      unrestrictedIntegralTransition l E Y n
    have hQ := (Functor.whiskerRight τ
      (DerivedCategory.Q (C := scalarReductionSource l E Y))).naturality f
    simpa only [Functor.comp_map, Functor.whiskerRight_app, τ,
      unrestrictedTowerTransition] using hQ
  constructor
  · intro n
    apply (cancel_epi (DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q)).1
    change (DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q) ≫
        (inv (DerivedCategory.Q.map q) ≫ _ ≫ _) =
      (DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q) ≫
        (inv (DerivedCategory.Q.map q') ≫ _)
    calc
      _ = DerivedCategory.Q.map a ≫
          DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P n) ≫
            (unrestrictedTowerComparison l E Y n q q' hq hq').hom := by simp [Category.assoc]
      _ = DerivedCategory.Q.map (unrestrictedTowerUnit l E Y T n) ≫
          (DerivedCategory.Q.map ((towerFunctor l E Y n).map a) ≫
            (unrestrictedTowerComparison l E Y n q q' hq hq').hom) := by
          rw [← Category.assoc, hu, Category.assoc]
      _ = DerivedCategory.Q.map (unrestrictedTowerUnit l E Y T n) ≫
          DerivedCategory.Q.map ((towerFunctor l E Y n).map b) := by
          rw [hc]
      _ = DerivedCategory.Q.map b ≫
          DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P' n) := (hu n b).symm
      _ = _ := by rw [h]; simp [Category.assoc]
  · intro n
    have := towerReduction_quasiIso l E Y (n + 1) a hT hq.2 ha
    apply (cancel_epi
      (DerivedCategory.Q.map ((towerFunctor l E Y (n + 1)).map a))).1
    calc
      _ = DerivedCategory.Q.map (unrestrictedTowerTransition l E Y T n) ≫
          (DerivedCategory.Q.map ((towerFunctor l E Y n).map a) ≫
            (unrestrictedTowerComparison l E Y n q q' hq hq').hom) := by
          rw [← Category.assoc, ht, Category.assoc]
      _ = DerivedCategory.Q.map (unrestrictedTowerTransition l E Y T n) ≫
          DerivedCategory.Q.map ((towerFunctor l E Y n).map b) := by
          rw [hc]
      _ = DerivedCategory.Q.map ((towerFunctor l E Y (n + 1)).map b) ≫
          DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P' n) := (ht n b).symm
      _ = _ := by rw [← Category.assoc, hc]

end WeilConjectures
