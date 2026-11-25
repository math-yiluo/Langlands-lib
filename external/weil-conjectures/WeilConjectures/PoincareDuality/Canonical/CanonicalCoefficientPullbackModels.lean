/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

/-!
# Models for canonical coefficient pullback and finite quotient projections

(blueprint: lem-pod-canonical-coefficient-model-maps).

Source: Stacks Tags 03D6 and 08TC; blueprint prop-cohomological-finiteness, Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

The sectionwise inverse image used by the specified kappa is compared with the
normalized constant Weil structure through the actual regular-module coefficient
maps. Finite multiplication and projection from the strict Roos cone are retained
as morphisms, including their transition maps before localization. Level n means
positive exponent n+1 throughout.

## Main definitions

* `canonicalCoefficientKappa`: the recorded comparison on the regular good complex.
* `canonicalCoefficientLambda`, `canonicalCoefficientLambdaFinite`: the normalized
  integral comparison and finite multiplication, with coefficient-model transport.
* `canonicalCoefficientRho`: the actual quotient-cone projection and reduction.
* `canonicalCoefficientProjection`, `canonicalCoefficientInverseProjection`: the
  two coefficient projections in the same integral derived category.
* `canonicalCoefficientPullbackTransition`, `canonicalCoefficientInverseTransition`:
  the strict finite quotient transitions.

## Main statements

* `canonicalCoefficientModelMaps_isIso`: the regular coefficient identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] regularExtensionIso regularExtensionPresheafIso
  identityRestrictionIso scalarReductionExistence HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence limit finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel chainUnitCandidate
  integralDerivedPullback integralDerivedPullbackComparison
  constantWeilIntegralRoosComparison
  constantWeilIntegralLambda constantWeilDerivedCoefficientComparison
  SheafOfModules.monoidalCategory constantSheaf
set_option backward.isDefEq.respectTransparency.types false

/-- The regular-module map R_X to the sectionwise inverse image of R_Y.
Its sectionwise formula is c_R inverse: send 1 to 1 and transport scalars by c_R.
Source: Stacks 03D6; inverse-image-pullback-comparison, structure isomorphism
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientIntegralUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X) ⟶
    (inverseImageIntegralModules l E g).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U.unop))))
      (fun {_ _} f ↦ map_one
        ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map
          ((proEtaleIsoPostcompose g).map f.unop).op).hom))
/-- The finite regular-module map B_X,n to inverse image of B_Y,n,
sending 1 to 1 with scalar action through c_n inverse.
Source: Stacks 03D6, module pullback along the coefficient isomorphism
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) : SheafOfModules.unit (integralCoefficientSheaf l E X n) ⟶
    (inverseImageFiniteModules l E g n).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E Y n).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U.unop))))
      (fun {_ _} f ↦ map_one
        ((integralCoefficientSheaf l E Y n).obj.map
          ((proEtaleIsoPostcompose g).map f.unop).op).hom))
/-- The canonical multiplication identification of reduction of the regular
module with the finite regular module, transposed from the actual coefficient
projection under the normalized tensor/restriction adjunction.
Source: Stacks 03D6; node proof Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientReduction (W : Scheme.{u}) (n : ℕ) :=
  ((scalarReductionExtension_adjunction l E W n).choose.homEquiv _ _).symm
    (constantCoefficientProjection l E W n)
/-- The same canonical reduction identification on the regular complexes,
using the exact degree-zero single-complex comparison.
Source: Stacks 03D6; node proof Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientReductionComplex (W : Scheme.{u}) (n : ℕ) :=
  ((unrestrictedIntegralReductionFunctor l E W n).mapCochainComplexSingleFunctor 0).hom.app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) ≫
    (CochainComplex.singleFunctor _ 0).map (canonicalCoefficientReduction l E W n)

/-- The regular finite coefficient complex B_Y,n[0].
Source: node statement, finite coefficient objects; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteComplex (W : Scheme.{u}) (n : ℕ) :=
  (CochainComplex.singleFunctor (integralOperationsFiniteModules l E W n) 0).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E W n))

/-- The finite tensor-unit chain map x to x tensor 1, whose inverse is multiplication.
Source: inverse-image-pullback-comparison (a); node proof Step 2; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteKappaComplex {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  inverseImageFiniteComparisonComplex l E g n (canonicalCoefficientFiniteComplex l E Y n)

private theorem canonicalCoefficientFiniteUnit_isIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    IsIso (canonicalCoefficientFiniteUnit l E g n) := by
  apply (isIso_iff_of_reflects_iso (canonicalCoefficientFiniteUnit l E g n)
    (SheafOfModules.toSheaf (integralCoefficientSheaf l E X n) ⋙
      sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1})).mp
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (fun x ↦
    (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U x * 1)
  simp only [mul_one]
  exact (ConcreteCategory.isIso_iff_bijective
    ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U)).1 inferInstance

private theorem coefficientReduction_eq (W : Scheme.{u}) (n : ℕ) :
    canonicalCoefficientReduction l E W n = (finiteRegularIso l E W n).hom := by
  let adj := (scalarReductionExtension_adjunction l E W n).choose
  apply (adj.homEquiv _ _).injective
  change (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply (SheafOfModules.unitHomEquiv _).injective
  ext U
  have hu := (scalarReductionExtension_adjunction l E W n).choose_spec
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) U
    (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U)
  simp only [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U 1 * 1 =
    (finiteRegularIso l E W n).hom.val.app U
      ((adj.unit.app (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E W))).val.app U
        (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U))
  rw [map_one, one_mul, hu]
  exact (finiteRegularIso_one l E W n U).symm

private theorem canonicalCoefficientReduction_isIso (W : Scheme.{u}) (n : ℕ) :
    IsIso (canonicalCoefficientReduction l E W n) := by
  rw [coefficientReduction_eq]
  infer_instance

private def coefficientFiniteInverseIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    ((inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ)).obj
      (canonicalCoefficientFiniteComplex l E Y n) ≅
    canonicalCoefficientFiniteComplex l E X n :=
  (HomologicalComplex.singleMapHomologicalComplex
      (inverseImageFiniteModules l E g n) (.up ℤ) 0).app
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientFiniteUnit l E g n)
        (canonicalCoefficientFiniteUnit_isIso l E g n)).symm

private def coefficientFinitePullIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    ((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).obj
      (canonicalCoefficientFiniteComplex l E Y n) ≅
    canonicalCoefficientFiniteComplex l E X n :=
  (HomologicalComplex.singleMapHomologicalComplex
      (integralOperationsLevelPullback l E g n) (.up ℤ) 0).app
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso (finitePullbackRegularIso l E g n)

attribute [local irreducible] canonicalCoefficientFiniteKappaComplex canonicalCoefficientFiniteUnit
  coefficientFiniteInverseIso coefficientFinitePullIso

private theorem coefficientFiniteKappa_triangle {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (coefficientFiniteInverseIso l E g n).inv ≫
      canonicalCoefficientFiniteKappaComplex l E g n ≫
      (coefficientFinitePullIso l E g n).hom = 𝟙 _ := by
  let I := inverseImageFiniteModules l E g n
  let P : integralOperationsFiniteModules l E Y n ⥤
      integralOperationsFiniteModules l E X n := integralOperationsLevelPullback l E g n
  let M := SheafOfModules.unit (integralCoefficientSheaf l E Y n)
  let N := SheafOfModules.unit (integralCoefficientSheaf l E X n)
  let sY := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) 0 N
  have := canonicalCoefficientFiniteUnit_isIso l E g n
  let c := coefficientFiniteInverseIso l E g n
  let e := coefficientFinitePullIso l E g n
  have hc : sX.inv ≫ c.inv.f 0 =
      canonicalCoefficientFiniteUnit l E g n ≫ I.map sY.inv := by
    simp only [I, c, sX, sY, N, M, coefficientFiniteInverseIso, Iso.trans_inv,
      HomologicalComplex.comp_f, Functor.mapIso_inv,
      Iso.symm_inv, asIso_hom, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self,
      Iso.app_inv, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Category.assoc, Iso.inv_hom_id_assoc]
  have he : e.hom.f 0 ≫ sX.hom =
      P.map sY.hom ≫ (finitePullbackRegularIso l E g n).hom := by
    simp only [P, e, sX, sY, N, M, coefficientFinitePullIso, Iso.trans_hom,
      HomologicalComplex.comp_f, Functor.mapIso_hom,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_epi sX.inv).1
  apply (cancel_mono sX.hom).1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.assoc]
  erw [← Category.assoc sX.inv, hc, he]
  simp only [Category.assoc]
  apply (SheafOfModules.unitHomEquiv _).injective
  ext U
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let x := sY.inv.val.app (op V) (1 : (integralCoefficientSheaf l E Y n).obj.obj (op V))
  have hk := (inverseImageFiniteComparison_existsUnique l E g n
    (canonicalCoefficientFiniteComplex l E Y n)).exists.choose_spec 0 U.unop x
  have hn := (coefficientProEtaleModuleAdjunction.{u, u} g
    (CommRingCat.of (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))))).unit.naturality sY.hom
  have hnx := congrArg (fun a ↦ a.val.app (op V) x) hn
  have hx : sY.hom.val.app (op V) x =
      (1 : (integralCoefficientSheaf l E Y n).obj.obj (op V)) := by
    change ((sY.inv ≫ sY.hom).val.app (op V))
      (1 : (integralCoefficientSheaf l E Y n).obj.obj (op V)) = _
    rw [sY.inv_hom_id]
    rfl
  have hr := PresheafOfModules.naturality_apply (P.map sY.hom).val
    (proEtaleIsoCommaArrow g U.unop).op
    (integralOperationsPullbackGenerator l E g n
      ((canonicalCoefficientFiniteComplex l E Y n).X 0) V x)
  have ht := PresheafOfModules.naturality_apply
    (finitePullbackRegularIso l E g n).hom.val
    (proEtaleIsoCommaArrow g U.unop).op
    (integralOperationsPullbackGenerator l E g n M V
      (1 : (integralCoefficientSheaf l E Y n).obj.obj (op V)))
  have hunit : (canonicalCoefficientFiniteUnit l E g n).val.app U
      (1 : (integralCoefficientSheaf l E X n).obj.obj U) =
        (1 : (integralCoefficientSheaf l E Y n).obj.obj (op V)) := by
    unfold canonicalCoefficientFiniteUnit
    change (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U 1 * 1 = 1
    simp only [map_one, one_mul]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.unitHomEquiv_apply_coe]
  rw [hunit]
  change (finitePullbackRegularIso l E g n).hom.val.app U
    ((P.map sY.hom).val.app U
      (((canonicalCoefficientFiniteKappaComplex l E g n).f 0).val.app U x)) =
      (1 : (integralCoefficientSheaf l E X n).obj.obj U)
  change ((inverseImageFiniteComparisonComplex l E g n
    (canonicalCoefficientFiniteComplex l E Y n)).f 0).val.app U x = _ at hk
  have hkappa : canonicalCoefficientFiniteKappaComplex l E g n =
      inverseImageFiniteComparisonComplex l E g n
        (canonicalCoefficientFiniteComplex l E Y n) := by
    unfold canonicalCoefficientFiniteKappaComplex
    rfl
  rw [hkappa, hk]
  erw [hr]
  change integralOperationsPullbackGenerator l E g n M V
      (sY.hom.val.app (op V) x) =
    ((P.map sY.hom).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator l E g n _ V x) at hnx
  rw [hx] at hnx
  erw [← hnx]
  erw [ht]
  rw [finitePullbackRegularIso_generator l E g n V]
  exact PresheafOfModules.unit_map_one _ (proEtaleIsoCommaArrow g U.unop).op

private theorem canonicalCoefficientFiniteKappa_isIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    IsIso (canonicalCoefficientFiniteKappaComplex l E g n) := by
  have hi : IsIso ((coefficientFiniteInverseIso l E g n).inv ≫
      canonicalCoefficientFiniteKappaComplex l E g n ≫
      (coefficientFinitePullIso l E g n).hom) := by
    rw [coefficientFiniteKappa_triangle]
    infer_instance
  exact (isIso_comp_right_iff _ (coefficientFinitePullIso l E g n).hom).1
    ((isIso_comp_left_iff (coefficientFiniteInverseIso l E g n).inv _).1 hi)

/-- The maps used to identify the coefficient models are isomorphisms.
Source: node statement, c_R and c_n, finite multiplication and canonical reduction;
node proof Steps 2 and 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).
Proof: on sections the integral and finite unit maps are c_R inverse and c_n inverse,
respectively, so the coefficient isomorphisms give their inverses. The reduction map
s tensor x to s*pi_n(x) is inverse to b to b tensor 1 by the balancing relation.
These commute with differentials, giving the reduction complex isomorphism. Finally
x tensor b to c_n inverse(b)*x is inverse to the sheafified tensor-unit map in every
degree. The formulas commute with restrictions, so they descend from presheaves to
sheaves. Exact degree-zero comparisons preserve all these inverse identities. -/
theorem canonicalCoefficientModelMaps_isIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    IsIso (canonicalCoefficientIntegralUnit l E g) ∧
      ∀ n : ℕ, IsIso (canonicalCoefficientFiniteUnit l E g n) ∧
        IsIso (canonicalCoefficientReductionComplex l E Y n) ∧
        IsIso (canonicalCoefficientFiniteKappaComplex l E g n) := by
  constructor
  · apply (isIso_iff_of_reflects_iso (canonicalCoefficientIntegralUnit l E g)
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E X) ⋙
        sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1})).mp
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun x ↦
      (inv (inverseImageCompletedCoefficientMap l E g)).hom.app U x * 1)
    simp only [mul_one]
    exact (ConcreteCategory.isIso_iff_bijective
      ((inv (inverseImageCompletedCoefficientMap l E g)).hom.app U)).1 inferInstance
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · exact canonicalCoefficientFiniteUnit_isIso l E g n
    · have := canonicalCoefficientReduction_isIso l E Y n
      unfold canonicalCoefficientReductionComplex
      infer_instance
    · exact canonicalCoefficientFiniteKappa_isIso l E g n

attribute [local irreducible] canonicalCoefficientIntegralUnit
  canonicalCoefficientReduction canonicalCoefficientReductionComplex

/-- c_R on regular objects in the sectionwise inverse-image presentation.
It is defined from the actual coefficient map, independently of kappa and lambda.
Source: node structure isomorphism and proof Step 1; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientIntegralComparison {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  ((inverseImageIntegralModules l E g).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≪≫
    (DerivedCategory.singleFunctor (integralTowerModules l E X) 0).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientIntegralUnit l E g)
        (canonicalCoefficientModelMaps_isIso l E g).1).symm

/-- The canonical transport from the normalized termwise inverse-image realization
of constantWeilIntegralLambda to the sectionwise realization of the specified kappa.
It uses only the two independently constructed coefficient comparisons c_R.
Source: node proof Steps 1 and 9; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientInverseImageTransport {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  constantWeilDerivedCoefficientComparison l E g ≪≫
    (canonicalCoefficientIntegralComparison l E g).symm

/-- lambda_R is the normalized multiplication/completeness comparison, transported
by the coefficient-model identification. No inverse of kappa is used to define it.
Source: node proof Steps 2--6 and 9; Stacks 03D6 and 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientLambda {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  constantWeilIntegralLambda l E g ≪≫ canonicalCoefficientInverseImageTransport l E g

/-- kappa_R is exactly the specified zero-homotopy Roos augmentation of definition
(b), on the regular flat-term K-flat representative with its identity resolution.
Source: inverse-image-pullback-comparison (b); node proof Step 6; Stacks 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientKappa {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :=
  inverseImagePullbackComparison l E g hX hY
    (constantWeilIntegralComplex l E Y) (constantWeilIntegralGood l E Y) (𝟙 _)

/-- The actual finite multiplication chain isomorphism lambda_n. Its inverse is the
recorded sheafified x to x tensor 1 map, which uniquely fixes multiplication.
Source: node proof Step 2; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientLambdaFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :=
  (@asIso _ _ _ _ (canonicalCoefficientFiniteKappaComplex l E g n)
    ((canonicalCoefficientModelMaps_isIso l E g).2 n).2.2).symm

/-- c_n on finite regular complexes in the sectionwise inverse-image model.
Source: node structure isomorphism and proof Step 2; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :=
  ((inverseImageFiniteModules l E g n).mapCochainComplexSingleFunctor 0).app
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≪≫
    (CochainComplex.singleFunctor (integralOperationsFiniteModules l E X n) 0).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientFiniteUnit l E g n)
        ((canonicalCoefficientModelMaps_isIso l E g).2 n).1).symm

/-- The finite restriction of scalars Res_n, on actual complexes.
Source: completed-integral-coefficients; node statement; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
abbrev canonicalCoefficientRes (W : Scheme.{u}) (n : ℕ) :=
  integralOperationsRestrict l E W n

/-- The pulled-back canonical reduction identification, followed by restriction
of scalars. It identifies the strict quotient tower term with Res_n Lg_n^* B_Y,n.
Source: node proof Step 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientPullbackReductionIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientRes l E X n).mapIso
    (((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientReductionComplex l E Y n)
        ((canonicalCoefficientModelMaps_isIso l E g).2 n).2.1))

/-- rho_n is the defining good-representative comparison, the actual first Roos
coordinate and nth product projection, then the pulled reduction identification.
Its source is P_g R_Y; its target is Res_n Lg_n^* B_Y,n in the single R_X category.
Source: node proof Steps 3, 4 and 7; Stacks 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientRho {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (integralDerivedPullbackComparison l E g).hom.app (constantWeilIntegralGood l E Y) ≫
    DerivedCategory.Q.map
      (CochainComplex.mappingCocone.fst (constantWeilPullbackRoosEndomorphism l E g) ≫
        Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n) ≫
    DerivedCategory.Q.map (canonicalCoefficientPullbackReductionIso l E g n).hom

/-- pi_n,X as an R_X-linear derived morphism, with exact restriction-of-scalars
and degree-zero comparisons included.
Source: node proof Step 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientProjection (W : Scheme.{u}) (n : ℕ) :=
  DerivedCategory.Q.map
    ((CochainComplex.singleFunctor _ 0).map (constantCoefficientProjection l E W n) ≫
      ((scalarReductionRestriction l E W n).mapCochainComplexSingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))

/-- The inverse-image projection g^-1(pi_n,Y), expressed using the actual canonical
coefficient square c_R*pi_n,X = g^-1(pi_n,Y)*c_n. All maps here depend only on
coefficient projections and c_R,c_n, independently of lambda and rho.
Source: node structure square and proof Steps 1 and 8; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientInverseProjection {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientIntegralComparison l E g).hom ≫
    canonicalCoefficientProjection l E X n ≫
    DerivedCategory.Q.map
      ((canonicalCoefficientRes l E X n).map
        (canonicalCoefficientFiniteComparison l E g n).inv)

/-- theta_R = c_R composed with lambda_R in the recorded sectionwise model.
Source: node statement and proof Steps 8--9; Stacks 03D6 and blueprint Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientTheta {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  canonicalCoefficientLambda l E g ≪≫ canonicalCoefficientIntegralComparison l E g

/-- The specified finite pullback transition, transported by the two canonical
reduction identifications. This is a chain map before taking the derived limit.
Source: node proof Steps 3 and 7; Stacks 03D6 and 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientPullbackTransition {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientPullbackReductionIso l E g (n + 1)).inv ≫
    (integralOperationsPullbackTransition l E g n).app (constantWeilIntegralComplex l E Y) ≫
    (canonicalCoefficientPullbackReductionIso l E g n).hom

/-- The actual A_(n+2) to A_(n+1) quotient map on restricted regular complexes.
Reduction of the unit complex is identified with B_n by multiplication, so conjugating
the recorded pure-tensor transition gives precisely the quotient map.
Source: node proof Step 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientTransition (W : Scheme.{u}) (n : ℕ) :=
  (canonicalCoefficientRes l E W (n + 1)).map
      ((@asIso _ _ _ _ (canonicalCoefficientReductionComplex l E W (n + 1))
        ((canonicalCoefficientModelMaps_isIso l E (𝟙 W)).2 (n + 1)).2.1).inv) ≫
    (unrestrictedIntegralTransition l E W n).app (constantWeilIntegralComplex l E W) ≫
    (canonicalCoefficientRes l E W n).map (canonicalCoefficientReductionComplex l E W n)

/-- The corresponding inverse-image quotient transition, transported through c_n.
Source: node proof Step 3; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientInverseTransition {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientRes l E X (n + 1)).map
      (canonicalCoefficientFiniteComparison l E g (n + 1)).hom ≫
    canonicalCoefficientTransition l E X n ≫
    (canonicalCoefficientRes l E X n).map (canonicalCoefficientFiniteComparison l E g n).inv

attribute [local irreducible] canonicalCoefficientIntegralComparison
  canonicalCoefficientInverseImageTransport
  canonicalCoefficientLambda canonicalCoefficientKappa canonicalCoefficientLambdaFinite
  canonicalCoefficientFiniteComparison canonicalCoefficientPullbackReductionIso
  canonicalCoefficientRho canonicalCoefficientProjection canonicalCoefficientInverseProjection
  canonicalCoefficientTheta canonicalCoefficientPullbackTransition canonicalCoefficientTransition
  canonicalCoefficientInverseTransition

end WeilConjectures
