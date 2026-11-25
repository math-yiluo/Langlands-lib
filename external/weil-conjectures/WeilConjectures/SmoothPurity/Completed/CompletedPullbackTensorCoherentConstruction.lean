/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorAssociativityRepresentatives
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorUnitFromAssociativity
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorSignedRepresentatives
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationRepresentatives
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorProofImplementations
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
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
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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

/-! # Coherent pullback/tensor evaluation and coherence

Source: Stacks 07A4, 0941 and 03D2. These existing proved declarations are
extracted verbatim from the completed construction to keep file compilation
within the project limit. The parent publicly re-exports them.
(blueprint: lem-pur-completed-pullback-tensor-coherent-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite inverse image in the strict integral tower is the intrinsic inverse
image, with equality on the actual adjunction-unit sections.
Source: Stacks 00YV, 03D2 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: both right adjoints take sections over the same base-change object with
the same constant coefficient action. The identity of right adjoints induces
this comparison of left adjoints. Its unit formula characterizes it uniquely. -/
theorem pullbackTensorLevelIntrinsic_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
        (x : M.val.obj (op U)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
          (((coefficientProEtaleModuleAdjunction.{u, u} f
            (CommRingCat.of (ULift.{u + 1}
              (finiteCoefficientRing l E (n + 1))))).unit.app M).val.app (op U) x) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op U) x := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let A := finiteCoefficientRing l E (n + 1)
    let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f
      (CommRingCat.of (ULift.{u + 1} A))
    let adj₂ : sfIntrinsicPullback A f ⊣
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} A)) :=
      sfIntrinsicConstantModuleAdjunction f A
    refine ⟨adj₁.leftAdjointUniq adj₂, ?_, ?_⟩
    · intro M U x
      exact congrArg (fun a ↦ a.val.app (op U) x)
        (Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ M)
    · intro e he
      apply Iso.ext
      apply NatTrans.ext
      funext M
      apply (adj₁.homEquiv M _).injective
      rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
      ext U x
      exact he M U.unop x

/-- The unit-normalized realization of the finite pullback used by the strict tower.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorLevelIntrinsic {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorLevelIntrinsic_existsUnique l E f n)

private theorem derivedCompositeIso_existsUnique
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (A : C₁ ⥤ C₂) (B : C₂ ⥤ D₂) (C : C₁ ⥤ D₁) (D D₀ : D₁ ⥤ D₂)
    [A.Additive] [B.Additive] [C.Additive] [D.Additive] [D₀.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits C] [PreservesFiniteColimits C]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    (c₁ : A.mapHomologicalComplex (.up ℤ) ⋙ B.mapHomologicalComplex (.up ℤ) ≅
      C.mapHomologicalComplex (.up ℤ) ⋙ D₀.mapHomologicalComplex (.up ℤ)) (c₂ : D₀ ≅ D) :
    ∃! e : A.mapDerivedCategory ⋙ B.mapDerivedCategory ≅
      C.mapDerivedCategory ⋙ D.mapDerivedCategory,
      ∀ P : CochainComplex C₁ ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            D.mapDerivedCategory.map (C.mapDerivedCategoryFactors.hom.app P) ≫
            D.mapDerivedCategoryFactors.hom.app
              ((C.mapHomologicalComplex (.up ℤ)).obj P) =
          B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.hom.app P) ≫
            B.mapDerivedCategoryFactors.hom.app
              ((A.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map (c₁.hom.app P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c₂ (.up ℤ)).hom.app
              ((C.mapHomologicalComplex (.up ℤ)).obj P)) := by
  exact completedPullbackDerivedCompositeIso_existsUnique A B C D D₀ c₁ c₂

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived in
attribute [local irreducible] pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic in
/-- The full cochain normalization of finite evaluation, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorDerivedEvaluationNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f) : Prop :=
  ∀ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P))

attribute [local irreducible] pullbackTensorDerivedEvaluationNormalization

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived in
attribute [local irreducible] pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic in
/-- Evaluating the system inverse image gives the finite intrinsic inverse image;
the comparison is fixed on all cochain representatives by the two ordinary units.
Source: Stacks 0941, 03D2 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: apply the exact evaluation functor to a cochain representative. The
ordinary inverse-image/evaluation mate and the unit-normalized intrinsic
realization give the displayed chain comparison. Exact localization descends
it uniquely, since every derived object is represented by a complex. -/
theorem pullbackTensorDerivedEvaluation_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f,
      pullbackTensorDerivedEvaluationNormalization l E f n e := by
  unfold pullbackTensorDerivedEvaluationNormalization
  let D : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
    sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  letI : D.Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI : PreservesFiniteLimits D :=
    sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI : PreservesFiniteColimits D :=
    sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  letI := integralOperationsLevelPullback_additive l E f n
  exact derivedCompositeIso_existsUnique (pullbackTensorSequenceInverse l E f)
    (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E Y n) D
    (integralOperationsLevelPullback l E f n)
    (pullbackTensorInverseEvaluationComplex l E f n).symm
    (pullbackTensorLevelIntrinsic l E f n)

/-- The actual evaluation comparison, including its fixed cochain normalization.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorDerivedEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorDerivedEvaluation_existsUnique l E f n)

private theorem coherentTensor_representatives
    (W : Scheme.{u}) (M : coefficientSequenceDerived l E W) :
    ∃ P : CochainComplex (coefficientSequenceModules l E W) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let q := DerivedCategory.Q (C := coefficientSequenceModules l E W)
  let K := q.objPreimage M
  obtain ⟨P, a, hP, _, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  let : QuasiIso a := ha
  exact ⟨P, hP, ⟨asIso (q.map a) ≪≫ q.objObjPreimageIso M⟩⟩

private theorem tensorNatTrans_ext_resolving
    {B : Type*} [Category* B] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ Y Z : B, P Y → P Z → a.app (q.obj Y, q.obj Z) =
      b.app (q.obj Y, q.obj Z)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, hY, ⟨eY⟩⟩ := res X.1
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := res X.2
  let e := Iso.prod eY eZ
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h Y Z hY hZ]

section CoherentEvaluation
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] pullbackTensorSystemComparison pullbackTensorDerivedEvaluation
  pullbackTensorSequenceDerived pullbackTensorSequenceInverse
  finitePullbackTensorConstructionIso canonicalFinitePullbackTensor

/-- The coherent comparison whose limit defines μI evaluates to the same μF at
EVERY finite level, under the canonical tensor and inverse-image comparisons.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: on a flat K-flat pair both routes are the totalization of the identical
ordinary section formula. The evaluation tensor comparison and inverse-image
comparison preserve these sections by their normalizations. K-flat descent
therefore proves the equation on arbitrary coherent derived inputs. -/
theorem pullbackTensorSystemComparison_evaluation {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : coefficientSequenceDerived l E Y) :
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((pullbackTensorDerivedEvaluation l E f n).hom.app M)
          ((pullbackTensorDerivedEvaluation l E f n).hom.app N)) =
    (pullbackTensorDerivedEvaluation l E f n).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom := by
  unfold canonicalFinitePullbackTensor
  exact completedPullbackTensor_evaluation_descent l E f n
    (pullbackTensorLevelIntrinsic l E f n)
    ((pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose_spec)
    (pullbackTensorDerivedEvaluation l E f n) (by
      unfold pullbackTensorDerivedEvaluation pullbackTensorUniqueChoice
      simpa only [pullbackTensorDerivedEvaluationNormalization] using
        (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec)
    (coherentTensor_representatives l E Y) M N

end CoherentEvaluation

section CoherentAssociativity
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorSequenceInverse

/-- Associativity for the actual coherent μ whose derived limit is the integral μ.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: on three simultaneous flat K-flat representatives the two maps send
(x tensor y) tensor z to f*x tensor (f*y tensor f*z). The total reassociation
preserves the signed differential and all sequence restrictions. Localize this
equality of coherent complexes; applying the actual limit functor preserves it. -/
theorem pullbackTensorSystemComparison_associativity {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N P : coefficientSequenceDerived l E Y) :
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.associator M N P).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (M,(pullbackTensorCalculus l E Y).systemClosed.tensor.obj (N,P)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((pullbackTensorSystemComparison l E f).hom.app (N,P))) =
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N),P) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorSystemComparison l E f).hom.app (M,N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l E X).systemClosed.monoidal.associator
        ((pullbackTensorSequenceDerived l E f).obj M)
        ((pullbackTensorSequenceDerived l E f).obj N)
        ((pullbackTensorSequenceDerived l E f).obj P)).hom := by
  letI : MonoidalCategory (coefficientSequenceDerived l E Y) :=
    (pullbackTensorCalculus l E Y).systemClosed.monoidal
  letI : MonoidalCategory (coefficientSequenceDerived l E X) :=
    (pullbackTensorCalculus l E X).systemClosed.monoidal
  let F := pullbackTensorSequenceDerived l E f
  let μ := pullbackTensorSystemComparison l E f
  let a := assocLeftPath F μ
  let b := assocRightPath F μ
  have hab : a = b := tripleNatTrans_ext_resolving DerivedCategory.Q
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y))
    (coherentTensor_representatives l E Y) a b (by
      intro A B C hA hB hC
      exact completedPullbackTensor_associativity_representatives l E f A B C hA hB hC)
  exact NatTrans.congr_app hab (M,N,P)

end CoherentAssociativity

section CoherentBraiding
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorBraiding pullbackTensorSequenceInverse

attribute [local implicit_reducible] pullbackTensorSwap in
/-- Koszul braiding for the same coherent μ before taking its derived limit.
Source: Stacks 06YS, 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: both maps take a homogeneous generator x tensor y of degrees p,q to
(-1)^(pq) f*y tensor f*x. The equality respects every sequence restriction and
descends through the specified K-flat tensor models. Its image under the actual
limit, scalar localization, and common-stage maps gives the higher-level equation. -/
theorem pullbackTensorSystemComparison_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N : coefficientSequenceDerived l E Y) :
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y)
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel).hom.app (M,N)) ≫
      (pullbackTensorSystemComparison l E f).hom.app (N,M) =
    (pullbackTensorSystemComparison l E f).hom.app (M,N) ≫
      (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).systemTensorModel).hom.app
          ((pullbackTensorSequenceDerived l E f).obj M,
            (pullbackTensorSequenceDerived l E f).obj N) := by
  let F := pullbackTensorSequenceDerived l E f
  let TY := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let μ := pullbackTensorSystemComparison l E f
  let σY := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y)
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E Y).systemTensorModel
  let σX := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    (pullbackTensorCalculus l E X).systemClosed
    (pullbackTensorCalculus l E X).systemTensorModel
  let a : TY ⋙ F ⟶ pullbackTensorSwap _ ⋙ (F.prod F) ⋙ TX :=
    Functor.whiskerRight σY.hom F ≫
      Functor.whiskerLeft (pullbackTensorSwap _) μ.hom
  let b : TY ⋙ F ⟶ pullbackTensorSwap _ ⋙ (F.prod F) ⋙ TX :=
    μ.hom ≫ Functor.whiskerLeft (F.prod F) σX.hom
  have hab : a = b := tensorNatTrans_ext_resolving DerivedCategory.Q
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y))
    (coherentTensor_representatives l E Y) a b (by
      intro P Q hP hQ
      exact completedPullbackTensor_signed_representatives l E f P Q hP hQ)
  exact NatTrans.congr_app hab (M,N)

end CoherentBraiding

section CoherentUnit
universe a b c d
open MonoidalCategory

/-- Both unit equations for the coherent μ used to define the integral comparison.
Source: Stacks 03EL, 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: the associativity comparison and the coherent unit representative are
combined by the monoidal unit extraction lemma. -/
theorem pullbackTensorSystemComparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ ε : (pullbackTensorSequenceDerived l E f).obj
        (pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l E X).systemClosed.monoidal.tensorUnit,
      ∀ M : coefficientSequenceDerived l E Y,
        ((pullbackTensorSystemComparison l E f).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit,M) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
            ((pullbackTensorSequenceDerived l E f).obj M)).hom =
        (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.leftUnitor M).hom) ∧
        ((pullbackTensorSystemComparison l E f).hom.app
          (M,(pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
            ((pullbackTensorSequenceDerived l E f).obj M)).hom =
        (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.rightUnitor M).hom) := by
  exact completedPullbackTensor_unit_of_associativity l E f
    (pullbackTensorSystemComparison_associativity l E f)

end CoherentUnit

end CoherentSystems

end WeilConjectures
