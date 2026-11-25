/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearStageTowerTransport
import WeilConjectures.SmoothPurity.Rational.RationalTensorTowerCoherence

/-! # Coherence of the rational tensor scalar comparisons

Source: the common-stage tensor argument of prose-03-02,
using the normalized scalar-extension comparisons of
lem-pur-integral-operations-scalar-extension; Stacks Project, Tags 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w u₁ v₁ u₂ v₂
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension
  rationalTensorScalarComparison HasDerivedCategory.standard integralCoefficientLinear
  ObjectProperty.FullSubcategory.category

/-- Reassociate the two input corrections through the bifunctor.
The proof uses only functoriality and component formulas for whiskering. -/
private theorem tensorStageComparison_endpoint
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C × C ⥤ C) (G : D × D ⥤ D) {T R : C ⥤ D} (e : T ≅ R)
    (c : F ⋙ R ≅ R.prod R ⋙ G) (X Y : C) {X' Y' : D}
    (a : T.obj X ≅ X') (b : T.obj Y ≅ Y') :
    ((Functor.isoWhiskerLeft F e ≪≫ c ≪≫
        Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) G).app (X, Y) ≪≫
      G.mapIso (Iso.prod a b)) =
    e.app (F.obj (X, Y)) ≪≫ c.app (X, Y) ≪≫
      G.mapIso (Iso.prod ((e.app X).symm ≪≫ a) ((e.app Y).symm ≪≫ b)) := by
  apply Iso.ext
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    NatIso.prod_hom, NatTrans.prod, Iso.prod_hom, Functor.mapIso_hom]
  simp only [Category.assoc, ← Functor.map_comp, prod_comp]

/-- Convert generic bilinear descent to a curried specification with supplied endpoints.
This uses the proved descent theorem and substitutes the endpoint equalities. -/
private theorem tensorDescent_with_components
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    (S : StageSystem C) (U : BilinearCoefficientDescent.Family S S S)
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (c : ∀ (P Q : S.PairCategory) (L : I) (h : join P.stage Q.stage ≤ L),
      (S.T h).obj (BilinearCoefficientDescent.output U join left right (P, Q)).obj ≅
        (U.U L).obj (P.toStage ((left _ _).trans h), Q.toStage ((right _ _).trans h)))
    (hc : ∀ P Q L h,
      BilinearCoefficientDescent.endpoint U join left right (P, Q) h = c P Q L h) :
    ∃! F : S.PairCategory × S.PairCategory ⥤ S.PairCategory,
      (∀ P Q, F.obj (P, Q) = BilinearCoefficientDescent.output U join left right (P, Q)) ∧
      ∀ (P Q P' Q' : S.PairCategory) (L : I)
        (h : join P.stage Q.stage ≤ L) (h' : join P'.stage Q'.stage ≤ L)
        (a : P.toStage ((left _ _).trans h) ⟶ P'.toStage ((left _ _).trans h'))
        (b : Q.toStage ((right _ _).trans h) ⟶ Q'.toStage ((right _ _).trans h')),
        HEq (F.map (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom
          (StageSystem.PairCategory.mkHom L _ _ a)
          (StageSystem.PairCategory.mkHom L _ _ b)))
          (StageSystem.PairCategory.mkHom
            (X := BilinearCoefficientDescent.output U join left right (P, Q))
            (Y := BilinearCoefficientDescent.output U join left right (P', Q')) L h h'
            ((c P Q L h).hom ≫ (U.U L).map (Prod.mkHom a b) ≫ (c P' Q' L h').inv)) := by
  have H := BilinearCoefficientDescent.descent_existsUnique U join left right
  apply (existsUnique_congr (fun F ↦ ?_)).mp H
  rw [BilinearCoefficientDescent.isDescent_iff]
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨fun P Q ↦ ho (P, Q), fun P Q P' Q' L h h' a b ↦ ?_⟩
    simpa only [hc] using hm (P, Q) (P', Q') L h h' a b
  · rintro ⟨ho, hm⟩
    refine ⟨fun P ↦ ho P.1 P.2, fun P Q L h h' a b ↦ ?_⟩
    simpa only [hc] using hm P.1 P.2 Q.1 Q.2 L h h' a b

section ProofHelpers

section
variable (l : ℕ) [Fact l.Prime]
  (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem scalarAssociator_self
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) :
    scalarAssociator l E L M ι j (j.comp ι) rfl W =
      sfRationalScalarComp l E L ι W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j := by
  unfold scalarAssociator
  exact Iso.trans_refl _

attribute [local irreducible] scalarAssociator

private def tensorTowerDatum
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (k : E →ₐ[ℚ_[l]] M) (h : j.comp ι = k) :
    TensorTowerDatum (sfRationalConstructibleCategory l E W)
      (sfRationalConstructibleCategory l L W) (sfRationalConstructibleCategory l M W) where
  catC := inferInstance
  catD := inferInstance
  catE := inferInstance
  U := rationalDerivedTensor l E W
  V := rationalDerivedTensor l L W
  B := rationalDerivedTensor l M W
  F := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  G := sfRationalScalarExtension l L W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j
  H := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M k
  a := scalarAssociator l E L M ι j k h W
  p := rationalTensorScalarComparison l E L ι W
  q := rationalTensorScalarComparison l L M j W
  r := rationalTensorScalarComparison l E M k W

private theorem tensorTowerDatum_coherent
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (k : E →ₐ[ℚ_[l]] M) (h : j.comp ι = k) :
    (tensorTowerDatum l W E L ι M j k h).Coherent := by
  subst k
  have hd : tensorTowerDatum l W E L ι M j (j.comp ι) rfl =
      rationalTensorTowerDatum l W E L ι M j := by
    unfold tensorTowerDatum rationalTensorTowerDatum
    rw [scalarAssociator_self l W E L ι M j]
  rw [hd]
  exact rationalTensor_tower l W E L ι M j

end
end ProofHelpers

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- The normalized tensor comparison, expressed using the recorded stage transitions.
Source: the common-stage paragraph of prose-03-02.
(blueprint: lem-weil-rational-tensor-stage-coherence). -/
def rationalTensorStageComparison {E L : Index l Ω} (h : E ≤ L) :
    rationalDerivedTensor l (Coefficient.{u} l Ω E) W ⋙ (stageSystem l Ω W).T h ≅
      ((stageSystem l Ω W).T h).prod ((stageSystem l Ω W).T h) ⋙
        rationalDerivedTensor l (Coefficient.{u} l Ω L) W :=
  have e := eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)
  Functor.isoWhiskerLeft _ e ≪≫
    rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W ≪≫
    Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) _

attribute [local irreducible] scalarAssociator

/-- Cache the tensor functor with the named stage's category interface. -/
private def stageTensorFunctor (E : Index l Ω) :
    Stage l Ω W E × Stage l Ω W E ⥤ Stage l Ω W E :=
  rationalDerivedTensor l (Coefficient.{u} l Ω E) W

/-- Cache the scalar comparison with the named stages' category interfaces. -/
private def stageTensorComparison {E L : Index l Ω} (h : E ≤ L) :
    stageTensorFunctor l Ω W E ⋙ transition l Ω W E L h ≅
      (transition l Ω W E L h).prod (transition l Ω W E L h) ⋙
        stageTensorFunctor l Ω W L :=
  rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W

/-- Cache the normalized associator with the named stages' category interfaces. -/
private def stageTensorAssociator {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    transition l Ω W E L h ⋙ transition l Ω W L M k ≅
      transition l Ω W E M (h.trans k) :=
  scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
    (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) W

private def stageTensorDatum {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    TensorTowerDatum (Stage l Ω W E) (Stage l Ω W L) (Stage l Ω W M) where
  catC := stageCategory l Ω W E
  catD := stageCategory l Ω W L
  catE := stageCategory l Ω W M
  U := stageTensorFunctor l Ω W E
  V := stageTensorFunctor l Ω W L
  B := stageTensorFunctor l Ω W M
  F := transition l Ω W E L h
  G := transition l Ω W L M k
  H := transition l Ω W E M (h.trans k)
  a := stageTensorAssociator l Ω W h k
  p := stageTensorComparison l Ω W h
  q := stageTensorComparison l Ω W k
  r := stageTensorComparison l Ω W (h.trans k)

private theorem stageTensorDatum_eq {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    stageTensorDatum l Ω W h k = tensorTowerDatum l W
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)
      (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k)
      (coefficientInclusion l Ω E M (h.trans k))
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) := by
  rfl

private theorem stageTensor_tower {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    (stageTensorDatum l Ω W h k).Coherent := by
  rw [stageTensorDatum_eq]
  exact tensorTowerDatum_coherent l W
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k)
    (coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)

private theorem stageAssociator_heq {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    HEq ((stageSystem l Ω W).assoc h k) (stageTensorAssociator l Ω W h k) := by
  exact ((stageSystem_existsUnique l Ω W).exists.choose_spec.2 E L M h k).trans
    (associator_existsUnique l Ω W E L M h k).exists.choose_spec

/-- The normalized rational tensor comparisons satisfy the coefficient tower equation.
Source: lem-pur-integral-operations-scalar-extension, coefficient-tower calculation
(scalarOperationsOrdinary_tower), and the common-stage tensor paragraph of
 prose-03-02; Stacks Project, Tags 07A4 and 08J9.
(blueprint: lem-weil-rational-tensor-stage-coherence).

Proof: apply the tensor clause of scalarOperationsOrdinary_tower to the three
coefficient fields and their actual inclusions. Conjugate each ordinary scalar
extension by its canonical scalarCompletion comparison. Naturality moves these
comparisons through the tensor functor; the adjacent inverse completion maps
cancel, giving the completed integral tensor equation with sfIntegralScalarComp.
Restrict to the constructible full subcategories and apply rational localization.
The component specifications of rationalTensorScalarComparison and
sfRationalScalarComp identify the localized maps with the published comparisons.
The coefficient-inclusion composition law identifies the composite inclusion with
the direct inclusion. Finally substitute the transition and associator clauses
of stageSystem_existsUnique. The equality transports in
rationalTensorStageComparison cancel. This is precisely FamilyTower. The same
calculation covers repeated fields, identity inclusions, zero objects, and empty
schemes; it requires no additional geometric or flatness hypothesis. -/
theorem rationalTensorStageComparison_coherent :
    BilinearCoefficientDescent.FamilyTower (stageSystem l Ω W) (stageSystem l Ω W)
      (stageSystem l Ω W)
      (fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W)
      (fun {_ _} h ↦ rationalTensorStageComparison l Ω W h) := by
  have hc : (fun {E L : Index l Ω} (h : E ≤ L) ↦
      rationalTensorStageComparison l Ω W h) =
      (fun {E L} h ↦
        Functor.isoWhiskerLeft _
            (eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)) ≪≫
          rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W ≪≫
          Functor.isoWhiskerRight
            (NatIso.prod
              (eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)).symm
              (eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)).symm) _) := by
    rfl
  rw [hc]
  refine @BilinearCoefficientDescent.familyTower_of_transport (Index l Ω) inferInstance
    (Stage l Ω W) (stageCategory l Ω W)
    (fun {_ _} h ↦ transition l Ω W _ _ h)
    (fun {_ _ _} h k ↦ stageTensorAssociator l Ω W h k)
    (stageTensorFunctor l Ω W)
    (fun {_ _} h ↦ stageTensorComparison l Ω W h)
    ?_ (stageSystem l Ω W)
    (fun {E L} h ↦ (stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h) ?_
  · exact fun h k ↦ stageTensor_tower l Ω W h k
  · exact fun h k ↦ stageAssociator_heq l Ω W h k

end WeilConjectures
