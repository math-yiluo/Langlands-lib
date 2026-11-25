/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalStageLocalization
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalCommonExactness
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Common-field descent of fixed rational exceptional operations

Only the closed operations and their inclusion comparisons are outputs. Rational
operations and their scalar maps are fixed inputs. The representative-arrow law is
proved by the consumer from the transition law and naturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category CategoryTheory.ScalarLocalization.preadditive
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

section GenericTransitions
attribute [local implicit_reducible] StageSystem.Morphism.functor StageSystem.ι
  StageSystem.instCategoryPairCategory

private theorem pairFunctor_transition
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {D : I → Type*} [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) (K : C i) :
    F.functor.map ((S.transIso h).hom.app K) =
      (T.ι j).map ((F.β h).inv.app K) ≫
        (T.transIso h).hom.app ((F.Φ i).obj K) := by
  rw [StageSystem.transIso_hom_app_eq, F.functor_map_mkHom,
    StageSystem.ι_map_eq le_rfl, StageSystem.transIso_hom_app_eq,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  change (F.β le_rfl).hom.app ((S.T h).obj K) ≫
      (F.Φ j).map ((S.assoc h le_rfl).hom.app K) ≫ (F.β h).inv.app K =
    (T.T le_rfl).map ((F.β h).inv.app K) ≫
      (T.assoc h le_rfl).hom.app ((F.Φ i).obj K)
  rw [← cancel_epi ((T.T le_rfl).map ((F.β h).hom.app K))]
  rw [reassoc_of% (F.coh h le_rfl K)]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  change (T.assoc h le_rfl).hom.app ((F.Φ i).obj K) ≫ 𝟙 _ =
    (T.T le_rfl).map (𝟙 ((T.T h).obj ((F.Φ i).obj K))) ≫
      (T.assoc h le_rfl).hom.app ((F.Φ i).obj K)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

private theorem pairFunctor_transition_inv
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {D : I → Type*} [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) (K : C i) :
    F.functor.map ((S.transIso h).inv.app K) =
      (T.transIso h).inv.app ((F.Φ i).obj K) ≫
        (T.ι j).map ((F.β h).hom.app K) := by
  apply (cancel_mono (F.functor.map ((S.transIso h).hom.app K))).1
  rw [← F.functor.map_comp, Iso.inv_hom_id_app, F.functor.map_id,
    pairFunctor_transition]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  change 𝟙 _ = (T.transIso h).inv.app ((F.Φ i).obj K) ≫
    (T.ι j).map (𝟙 ((T.T h).obj ((F.Φ i).obj K))) ≫
      (T.transIso h).hom.app ((F.Φ i).obj K)
  erw [(T.ι j).map_id, Category.id_comp, Iso.inv_hom_id_app]

private theorem pairFunctor_cast_transition_inv
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {D : I → Type*} [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) {U : C i ⥤ C j} {V : D i ⥤ D j}
    (hU : S.T h = U) (hV : T.T h = V)
    (q : F.Φ i ⋙ V ≅ U ⋙ F.Φ j)
    (hq : F.β h = commonComparisonCast hU hV q) (K : C i) :
    F.functor.map
        ((eqToIso (congrArg (fun H ↦ H ⋙ S.ι j) hU.symm) ≪≫ S.transIso h).inv.app K) =
      (eqToIso (congrArg (fun H ↦ H ⋙ T.ι j) hV.symm) ≪≫ T.transIso h).inv.app
          ((F.Φ i).obj K) ≫
        (T.ι j).map (q.hom.app K) := by
  subst U V
  change F.β h = q at hq
  subst q
  simpa using pairFunctor_transition_inv F h K

end GenericTransitions

private theorem adjunctionAdditive
    {U V : Type*} [Category U] [Category V]
    [Preadditive U] [Preadditive V] [Limits.HasBinaryProducts V]
    {F : U ⥤ V} {G : V ⥤ U} (a : F ⊣ G) :
    F.Additive ∧ G.Additive := by
  let : G.IsRightAdjoint := a.isRightAdjoint
  have : G.Additive := CategoryTheory.Functor.additive_of_preserves_binary_products G
  exact ⟨a.left_adjoint_additive, inferInstance⟩

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Closed operations descending the supplied rational family, with its transition law.
No rational operation or scalar comparison is chosen again by this record.
Source: Zheng, Construction 6.6; coefficient construction step 5, common-field part
(blueprint: lem-sf-common-stage-descent-fixed-rational). -/
structure CommonStageAssembly
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (P : RationalStageAssembly.{u, v} l Ω D hl A) where
  operation (c : Compactification f) : Operation.{u, v} l Ω X Y .closed
  comparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    CounitFieldComparison.{u, v} l Ω (P.operation c (commonField.{u, v} l Ω i)) (operation c)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  normalized (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((comparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((P.operation c (commonField.{u, v} l Ω i)).F.obj K)))
  shiftX (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (comparison c i).shiftX = (comparison d i).shiftX
  shiftY (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (comparison c i).shiftY = (comparison d i).shiftY
  transition (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (comparison c i).q.hom.app K ≫
        (operation c).F.map ((commonTransition.{u, v} l Ω X i j h).inv.app K) =
      (commonTransition.{u, v} l Ω Y i j h).inv.app
          ((P.operation c (commonField.{u, v} l Ω i)).F.obj K) ≫
        (commonInclusion.{u, v} l Ω Y j).map
          ((P.scalar c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app K) ≫
        (comparison c j).q.hom.app
          ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).obj K)

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage

/-- Descend a fixed normalized rational family to the literal common-field pair category.
Only closed operations and inclusion comparisons are constructed here. In particular,
this does not assert the rational-localization existence theorem.
Source: Zheng, Construction 6.6; `lem-sf-field-stage-completion`, step 4
(blueprint: lem-sf-common-stage-descent-fixed-rational).

Proof: use `P.action`, `P.scalar_normalized`, and the residue-Tor equality to identify
all rational scalar comparisons with localizations of the supplied integral comparisons.
The proper/open coefficient projection cocycle and the tensor unit normalization prove
their balanced composition and identity laws; the counit equations give the same laws
for right adjoints by transposition. At each common finite coefficient field take exactly
`P.operation` as stage functor. The published scalar transitions, tensor associators and
unitors form the actual stage systems. Their cocycle gives morphisms of these systems
for both adjoints. Apply coherent-pair functor descent: a pair (E,K) goes to (E,F_E K),
and a representative at a common stage is conjugated by the scalar q comparisons.
This preserves identity, composition and addition, and is unchanged by enlargement.
Descend each stage adjunction Hom bijection and its inverse at one common field. The
mate unit and counit equations make these maps compatible with enlargement. Naturality
and the two triangles hold on representatives, and hence on their quotient Hom groups.
They give the closed adjunction. Descend the stage shift isomorphisms; distinguished
triangles are represented at finite stages, so both closed functors are exact. The
units and counits commute with shifts already at each stage. Choose inclusion shifts
from the endpoint coefficient functors, independently of compactification. The left
inclusion comparison is the identity on the literal pair object, and the right one is
its invertible counit transpose. Finally the quotient functor's formula on an inverse
transition gives the displayed transition equation. No absolute separatedness is used;
identity field extensions use the tensor unit and empty schemes give zero functors. -/
theorem exists_common_stage_descent
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (P : RationalStageAssembly.{u, v} l Ω D hl A) :
    Nonempty (CommonStageAssembly.{u, v} l Ω D hl A P) := by
  obtain ⟨S⟩ := exists_rational_common_exact_shifts l Ω D hl A P
  have additive (c : Compactification f) :=
    adjunctionAdditive (rationalCommonAdjunction A P c)
  let operation (c : Compactification f) : Operation.{u, v} l Ω X Y .closed :=
    { F := (rationalCommonLeft A P c).functor
      G := (rationalCommonRight A P c).functor
      adjunction := rationalCommonAdjunction A P c
      leftAdditive := (additive c).1
      rightAdditive := (additive c).2
      leftShift := S.leftShift c
      rightShift := S.rightShift c
      leftExact := S.leftExact c
      rightExact := S.rightExact c
      unitShift := S.unitShift c
      counitShift := S.counitShift c }
  let comparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
      CounitFieldComparison.{u, v} l Ω
        (P.operation c (commonField.{u, v} l Ω i)) (operation c)
        (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i) := by
    letI := S.inclusionX i
    letI := S.inclusionY i
    letI : (operation c).F.CommShift ℤ := S.leftShift c
    letI : (operation c).G.CommShift ℤ := S.rightShift c
    exact {
      shiftX := S.inclusionX i
      shiftY := S.inclusionY i
      comparison :=
        { q := ((rationalCommonLeft A P c).ιCompFunctorIso i).symm
          b := ((rationalCommonRight A P c).ιCompFunctorIso i).symm
          counit := by
            intro M
            change 𝟙 _ ≫ (rationalCommonLeft A P c).functor.map (𝟙 _) ≫
                (rationalCommonAdjunction A P c).counit.app
                  (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).obj M) =
              ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).map
                ((rationalCommonFiniteAdjunction A P c i).counit.app M)
            erw [(rationalCommonLeft A P c).functor.map_id, Category.id_comp,
              Category.id_comp]
            exact StageSystem.Morphism.adjunction_counit_app
              (rationalCommonLeft A P c) (rationalCommonRight A P c)
              (fun j ↦ rationalCommonFiniteAdjunction A P c j)
              (rationalCommonUnit A P c) (rationalCommonCounit A P c)
              (fun _ ↦ rfl) (fun _ ↦ rfl)
              ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i |>.obj M)
          qShift := S.qShift c i
          bShift := S.bShift c i } }
  refine ⟨{
    operation := operation
    comparison := comparison
    normalized := ?_
    shiftX := ?_
    shiftY := ?_
    transition := ?_ }⟩
  · intro c i K
    exact HEq.rfl
  · intro c d i
    rfl
  · intro c d i
    rfl
  · intro c i j h K
    change 𝟙 _ ≫ (rationalCommonLeft A P c).functor.map
        ((commonTransition.{u, v} l Ω X i j h).inv.app K) =
      (commonTransition.{u, v} l Ω Y i j h).inv.app
          ((P.operation c (commonField.{u, v} l Ω i)).F.obj K) ≫
        (commonInclusion.{u, v} l Ω Y j).map
          ((rationalCommonRawQ A P c h).hom.app K) ≫
        𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact pairFunctor_cast_transition_inv (rationalCommonLeft A P c) h
      (commonStageTransition_eq l Ω X h) (commonStageTransition_eq l Ω Y h)
      (rationalCommonRawQ A P c h) rfl K

end WeilConjectures.ConstructibleExceptionalCoefficients
