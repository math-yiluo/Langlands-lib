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

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPointStages

import WeilConjectures.SmoothPurity.Point.PointFibreRepresentativeTransport

/-! # Descent of the point fibre on common-stage morphisms

Source: the common-stage construction of the point fibre.
(blueprint: lemma-perfect-complexes-geometric-point).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w r s

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Descend an object map and representative maps through eventual equality.
Identity and composition are checked at one common stage; representatives also
prove uniqueness, including the prescribed object equalities. -/
private theorem pointPairFunctor_existsUnique
    {I : Type r} [Preorder I] [IsDirectedOrder I]
    {C : I → Type v} [∀ i, Category.{w} (C i)] (S : StageSystem C)
    {B : Type s} [Category B] (O : S.PairCategory → B)
    (R : ∀ (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n),
      (X.toStage hX ⟶ Y.toStage hY) → (O X ⟶ O Y))
    (htr : ∀ (X Y : S.PairCategory) (n p : I)
      (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (h : n ≤ p)
      (f : X.toStage hX ⟶ Y.toStage hY),
      R X Y p (hX.trans h) (hY.trans h) (S.tr h f) = R X Y n hX hY f)
    (hid : ∀ (X : S.PairCategory) (n : I) (hX : X.stage ≤ n),
      R X X n hX hX (𝟙 _) = 𝟙 _)
    (hcomp : ∀ (X Y Z : S.PairCategory) (n : I)
      (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (hZ : Z.stage ≤ n)
      (f : X.toStage hX ⟶ Y.toStage hY) (g : Y.toStage hY ⟶ Z.toStage hZ),
      R X Z n hX hZ (f ≫ g) = R X Y n hX hY f ≫ R Y Z n hY hZ g) :
    ∃! F : S.PairCategory ⥤ B,
      (∀ X, F.obj X = O X) ∧
      (∀ (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
        (f : X.toStage hX ⟶ Y.toStage hY),
        HEq (F.map (StageSystem.PairCategory.mkHom n hX hY f)) (R X Y n hX hY f)) := by
  let m {X Y : S.PairCategory} (f : X ⟶ Y) : O X ⟶ O Y :=
    Quotient.lift (fun a : StageSystem.PairCategory.Rep X Y ↦ R X Y a.k a.hX a.hY a.u)
      (by
        intro a b hab
        obtain ⟨p, ha, hb, e⟩ := hab
        exact (htr X Y a.k p a.hX a.hY ha a.u).symm.trans
          ((congrArg (R X Y p _ _) e).trans (htr X Y b.k p b.hX b.hY hb b.u))) f
  have hm (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
      (f : X.toStage hX ⟶ Y.toStage hY) :
      m (StageSystem.PairCategory.mkHom n hX hY f) = R X Y n hX hY f := rfl
  let F : S.PairCategory ⥤ B :=
    { obj := O
      map := m
      map_id := by
        intro X
        rw [StageSystem.PairCategory.id_eq_mkHom X le_rfl, hm]
        exact hid X X.stage le_rfl
      map_comp := by
        intro X Y Z f g
        obtain ⟨n, _, hX, hY, hY', hZ, f, g, rfl, rfl⟩ :=
          StageSystem.PairCategory.exists_common_stage f g X.stage
        rw [StageSystem.PairCategory.mkHom_comp_mkHom, hm, hm, hm]
        exact hcomp X Y Z n hX hY hZ f g }
  refine ⟨F, ⟨fun _ ↦ rfl, fun X Y n hX hY f ↦ heq_of_eq (hm X Y n hX hY f)⟩, ?_⟩
  intro G hG
  refine CategoryTheory.Functor.ext hG.1 ?_
  intro X Y f
  induction f using StageSystem.PairCategory.hom_induction with
  | h n hX hY f =>
    apply (conj_eqToHom_iff_heq _ _ (hG.1 X) (hG.1 Y)).2
    exact (hG.2 X Y n hX hY f).trans (heq_of_eq (hm X Y n hX hY f).symm)

private theorem pointConjugateMap_id
    {C : Type v} [Category.{w} C] {D : Type r} [Category D]
    {B : Type s} [Category B] (F : C ⥤ D) (J : D ⥤ B)
    {X : C} {Y : D} {Z : B} (e : Y ≅ F.obj X) (k : J.obj Y ≅ Z) :
    k.inv ≫ J.map (e.hom ≫ F.map (𝟙 X) ≫ e.inv) ≫ k.hom = 𝟙 Z := by
  simp

private theorem pointConjugateMap_comp
    {C : Type v} [Category.{w} C] {D : Type r} [Category D]
    {B : Type s} [Category B] (F : C ⥤ D) (J : D ⥤ B)
    {X Y Z : C} {X' Y' Z' : D} {U V W : B}
    (a : X' ≅ F.obj X) (b : Y' ≅ F.obj Y) (c : Z' ≅ F.obj Z)
    (i : J.obj X' ≅ U) (j : J.obj Y' ≅ V) (k : J.obj Z' ≅ W)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    i.inv ≫ J.map (a.hom ≫ F.map (f ≫ g) ≫ c.inv) ≫ k.hom =
      (i.inv ≫ J.map (a.hom ≫ F.map f ≫ b.inv) ≫ j.hom) ≫
        j.inv ≫ J.map (b.hom ≫ F.map g ≫ c.inv) ≫ k.hom := by
  simp [Category.assoc]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] pointStageFibre
  pointRationalFibre pointRationalFibreScalarIso
  DerivedCategory.pointFdQbarStageComp
attribute [local irreducible] pointStageFibreScalarIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The common-stage formula uniquely defines the fourth fibre functor.
Source: blueprint order 1509, clause 4 (blueprint: lemma-perfect-complexes-geometric-point).
Proof: use the displayed object map. Every source morphism has a common-stage
representative by the recorded common-stage calculus. Send it to
pointQbarFibreRepresentative. The scalar-extension coherence of the recorded
sections comparison, and the canonical tensor towers and Shrink square, identify
the two images after any enlargement of the common field. Thus equivalent
representatives give equal maps. At a common stage, the two middle phi factors
cancel in a composite; functoriality of the rational fibre proves composition.
For the identity the inverse phi factors cancel. The object formula and the map
formula on all representatives determine the functor uniquely. -/
theorem pointQbarFibre_existsUnique :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
        DerivedCategory.PointFdQbar l Ω,
      (∀ A, F.obj A = pointQbarFibreObj D l hl Ω A) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
        (G : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ G) (hB : B.stage ≤ G)
        (f : A.toStage hA ⟶ B.toStage hB),
        HEq (F.map (StageSystem.PairCategory.mkHom G hA hB f))
          (pointQbarFibreRepresentative D l hl Ω A B G hA hB f)) := by
  apply pointPairFunctor_existsUnique
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k)))
    (pointQbarFibreObj D l hl Ω) (pointQbarFibreRepresentative D l hl Ω)
  · exact pointQbarFibreRepresentative_transport D l hl Ω
  · intro A G hA
    exact pointConjugateMap_id (pointStageFibre D l hl Ω G)
      (DerivedCategory.pointFdQbarStage l Ω G)
      ((pointStageFibreScalarIso D l hl Ω A.stage G hA).symm.app A.obj)
      ((DerivedCategory.pointFdQbarStageComp l Ω hA).app
        ((pointStageFibre D l hl Ω A.stage).obj A.obj))
  · intro A B C G hA hB hC f g
    exact pointConjugateMap_comp (pointStageFibre D l hl Ω G)
      (DerivedCategory.pointFdQbarStage l Ω G)
      ((pointStageFibreScalarIso D l hl Ω A.stage G hA).symm.app A.obj)
      ((pointStageFibreScalarIso D l hl Ω B.stage G hB).symm.app B.obj)
      ((pointStageFibreScalarIso D l hl Ω C.stage G hC).symm.app C.obj)
      ((DerivedCategory.pointFdQbarStageComp l Ω hA).app
        ((pointStageFibre D l hl Ω A.stage).obj A.obj))
      ((DerivedCategory.pointFdQbarStageComp l Ω hB).app
        ((pointStageFibre D l hl Ω B.stage).obj B.obj))
      ((DerivedCategory.pointFdQbarStageComp l Ω hC).app
        ((pointStageFibre D l hl Ω C.stage).obj C.obj)) f g

/-- Clause 4: stagewise sections, with the prescribed action on every common-stage morphism.
Together with pointFiniteFibre, pointIntegralFibre and pointRationalFibre, this is the
four-stage geometric-point fibre. Equivalence is a separate node, not assumed here.
Source: blueprint order 1509 (blueprint: lemma-perfect-complexes-geometric-point). -/
noncomputable def pointQbarFibre :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
      DerivedCategory.PointFdQbar l Ω :=
  (pointQbarFibre_existsUnique D l hl Ω).exists.choose

end WeilConjectures
