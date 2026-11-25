/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! # Common-stage coefficient arrows under pullback

Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-common-stage-integral-scalar-arrow)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  integralDerivedPullback commonStageDerivedPullback rationalDerivedPullback
  rationalPullbackScalarComparison integralPullbackScalarComparison

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

attribute [local implicit_reducible] StageSystem.ι StageSystem.Morphism.functor
  StageSystem.instCategoryPairCategory GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory

private theorem transition_transport_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : C ⥤ D) {TX TX' : B ⥤ D} {TY TY' : A ⥤ C}
    (eX : TX = TX') (eY : TY = TY') (α : F ⋙ TX' ≅ TY' ⋙ G) (K : A) :
    HEq ((Functor.isoWhiskerLeft F (eqToIso eX) ≪≫ α ≪≫
      Functor.isoWhiskerRight (eqToIso eY).symm G).hom.app K) (α.hom.app K) := by
  subst TX' TY'
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

private theorem isoToStage_heq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    {A B : S.PairCategory} (e : A = B) {j : I}
    (hA : A.stage ≤ j) (hB : B.stage ≤ j) :
    HEq (S.isoToStage A hA).hom (S.isoToStage B hB).hom := by
  subst B
  rfl

private theorem map_isoToStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    (X : S.PairCategory) {j : I} (h : X.stage ≤ j) :
    F.functor.map (S.isoToStage X h).hom =
      (T.isoToStage (F.functor.obj X) h).hom ≫
        (T.ι j).map ((F.β h).hom.app X.obj) := by
  simp only [StageSystem.isoToStage, StageSystem.Morphism.functor_map_mkHom,
    StageSystem.ι_map_eq le_rfl, StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  simp only [StageSystem.Morphism.mapAt]
  change (F.β h).hom.app X.obj ≫
      (F.Φ j).map ((S.assoc h (le_refl j)).inv.app X.obj) ≫
      (F.β (le_refl j)).inv.app ((S.T h).obj X.obj) =
    (T.assoc h (le_refl j)).inv.app ((F.Φ X.stage).obj X.obj) ≫
      (T.T (le_refl j)).map ((F.β h).hom.app X.obj)
  apply (cancel_mono ((T.T (le_refl j)).map ((F.β h).inv.app X.obj))).mp
  have hc := congrArg (fun q ↦ (F.β h).hom.app X.obj ≫ q)
    (F.coh_inv h (le_refl j) X.obj)
  simpa [Category.assoc, ← Functor.map_comp] using hc

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (eA : A = A') (eB : B = B') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A' B'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

private theorem stageScalarArrow_heq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) {x : C i} {y : C j} {u : D i} {v w : D j}
    (eY : (S.T h).obj x = y) (eX : (T.T h).obj u = v)
    (hobj : (F.Φ i).obj x = u) (hobjL : (F.Φ j).obj y = w)
    {f : v ⟶ w} (hβ : HEq ((F.β h).hom.app x) f) :
    HEq (F.functor.map
      ((S.isoToStage ((S.ι i).obj x) h).hom ≫ (S.ι j).map (eqToHom eY)))
      (((T.isoToStage ((T.ι i).obj u) h).hom ≫ (T.ι j).map (eqToHom eX)) ≫
        (T.ι j).map f) := by
  subst u y v w
  have hf := eq_of_heq hβ
  subst f
  simp only [eqToHom_refl, _root_.CategoryTheory.Functor.map_id, Category.comp_id]
  rw [map_isoToStage]
  rfl

-- Stage descent transports several dependent category presentations.
/-- Pullback of a literal coefficient arrow is the localized integral scalar map,
with the prescribed endpoint transports.
Source: BS Remark 6.8.15; normalized common-stage pullback and rational scalar descent.
(blueprint: lem-sf-common-stage-integral-scalar-arrow).

Proof: use normalized stage-system descent. A stage morphism maps isoToStage to
the target isoToStage followed by its transition comparison. That comparison
is the rational scalar comparison, conjugated by the recorded transition equalities.
Its integral representative is the prescribed integral scalar comparison.
Apply the equality of the localized pullback objects and the two given stage
identifications to align endpoints. Heterogeneous composition then gives the arrow
formula, including the endpoint transports. -/
theorem commonStageIntegralScalarArrow (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (eY : (((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l Ω E) Y).obj K)).toStage h) =
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).obj
        ((integralTransition l Ω Y E L h).obj K))
    (eX : (((inclusion (l := l) (Ω := Ω) (Y := X) E).obj
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l Ω E) X).obj
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K))).toStage h) =
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
        ((integralTransition l Ω X E L h).obj
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K))) :
    HEq ((commonStageDerivedPullback l Ω g).map
      (((stageSystem l Ω Y).isoToStage
        ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l Ω E) Y).obj K)) h).hom ≫
      (inclusion (l := l) (Ω := Ω) (Y := Y) L).map (eqToHom eY)))
      ((((stageSystem l Ω X).isoToStage
        ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l Ω E) X).obj
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K))) h).hom ≫
      (inclusion (l := l) (Ω := Ω) (Y := X) L).map (eqToHom eX)) ≫
        (inclusion (l := l) (Ω := Ω) (Y := X) L).map
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
            (integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω L)
              (coefficientInclusion l Ω E L h) g K).hom)) := by
  obtain ⟨hc, he⟩ := commonStagePullbackNormalizedDescent l Ω g
  rw [he]
  have hobj :
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K) =
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K) := by
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      (Coefficient.{u} l Ω E) g).exists.choose_spec.2.1 _
  have hobjL :
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).obj
          ((integralTransition l Ω Y E L h).obj K)) =
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
        ((constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).obj
          ((integralTransition l Ω Y E L h).obj K)) := by
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      (Coefficient.{u} l Ω L) g).exists.choose_spec.2.1 _
  have hβ : HEq
      ((commonStagePullbackTransition l Ω g h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
        (integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) g K).hom) := by
    dsimp only [commonStagePullbackTransition, operationStageTransitionIso]
    apply HEq.trans (transition_transport_heq
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) g)
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) g)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l
        Ω X).exists.choose_spec.1 E L h)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l
        Ω Y).exists.choose_spec.1 E L h)
      (rationalPullbackScalarComparison l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g) _)
    change HEq ((rationalPullbackScalarComparison l
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) g).hom.app _) _
    unfold rationalPullbackScalarComparison
    exact ((rationalPullbackScalarComparison_existsUnique l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g).exists.choose_spec _)
  exact stageScalarArrow_heq ⟨_, _, hc⟩ h eY eX hobj hobjL hβ

end WeilConjectures.AdicQbarRealization
