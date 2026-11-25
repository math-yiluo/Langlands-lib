/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalStageLocalization
public import WeilConjectures.CategoryTheory.StageSystem.Morphism.StageSystemAdjunction
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalScalarComposition

/-! # The rational scalar tower law and its explicit unshifted adjunction descent

Source: Zheng, Construction 6.6; common-field descent, steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  CategoryTheory.ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  WeilConjectures.sfRationalScalarExtension WeilConjectures.sfRationalConstructibleLocalization
  WeilConjectures.sfRationalScalarComp
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.scalarAssociator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance 2000] Shrink.instField
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace ExceptionalCommonMate
universe w u₁ v₁ u₂ v₂
variable {I : Type w} [Preorder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  {S : StageSystem C} {T : StageSystem D} (L : S.Morphism T)
  (R : ∀ i, D i ⥤ C i) (a : ∀ i, L.Φ i ⊣ R i)
  (b : ∀ {i j : I} (h : i ≤ j), R i ⋙ S.T h ≅ T.T h ⋙ R j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : D i),
    (L.Φ j).map ((b h).hom.app K) ≫ (a j).counit.app ((T.T h).obj K) =
      (L.β h).inv.app ((R i).obj K) ≫ (T.T h).map ((a i).counit.app K))

include hb

/-- Constructive counit-transpose calculus for a coherent stage family.
Source: Zheng, Construction 6.6, common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
theorem unitEquation {i j : I} (h : i ≤ j) (K : C i) :
    (S.T h).map ((a i).unit.app K) ≫ (b h).hom.app ((L.Φ i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R j).map ((L.β h).inv.app K) := by
  apply ((a j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hb]
  have hn := (L.β h).inv.naturality ((a i).unit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at hn
  rw [reassoc_of% hn]
  rw [← (T.T h).map_comp, (a i).left_triangle_components, (T.T h).map_id]
  simp only [Category.comp_id]
  rw [(a j).counit_naturality, ← Category.assoc,
    (a j).left_triangle_components ((S.T h).obj K)]
  exact (Category.id_comp _).symm

/-- Constructive counit-transpose calculus for a coherent stage family.
Source: Zheng, Construction 6.6, common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
theorem tower {i j k : I} (h : i ≤ j) (h' : j ≤ k) (K : D i) :
    (S.T h').map ((b h).hom.app K) ≫ (b h').hom.app ((T.T h).obj K) ≫
      (R k).map ((T.assoc h h').hom.app K) =
    (S.assoc h h').hom.app ((R i).obj K) ≫ (b (h.trans h')).hom.app K := by
  apply ((a k).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [(a k).counit_naturality, reassoc_of% (hb h' ((T.T h).obj K))]
  have hn := (L.β h').inv.naturality ((b h).hom.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at hn
  rw [reassoc_of% hn]
  rw [← (T.T h').map_comp_assoc, hb, (T.T h').map_comp]
  have ht := (T.assoc h h').hom.naturality ((a i).counit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at ht
  simp only [Category.assoc]
  rw [ht]
  have hc := L.coh_inv h h' ((R i).obj K)
  have hc' : (L.β h').inv.app ((S.T h).obj ((R i).obj K)) ≫
      (T.T h').map ((L.β h).inv.app ((R i).obj K)) ≫
      (T.assoc h h').hom.app ((L.Φ i).obj ((R i).obj K)) =
      (L.Φ k).map ((S.assoc h h').hom.app ((R i).obj K)) ≫
        (L.β (h.trans h')).inv.app ((R i).obj K) := by
    rw [← cancel_epi ((L.Φ k).map ((S.assoc h h').inv.app ((R i).obj K)))]
    rw [reassoc_of% hc]
    simp only [Iso.inv_hom_id_app, Category.comp_id,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hc', hb]

/-- Constructive counit-transpose calculus for a coherent stage family.
Source: Zheng, Construction 6.6, common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rightSystem : T.Morphism S where
  Φ := R
  β := b
  coh := tower L R a b hb

/-- Constructive counit-transpose calculus for a coherent stage family.
Source: Zheng, Construction 6.6, common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def unitFamily : StageSystem.Morphism.Hom (StageSystem.Morphism.id S)
    (L.comp (rightSystem L R a b hb)) where
  τ i := (a i).unit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (S.T h).map ((a i).unit.app K) ≫
      ((b h).hom.app ((L.Φ i).obj K) ≫ (R j).map ((L.β h).hom.app K)) =
      𝟙 _ ≫ (a j).unit.app ((S.T h).obj K)
    rw [Category.id_comp]
    rw [← Category.assoc, unitEquation L R a b hb, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    change (a j).unit.app ((S.T h).obj K) ≫
      (R j).map (𝟙 ((L.Φ j).obj ((S.T h).obj K))) = _
    rw [(R j).map_id]
    exact Category.comp_id _

/-- Constructive counit-transpose calculus for a coherent stage family.
Source: Zheng, Construction 6.6, common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def counitFamily : StageSystem.Morphism.Hom
    ((rightSystem L R a b hb).comp L) (StageSystem.Morphism.id T) where
  τ i := (a i).counit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (T.T h).map ((a i).counit.app K) ≫ 𝟙 _ =
      ((L.β h).hom.app ((R i).obj K) ≫ (L.Φ j).map ((b h).hom.app K)) ≫
        (a j).counit.app ((T.T h).obj K)
    rw [Category.comp_id, Category.assoc, hb, Iso.hom_inv_id_app_assoc]

end ExceptionalCommonMate
end WeilConjectures

namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Equality of the existing stage transition with the published rational scalar functor.
Source: the common-field coefficient construction
(blueprint: lem-sf-rational-common-scalar-coherence). -/
theorem commonStageTransition_eq (T : Scheme.{max u v})
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).T h =
      rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) T :=
  (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω T).exists.choose_spec.1
    i j h

/-- Transport a scalar comparison across equal endpoint functors.
Source: coefficient-stage identifications
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def commonComparisonCast
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {TX TX' : C ⥤ C'} {TY TY' : D ⥤ D'}
    (hx : TX = TX') (hy : TY = TY') (q : F ⋙ TY' ≅ TX' ⋙ F') :
    F ⋙ TY ≅ TX ⋙ F' := by
  subst TX' TY'
  exact q

/-- Transporting both comparisons preserves their counit equation.
Source: coefficient-stage identifications
(blueprint: lem-sf-rational-common-scalar-coherence). -/
theorem commonComparisonCast_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {TX TX' : C ⥤ C'} {TY TY' : D ⥤ D'}
    (hx : TX = TX') (hy : TY = TY') (a : F ⊣ G) (a' : F' ⊣ G')
    (q : F ⋙ TY' ≅ TX' ⋙ F') (b : G ⋙ TX' ≅ TY' ⋙ G')
    (hc : ∀ M, q.hom.app (G.obj M) ≫ F'.map (b.hom.app M) ≫
      a'.counit.app (TY'.obj M) = TY'.map (a.counit.app M)) (M : D) :
    (commonComparisonCast hx hy q).hom.app (G.obj M) ≫
        F'.map ((commonComparisonCast hy hx b).hom.app M) ≫
        a'.counit.app (TY.obj M) = TY.map (a.counit.app M) := by
  subst TX' TY'
  exact hc M

private theorem cast_coherence
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    {X₀₁ X₀₁' : C₀ ⥤ C₁} {X₁₂ X₁₂' : C₁ ⥤ C₂} {X₀₂ X₀₂' : C₀ ⥤ C₂}
    {Y₀₁ Y₀₁' : D₀ ⥤ D₁} {Y₁₂ Y₁₂' : D₁ ⥤ D₂} {Y₀₂ Y₀₂' : D₀ ⥤ D₂}
    (hx₀₁ : X₀₁ = X₀₁') (hx₁₂ : X₁₂ = X₁₂') (hx₀₂ : X₀₂ = X₀₂')
    (hy₀₁ : Y₀₁ = Y₀₁') (hy₁₂ : Y₁₂ = Y₁₂') (hy₀₂ : Y₀₂ = Y₀₂')
    (ax : X₀₁ ⋙ X₁₂ ≅ X₀₂) (ax' : X₀₁' ⋙ X₁₂' ≅ X₀₂')
    (ay : Y₀₁ ⋙ Y₁₂ ≅ Y₀₂) (ay' : Y₀₁' ⋙ Y₁₂' ≅ Y₀₂')
    (hax : HEq ax ax') (hay : HEq ay ay')
    (q₀₁ : F₀ ⋙ Y₀₁' ≅ X₀₁' ⋙ F₁) (q₁₂ : F₁ ⋙ Y₁₂' ≅ X₁₂' ⋙ F₂)
    (q₀₂ : F₀ ⋙ Y₀₂' ≅ X₀₂' ⋙ F₂)
    (hc : Functor.whiskerRight q₀₁.hom Y₁₂' ≫
      Functor.whiskerLeft X₀₁' q₁₂.hom ≫ Functor.whiskerRight ax'.hom F₂ =
      Functor.whiskerLeft F₀ ay'.hom ≫ q₀₂.hom) :
    Functor.whiskerRight (commonComparisonCast hx₀₁ hy₀₁ q₀₁).hom Y₁₂ ≫
      Functor.whiskerLeft X₀₁ (commonComparisonCast hx₁₂ hy₁₂ q₁₂).hom ≫
      Functor.whiskerRight ax.hom F₂ =
      Functor.whiskerLeft F₀ ay.hom ≫ (commonComparisonCast hx₀₂ hy₀₂ q₀₂).hom := by
  subst X₀₁' X₁₂' X₀₂' Y₀₁' Y₁₂' Y₀₂'
  cases eq_of_heq hax
  cases eq_of_heq hay
  exact hc

-- Keep equality transports folded when elaborating their component equations.
attribute [local irreducible] commonComparisonCast

variable {l Ω D hl}
variable (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
  (P : RationalStageAssembly.{u, v} l Ω D hl A)

/-- The supplied left functor, typed with the published stage categories.
Source: coefficient-stage identification
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonF (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω X i ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i := by
  have F := (P.operation c (commonField.{u, v} l Ω i)).F
  dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at F ⊢
  exact F

/-- The supplied right functor, typed with the published stage categories.
Source: coefficient-stage identification
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonG (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω X i := by
  have G := (P.operation c (commonField.{u, v} l Ω i)).G
  dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at G ⊢
  exact G

/-- The unchanged finite adjunction with the stage-category endpoint types.
Source: coefficient-stage identification
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonFiniteAdjunction (c : Compactification f)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    rationalCommonF A P c i ⊣ rationalCommonG A P c i := by
  have a := (P.operation c (commonField.{u, v} l Ω i)).adjunction
  dsimp only [rationalCommonF, rationalCommonG,
    GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at a ⊢
  exact a

attribute [local irreducible] rationalCommonF rationalCommonG rationalCommonFiniteAdjunction

/-- The supplied rational scalar q, with stage-category endpoint types.
Source: coefficient-stage identification
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonRawQ (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    rationalCommonF A P c i ⋙
        rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y ≅
      rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X ⋙
        rationalCommonF A P c j := by
  unfold rationalCommonF
  have q := (P.scalar c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q
  dsimp only [rationalCommonF, GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at q ⊢
  exact q

/-- The supplied rational scalar b, with stage-category endpoint types.
Source: coefficient-stage identification
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonRawB (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    rationalCommonG A P c i ⋙
        rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X ≅
      rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y ⋙
        rationalCommonG A P c j := by
  unfold rationalCommonG
  have b := (P.scalar c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).b
  dsimp only [rationalCommonG, GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at b ⊢
  exact b

attribute [local irreducible] rationalCommonRawQ rationalCommonRawB

/-- The supplied left scalar map, on the actual stage-system transitions.
Source: Zheng, Construction 6.6, scalar comparison
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonQ (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    (rationalCommonF A P c i) ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ⋙
        (rationalCommonF A P c j) :=
  -- Fix all endpoint types before elaborating the scalar equality transports.
  @commonComparisonCast
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X i)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X j)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y j)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X i)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y i)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X j)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y j)
    (rationalCommonF A P c i) (rationalCommonF A P c j)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
    (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h)
    (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y)
    (commonStageTransition_eq l Ω X h) (commonStageTransition_eq l Ω Y h)
    (rationalCommonRawQ A P c h)

/-- The supplied right scalar map, on the actual stage-system transitions.
Source: Zheng, Construction 6.6, scalar comparison
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonB (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    (rationalCommonG A P c i) ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h ⋙
        (rationalCommonG A P c j) :=
  -- Fix all endpoint types before elaborating the scalar equality transports.
  @commonComparisonCast
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X i)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y j)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X j)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y i)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X i)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y j)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X j)
    (rationalCommonG A P c i) (rationalCommonG A P c j)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h)
    (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
    (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X)
    (commonStageTransition_eq l Ω Y h) (commonStageTransition_eq l Ω X h)
    (rationalCommonRawB A P c h)

private theorem rationalCommon_raw_coherence (c : Compactification f)
    (E L M : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (k : E.carrier →ₐ[Padic l] M.carrier) (hk : j.comp i = k)
    (K : C.{u, v} l Ω X (.rational E)) :
    (rationalScalar.{u, v} l Ω L M j Y).map ((P.scalar c E L i).q.hom.app K) ≫
        (P.scalar c L M j).q.hom.app ((rationalScalar.{u, v} l Ω E L i X).obj K) ≫
        (P.operation c M).F.map
          ((GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
            E.carrier L.carrier M.carrier i j k hk X).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
          E.carrier L.carrier M.carrier i j k hk Y).hom.app
          ((P.operation c E).F.obj K) ≫ (P.scalar c E M k).q.hom.app K := by
  subst k
  simpa only [GeneralAlgebraicallyClosedCoefficients.scalarAssociator, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_refl, NatTrans.id_app,
    Category.comp_id] using ring_stage_rational_left_composition l Ω D hl A P c E L M i j K

private theorem rationalCommon_raw_natural (c : Compactification f)
    (E L M : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (k : E.carrier →ₐ[Padic l] M.carrier) (hk : j.comp i = k) :
    Functor.whiskerRight (P.scalar c E L i).q.hom
        (rationalScalar.{u, v} l Ω L M j Y) ≫
      Functor.whiskerLeft (rationalScalar.{u, v} l Ω E L i X)
        (P.scalar c L M j).q.hom ≫
      Functor.whiskerRight (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
        E.carrier L.carrier M.carrier i j k hk X).hom (P.operation c M).F =
      Functor.whiskerLeft (P.operation c E).F
        (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
          E.carrier L.carrier M.carrier i j k hk Y).hom ≫
        (P.scalar c E M k).q.hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    rationalCommon_raw_coherence A P c E L M i j k hk K

private theorem commonStageAssociator_heq (T : Scheme.{max u v})
    {i j k : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) (h' : j ≤ k) :
    HEq ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).assoc h h')
      (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
        (commonField.{u, v} l Ω i).carrier (commonField.{u, v} l Ω j).carrier
        (commonField.{u, v} l Ω k).carrier
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h')
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i k (h.trans h'))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 i j k h h') T) :=
  ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω T).exists.choose_spec.2
    i j k h h').trans
    (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
      l Ω T i j k h h').exists.choose_spec

private theorem rationalCommon_stage_natural (c : Compactification f)
    {i j k : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) (h' : j ≤ k) :
    Functor.whiskerRight (rationalCommonRawQ A P c h).hom
        (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω j) (commonField.{u, v} l Ω k)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h') Y) ≫
      Functor.whiskerLeft
        (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X)
        (rationalCommonRawQ A P c h').hom ≫
      Functor.whiskerRight (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
        (commonField.{u, v} l Ω i).carrier (commonField.{u, v} l Ω j).carrier
        (commonField.{u, v} l Ω k).carrier
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h')
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i k (h.trans h'))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 i j k h h') X).hom
        (rationalCommonF A P c k) =
      Functor.whiskerLeft (rationalCommonF A P c i)
        (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
          (commonField.{u, v} l Ω i).carrier (commonField.{u, v} l Ω j).carrier
          (commonField.{u, v} l Ω k).carrier
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h')
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i k (h.trans h'))
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 i j k h h') Y).hom ≫
        (rationalCommonRawQ A P c (h.trans h')).hom := by
  unfold rationalCommonRawQ rationalCommonF
  have hc := rationalCommon_raw_natural A P c (commonField.{u, v} l Ω i)
    (commonField.{u, v} l Ω j) (commonField.{u, v} l Ω k)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h')
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i k (h.trans h'))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 i j k h h')
  dsimp only [rationalCommonF, rationalCommonRawQ,
    GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at hc ⊢
  exact hc

private theorem rationalCommon_stage_counit (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i) :
    (rationalCommonRawQ A P c h).hom.app ((rationalCommonG A P c i).obj M) ≫
      (rationalCommonF A P c j).map ((rationalCommonRawB A P c h).hom.app M) ≫
      (rationalCommonFiniteAdjunction A P c j).counit.app
        ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y).obj M) =
      (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y).map
        ((rationalCommonFiniteAdjunction A P c i).counit.app M) := by
  unfold rationalCommonRawQ rationalCommonRawB rationalCommonFiniteAdjunction
    rationalCommonF rationalCommonG
  let d := P.scalar c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
  let := d.shiftX
  let := d.shiftY
  have hd := d.comparison.counit M
  dsimp only [rationalCommonF, rationalCommonG, rationalCommonFiniteAdjunction,
    rationalCommonRawQ, rationalCommonRawB,
    GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at hd ⊢
  exact hd

attribute [local irreducible] rationalCommonQ rationalCommonB

/-- The normalized rational scalar maps obey the balanced tower equation.
Source: Zheng, Construction 6.6; common-field descent step 1
(blueprint: lem-sf-rational-common-scalar-coherence).

Proof: residue Tor identifies the finite-Tor integral subcategory with all integral
constructibles. Every rational object is therefore the raw localization of an integral
object. On such objects P.scalar_normalized identifies each q with the localization
of A.comparison. Apply A.comparison_normalized and its faithful ambient inclusion:
the proper coefficient projection cocycle and the open tensor normalization identify
the two composites with the same tensor-unit mate. The normalized integral scalar
associator agrees, under A.integralScalar_normalized, with the published completed
tensor associator. Localize this equality. Naturality gives its equality on all
rational arrows. The stage-system specification transports the scalar associator
and transitions to the displayed ones. Identity extensions use coefficient-unit
multiplication, so repeated stages are included. No right-adjoint or shift descent
is asserted by this theorem. -/
theorem rational_common_scalar_coherence (c : Compactification f) :
    StageSystem.pairFunctorCoherent
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y)
      (fun i ↦ (rationalCommonF A P c i))
      (rationalCommonQ A P c) := by
  intro i j k h h' K
  let E : FieldStage.{max u v} l := commonField.{u, v} l Ω i
  let L : FieldStage.{max u v} l := commonField.{u, v} l Ω j
  let M : FieldStage.{max u v} l := commonField.{u, v} l Ω k
  let ij := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h
  let jk := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h'
  let ik := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i k (h.trans h')
  have hik : jk.comp ij = ik :=
    (AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 i j k h h'
  have hx := commonStageAssociator_heq (l := l) (Ω := Ω) X h h'
  have hy := commonStageAssociator_heq (l := l) (Ω := Ω) Y h h'
  have hc := rationalCommon_stage_natural A P c h h'
  have hx₀₁ := commonStageTransition_eq l Ω X h
  have hx₁₂ := commonStageTransition_eq l Ω X h'
  have hx₀₂ := commonStageTransition_eq l Ω X (h.trans h')
  have hy₀₁ := commonStageTransition_eq l Ω Y h
  have hy₁₂ := commonStageTransition_eq l Ω Y h'
  have hy₀₂ := commonStageTransition_eq l Ω Y (h.trans h')
  let ax := (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).assoc h h'
  let ay := (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).assoc h h'
  let ax' := GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
    E.carrier L.carrier M.carrier ij jk ik hik X
  let ay' := GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
    E.carrier L.carrier M.carrier ij jk ik hik Y
  let q₀₁ := rationalCommonRawQ A P c h
  let q₁₂ := rationalCommonRawQ A P c h'
  let q₀₂ := rationalCommonRawQ A P c (h.trans h')
  have hh := cast_coherence (rationalCommonF A P c i) (rationalCommonF A P c j)
    (rationalCommonF A P c k)
    hx₀₁ hx₁₂ hx₀₂ hy₀₁ hy₁₂ hy₀₂ ax ax' ay ay' hx hy q₀₁ q₁₂ q₀₂ hc
  have hn := NatTrans.congr_app hh K
  simpa only [rationalCommonQ, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] using hn

/-- The left functor family with exactly the supplied rational scalar maps.
Source: Zheng, Construction 6.6, common-field descent step 2
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonLeft (c : Compactification f) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y) where
  Φ i := (rationalCommonF A P c i)
  β := rationalCommonQ A P c
  coh := rational_common_scalar_coherence A P c

/-- The scalar counit equation survives the endpoint identifications.
Source: Zheng, Construction 6.6, common-field descent step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
theorem rationalCommon_counit (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i) :
    (rationalCommonQ A P c h).hom.app
        ((rationalCommonG A P c i).obj M) ≫
      (rationalCommonF A P c j).map
        ((rationalCommonB A P c h).hom.app M) ≫
      (rationalCommonFiniteAdjunction A P c j).counit.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).obj M) =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).map
        ((rationalCommonFiniteAdjunction A P c i).counit.app M) := by
  unfold rationalCommonQ rationalCommonB
  exact @commonComparisonCast_counit
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X i)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X j)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y j)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X i)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y i)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X j)
    (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y j)
    (rationalCommonF A P c i) (rationalCommonG A P c i)
    (rationalCommonF A P c j) (rationalCommonG A P c j)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
    (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h)
    (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y)
    (commonStageTransition_eq l Ω X h) (commonStageTransition_eq l Ω Y h)
    (rationalCommonFiniteAdjunction A P c i) (rationalCommonFiniteAdjunction A P c j)
    (rationalCommonRawQ A P c h) (rationalCommonRawB A P c h)
    (rationalCommon_stage_counit A P c h) M

/-- The inverse-q form of the rational scalar counit equation.
Source: common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
theorem rationalCommon_transpose (c : Compactification f)
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y i) :
    (rationalCommonF A P c j).map
        ((rationalCommonB A P c h).hom.app M) ≫
      (rationalCommonFiniteAdjunction A P c j).counit.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).obj M) =
      (rationalCommonQ A P c h).inv.app
          ((rationalCommonG A P c i).obj M) ≫
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).map
          ((rationalCommonFiniteAdjunction A P c i).counit.app M) := by
  rw [← rationalCommon_counit A P c h M, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

/-- The right family obtained by the supplied invertible scalar counit transposes.
Source: common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonRight (c : Compactification f) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) :=
  ExceptionalCommonMate.rightSystem (rationalCommonLeft A P c)
    (fun i ↦ (rationalCommonG A P c i))
    (fun i ↦ (rationalCommonFiniteAdjunction A P c i))
    (rationalCommonB A P c) (rationalCommon_transpose A P c)

/-- The compatible family of actual rational units.
Source: common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonUnit (c : Compactification f) :
    StageSystem.Morphism.Hom
      (StageSystem.Morphism.id (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X))
      ((rationalCommonLeft A P c).comp (rationalCommonRight A P c)) :=
  ExceptionalCommonMate.unitFamily (rationalCommonLeft A P c) _
    (fun i ↦ (rationalCommonFiniteAdjunction A P c i))
    (rationalCommonB A P c) (rationalCommon_transpose A P c)

/-- The compatible family of actual rational counits.
Source: common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonCounit (c : Compactification f) :
    StageSystem.Morphism.Hom
      ((rationalCommonRight A P c).comp (rationalCommonLeft A P c))
      (StageSystem.Morphism.id (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y)) :=
  ExceptionalCommonMate.counitFamily (rationalCommonLeft A P c) _
    (fun i ↦ (rationalCommonFiniteAdjunction A P c i))
    (rationalCommonB A P c) (rationalCommon_transpose A P c)

/-- The adjunction on the literal pair categories, constructed from the finite triangles.
Source: common-field adjunction step 3
(blueprint: lem-sf-rational-common-scalar-coherence). -/
def rationalCommonAdjunction (c : Compactification f) :
    (rationalCommonLeft A P c).functor ⊣ (rationalCommonRight A P c).functor :=
  StageSystem.Morphism.adjunction (rationalCommonLeft A P c) (rationalCommonRight A P c)
    (fun i ↦ (rationalCommonFiniteAdjunction A P c i))
    (rationalCommonUnit A P c) (rationalCommonCounit A P c) (fun _ ↦ rfl) (fun _ ↦ rfl)

end WeilConjectures.ConstructibleExceptionalCoefficients
