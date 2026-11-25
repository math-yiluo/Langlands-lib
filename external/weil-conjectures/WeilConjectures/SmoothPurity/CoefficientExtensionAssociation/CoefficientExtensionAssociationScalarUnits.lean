/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor

/-! # Scalar unit sections and finite evaluation

Source: Stacks 03D7 and the sequence-site construction preceding 0941.
Native target carriers keep presheaf maps and adjunction sections small while
their proved comparison lemmas retain the actual restriction-of-scalars maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace CoefficientExtensionAssociation
section BalancedUnitMap
universe c v r
@[irreducible] private def abstractUnitSection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ)
    (M : SheafOfModules.{r} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (F.obj M).val.obj U := (adj.unit.app M).val.app U x

private theorem abstractUnitSection_heq
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ)
    (M : SheafOfModules.{r} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    HEq (abstractUnitSection φ adj M U x) ((adj.unit.app M).val.app U x) := by
  unfold abstractUnitSection
  rfl

@[irreducible] private def presheafMapSection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} (M : SheafOfModules.{r} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) : M.val.obj V := M.val.map f x

private structure AdjunctionUnitNaturality
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ) : Prop where
  naturality : ∀ (M : SheafOfModules.{r} R) {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U),
    HEq (presheafMapSection (F.obj M) f (abstractUnitSection φ adj M U x))
      (abstractUnitSection φ adj M V (presheafMapSection M f x))

private theorem adjunctionUnitNaturality
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ) : AdjunctionUnitNaturality φ adj := by
  constructor
  intro M U V f x
  unfold abstractUnitSection presheafMapSection
  exact heq_of_eq (PresheafOfModules.naturality_apply (adj.unit.app M).val f x).symm

end BalancedUnitMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  integralScalarReduction completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SemilinearSections.systemMap
  scalarReductionExtension scalarReductionExistence coefficientOrdinaryQuotient
  coefficientQuotientNatTrans coefficientOrdinaryQuotientComponent

private theorem evaluation_unit
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    ((ρ n).hom.app N).val.app U
      ((A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x) =
    (((A.levels n).ordinaryAdjunction.unit.app
      ((coefficientSequenceEvaluation l E W n).obj N)).val.app U x) := by
  unfold IsCoefficientScalarEvaluationUnit at hρ
  have hx := congrArg (fun f ↦ f.val.app U x) (hρ n N)
  have hd := (SemilinearSections.restrictionEvaluation_existsUnique.{t + 1, t,
    max (t + 1) u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W) n).exists.choose_spec
        (A.scalar.model.E.obj N) U
  have hy := congrFun (eq_of_heq hd)
    (((coefficientSequenceEvaluation l E W n).map
      (A.scalar.ordinaryAdjunction.unit.app N)).val.app U x)
  exact (congrArg
    (fun y ↦ ((SemilinearSections.res (integralScalarQuotientSheafMap l E L ι W n)).map
      ((ρ n).hom.app N)).val.app U y) hy).symm.trans hx

private theorem iso_hom_inv_section
    {R : Sheaf (Scheme.ProEt.topology W) RingCat.{max u (t + 1)}}
    {X Y : SheafOfModules.{max u (t + 1)} R} (e : X ≅ Y)
    (U : W.ProEtᵒᵖ) (x : X.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x :=
  congrArg (fun f ↦ f.val.app U x) e.hom_inv_id

private theorem iso_inv_hom_section
    {R : Sheaf (Scheme.ProEt.topology W) RingCat.{max u (t + 1)}}
    {X Y : SheafOfModules.{max u (t + 1)} R} (e : X ≅ Y)
    (U : W.ProEtᵒᵖ) (y : Y.val.obj U) :
    e.hom.val.app U (e.inv.val.app U y) = y :=
  congrArg (fun f ↦ f.val.app U y) e.inv_hom_id

/-- The unit section of finite scalar extension, in its native target module.
Source: Stacks 03D7. -/
@[irreducible] def finiteScalarUnitSection
    (A : CoefficientExtensionSystems l E L ι W)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    ((A.levels n).model.E.obj ((coefficientSequenceEvaluation l E W n).obj N)).val.obj U :=
  ((A.levels n).ordinaryAdjunction.unit.app
    ((coefficientSequenceEvaluation l E W n).obj N)).val.app U x

/-- The finite scalar unit transported back through the supplied evaluation isomorphism.
Source: Stacks 03D7 and the ordinary evaluation unit equation. -/
@[irreducible] def evaluatedUnitSection
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    ((coefficientSequenceEvaluation l L W n).obj (A.scalar.model.E.obj N)).val.obj U :=
  ((ρ n).inv.app N).val.app U (finiteScalarUnitSection l E L ι W A N n U x)

private theorem evaluatedUnitSection_hom
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    ((ρ n).hom.app N).val.app U (evaluatedUnitSection l E L ι W A ρ N n U x) =
      finiteScalarUnitSection l E L ι W A N n U x := by
  unfold evaluatedUnitSection
  exact iso_inv_hom_section W ((ρ n).app N) U _

private theorem evaluatedUnitSection_raw
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq (evaluatedUnitSection l E L ι W A ρ N n U x)
      ((A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x) := by
  have hx := congrArg (fun z ↦ ((ρ n).inv.app N).val.app U z)
    (evaluation_unit l E L ι W A ρ hρ N n U x)
  have hi := iso_hom_inv_section W ((ρ n).app N) U
    ((A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x)
  unfold evaluatedUnitSection finiteScalarUnitSection
  exact heq_of_eq (hx.symm.trans hi)

@[irreducible] private def scalarSystemMap :
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)) ⟶
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l L W)) :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (SemilinearSections.systemMap.{t + 1, t, max (t + 1) u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (coefficientExtensionQuotient_naturality l E L ι W))

@[irreducible] private def scalarAdjunction (A : CoefficientExtensionSystems l E L ι W) :
    A.scalar.model.E ⊣ SheafOfModules.restrictScalars (scalarSystemMap l E L ι W) := by
  unfold scalarSystemMap
  exact A.scalar.ordinaryAdjunction

private theorem scalarUnitNaturalityLaw (A : CoefficientExtensionSystems l E L ι W) :
    AdjunctionUnitNaturality (scalarSystemMap l E L ι W) (scalarAdjunction l E L ι W A) :=
  adjunctionUnitNaturality (scalarSystemMap l E L ι W) (scalarAdjunction l E L ι W A)

@[irreducible] private def rawScalarUnitSection
    (A : CoefficientExtensionSystems l E L ι W) (N : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) :=
  abstractUnitSection (scalarSystemMap l E L ι W) (scalarAdjunction l E L ι W A)
    N (op (n, U.unop)) x

private theorem rawScalarUnitSection_heq
    (A : CoefficientExtensionSystems l E L ι W) (N : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    HEq (rawScalarUnitSection l E L ι W A N n U x)
      (((scalarAdjunction l E L ι W A).unit.app N).val.app (op (n, U.unop)) x) := by
  unfold rawScalarUnitSection
  exact abstractUnitSection_heq (scalarSystemMap l E L ι W) (scalarAdjunction l E L ι W A)
    N (op (n, U.unop)) x

private theorem scalarUnit_naturality
    (A : CoefficientExtensionSystems l E L ι W) (N : coefficientSequenceModules l E W)
    {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ)
    (x : N.val.obj (op (m, U.unop))) :
    HEq (presheafMapSection (A.scalar.model.E.obj N)
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
      (rawScalarUnitSection l E L ι W A N m U x))
      (rawScalarUnitSection l E L ι W A N n U
        (presheafMapSection N (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)) := by
  unfold rawScalarUnitSection
  exact (scalarUnitNaturalityLaw l E L ι W A).naturality N
    (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x

private theorem evaluatedUnitSection_normalized
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq (evaluatedUnitSection l E L ι W A ρ N n U x)
      (rawScalarUnitSection l E L ι W A N n U x) := by
  have hi := rawScalarUnitSection_heq l E L ι W A N n U x
  unfold scalarAdjunction scalarSystemMap at hi
  exact (evaluatedUnitSection_raw l E L ι W A ρ hρ N n U x).trans hi.symm

private theorem coefficientTransition_nativeMap
    (N : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W m).obj N).val.obj U) :
    HEq (((coefficientSequenceTransition l E W h).app N).val.app U x)
      (presheafMapSection N (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  unfold presheafMapSection
  exact heq_of_eq (coefficientTransition_section l E W N h U x)

/-- The normalized finite scalar unit preserves every compatible pair of system sections.

Source: Stacks 03D7; sequence-site construction preceding 0941.
(blueprint: stage3-pur-extension-scalar-unit-transition).

Proof: apply the evaluation unit equation and cancel rho to identify the normalized
finite unit with the system adjunction unit. The latter is a sheaf-module morphism
on the sequence site, so naturality for the horizontal arrow commutes with the
presheaf restriction maps. The coefficient transition section formula identifies
these maps with the finite successors. Substitute compatibility of the input pair,
then use the lower evaluation unit identity in reverse. This applies also to
identity arrows and zero sections and uses no exactness or flatness. -/
theorem evaluatedUnitSection_transition
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W m).obj N).val.obj U)
    (y : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U)
    (hxy : HEq (((coefficientSequenceTransition l E W h).app N).val.app U x) y) :
    HEq (((coefficientSequenceTransition l L W h).app
      (A.scalar.model.E.obj N)).val.app U
        (evaluatedUnitSection l E L ι W A ρ N m U x))
      (evaluatedUnitSection l E L ι W A ρ N n U y) := by
  have hi := evaluatedUnitSection_normalized l E L ι W A ρ hρ N m U x
  have hj := evaluatedUnitSection_normalized l E L ι W A ρ hρ N n U y
  have hn := scalarUnit_naturality l E L ι W A N h U x
  have htE := coefficientTransition_nativeMap l E W N h U x
  have hx := htE.symm.trans hxy
  have htL := coefficientTransition_nativeMap l L W (A.scalar.model.E.obj N) h U
    (evaluatedUnitSection l E L ι W A ρ N m U x)
  have hh := congrArg (presheafMapSection (A.scalar.model.E.obj N)
    (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) (eq_of_heq hi)
  have hη := congrArg (rawScalarUnitSection l E L ι W A N n U) (eq_of_heq hx)
  exact htL.trans ((heq_of_eq hh).trans (hn.trans ((heq_of_eq hη).trans hj.symm)))

end CoefficientExtensionAssociation
end WeilConjectures
