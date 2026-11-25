/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.OrdinaryCompactSupportCoefficientTransport
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.OrdinaryCompactSupportCoefficientTransport
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportScalarProofs
import WeilConjectures.CategoryTheory.Localization.ResolutionNormalizedComparison
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CoefficientRestrictionLimitAcyclicity

/-! # SemilinearCompactSupportCoefficientTransport

Source: blueprint theorem-smooth-purity-all-admissible-coefficients, Steps 2--3; the compact-support
realization prerequisite, proof Steps 2--3 and 8--11 (agent-formulated constructions).
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true

set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q DerivedCategory.Qh
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftAdjoint constantSheaf
  WeilConjectures.CompactSupportCondensedRealization.systemScalarData

-- Preserve the private API used by the native constant-restriction proof.
private theorem pushforward_additive_explicit
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous JC JD]
    {R : Sheaf JD RingCat.{u + 1}} {S : Sheaf JC RingCat.{u + 1}}
    (b : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} JC JD).obj R) :
    (SheafOfModules.pushforward.{u + 1} b).Additive :=
  scalarSitePushforward_additive F b

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] coefficientSequenceRestriction rightUnitApp rightUnit

/-- The ordinary limit of a strict semilinear system after its actual coefficient
restriction. Source: Zheng 4.1; blueprint proof Step 3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def ordinarySystemLimit (W : Scheme.{u}) :
    coefficientSequenceModules.{u, u} l E W ⥤ scalarReductionSource.{u, u} l E W :=
  coefficientSequenceRestriction.{u, u} l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤
      scalarReductionSource.{u, u} l E W)

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- Additivity of the actual strict-system limit.
Source: Stacks 0941 (blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: restriction of scalars is additive and limits in module sheaves are formed
on the underlying additive sheaves. Thus the map of a sum of compatible sections
is the sum of their limit maps. The universal projections detect this equation. -/
@[instance] theorem ordinarySystemLimit_additive (W : Scheme.{u}) :
    (ordinarySystemLimit l E W).Additive := by
  have h := coefficientConstantTowerLimitAdditive l E W
  change (coefficientSequenceRestriction l E W ⋙ lim).Additive
  infer_instance

/-- The natural comparison from an ordinary limit on complexes to the specified total
limit: the real limit derived unit followed by exact coefficient-restriction descent.
Source: Stacks 0D6E; blueprint proof Step 3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def limitUnitApp (W : Scheme.{u}) (K : CochainComplex
    (coefficientSequenceModules.{u, u} l E W) ℤ) :=
  (rightUnit (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤
    scalarReductionSource.{u, u} l E W)).app
      (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj K) ≫
    (coefficientConstantTowerLimit.{u, u} l E W).map
      ((coefficientSequenceRestriction.{u, u} l E W).mapDerivedCategoryFactors.inv.app K)

/-- Naturality of the specified whole-system limit unit.
Source: Stacks 0D6E; blueprint proof Step 3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: naturality of the real right-derived limit unit and of exact restriction's
localization comparison paste to this equation on all chain maps. -/
theorem limitUnitApp_naturality (W : Scheme.{u})
    {K L : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map (((ordinarySystemLimit l E W).mapHomologicalComplex (.up ℤ)).map f) ≫
        limitUnitApp l E W L =
      limitUnitApp l E W K ≫ (coefficientSequenceLimit.{u, u} l E W).map
        (DerivedCategory.Q.map f) := by
  exact composed_rightUnit_naturality (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) f

/-- The actual total-limit comparison on complexes, retained to normalize coefficient
transport before evaluation. Source: blueprint proof Steps 3 and 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def limitUnit (W : Scheme.{u}) :
    (ordinarySystemLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit.{u, u} l E W where
  app := limitUnitApp l E W
  naturality := fun _ _ f ↦ limitUnitApp_naturality l E W f

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Actual restriction along the residue-normalized completed coefficient inclusion.
Source: blueprint proof Steps 7--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
abbrev completedRestriction (W : Scheme.{u}) :=
  pbcRestrict (completedCoefficientMap l E F i W)

attribute [local irreducible] completedCoefficientMap coefficientSequenceRestriction
  scalarSystemMap rightUnitApp rightUnit limitUnitApp limitUnit
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard DerivedCategory.Q DerivedCategory.Qh

section TowerComparisonProof

attribute [local irreducible] limit completedIntegralCommRingProjectionUnrestricted
  Functor.ofOpSequence Functor.ofSequence

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem tower_section_type
    (W : Scheme.{u}) (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    ((((coefficientSequenceRestriction l E W).obj M).obj (op n)).val.obj U : Type (u + 1)) =
      (M.val.obj (op (n, U.unop)) : Type (u + 1)) := by
  unfold coefficientSequenceRestriction
  exact congrArg (fun N : scalarReductionSource l E W ↦ (N.val.obj U : Type (u + 1)))
    ((coefficientSequenceRestriction_exists l E W).exists.choose_spec.1 M n)

private theorem tower_transition_sections
    (W : Scheme.{u}) (M : coefficientSequenceModules l E W) (m n : ℕ) (h : n ≤ m)
    (U : W.ProEtᵒᵖ) :
    HEq (fun x : (((coefficientSequenceRestriction l E W).obj M).obj (op m)).val.obj U ↦
      ((((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op).val.app U) x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  unfold coefficientSequenceRestriction
  exact (coefficientSequenceRestriction_exists l E W).exists.choose_spec.2.1 M m n h U

private theorem completed_map_projection (W : Scheme.{u}) (n : ℕ) :
    completedCoefficientMap l E F i W ≫
      completedIntegralCommRingProjectionUnrestricted l F W n =
    completedIntegralCommRingProjectionUnrestricted l E W n ≫
      integralScalarQuotientSheafMap l E F i W n := by
  unfold completedCoefficientMap
  exact (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec n

private theorem system_evaluation_eq (W : Scheme.{u}) (n : ℕ) :
    SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) n =
      coefficientSequenceEvaluation l E W n := rfl

private theorem heq_apply_of_heq {A B D : Type u} (hA : A = D) (hB : B = D)
    {f : A → B} (h : HEq f (fun x : D ↦ x)) (x : A) : HEq (f x) x := by
  subst A B
  exact heq_of_eq (congrFun (eq_of_heq h) x)

private theorem assemble_level_isos
    {D C I : Type*} [Category D] [Category C] [Category I]
    (A B : D ⥤ I ⥤ C)
    (d : ∀ n, A ⋙ (evaluation I C).obj n ≅ B ⋙ (evaluation I C).obj n)
    (hd : ∀ M m n (f : m ⟶ n),
      (A.obj M).map f ≫ (d n).hom.app M =
        (d m).hom.app M ≫ (B.obj M).map f) :
    ∃ e : A ≅ B, ∀ M n, (e.hom.app M).app n = (d n).hom.app M := by
  let eM (M : D) : A.obj M ≅ B.obj M :=
    NatIso.ofComponents (fun n ↦ (d n).app M) (fun f ↦ hd M _ _ f)
  let e : A ≅ B := NatIso.ofComponents eM (by
    intro M N f
    apply NatTrans.ext
    funext n
    exact (d n).hom.naturality f)
  exact ⟨e, fun _ _ ↦ rfl⟩

private theorem iso_section_transport
    {A C : Type*} [Category A] [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {F F' G G' : A ⥤ SheafOfModules.{u + 1} R}
    (hF : F = F') (hG : G = G') (d : F' ≅ G') (V : A → Cᵒᵖ → Type (u + 1))
    (hd : ∀ M U, HEq (fun x ↦ (d.hom.app M).val.app U x) (fun x : V M U ↦ x)) :
    ∃ e : F ≅ G,
      ∀ M U, HEq (fun x ↦ (e.hom.app M).val.app U x) (fun x : V M U ↦ x) := by
  subst F' G'
  exact ⟨d, hd⟩

attribute [local irreducible] constantSheaf Functor.leftAdjoint

private theorem system_restriction_evaluation (W : Scheme.{u}) (n : ℕ) :
    ∃ e : systemRestriction l E F i W ⋙ coefficientSequenceEvaluation l E W n ≅
        coefficientSequenceEvaluation l F W n ⋙
          SemilinearSections.res (integralScalarQuotientSheafMap l E F i W n),
      ∀ M U, HEq (fun x ↦ (e.hom.app M).val.app U x)
        (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  obtain ⟨d, hd, -⟩ := SemilinearSections.restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
    (ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l F W)
    (coefficientSequenceCommRingTransition l F W)
    (integralScalarQuotientSheafMap l E F i W) (scalarQuotients_commute l E F i W) n
  let d' : systemRestriction l E F i W ⋙
      SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W)
        (coefficientSequenceCommRingTransition l E W) n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l F W)
        (coefficientSequenceCommRingTransition l F W) n ⋙
        SemilinearSections.res (integralScalarQuotientSheafMap l E F i W n) := by
    unfold systemRestriction scalarSystemMap
    exact d
  exact iso_section_transport
    (congrArg (systemRestriction l E F i W ⋙ ·)
      (system_evaluation_eq l E W n).symm)
    (congrArg (· ⋙ SemilinearSections.res (integralScalarQuotientSheafMap l E F i W n))
      (system_evaluation_eq l F W n).symm)
    d' (fun M U ↦ M.val.obj (op (n, U.unop))) (by
      intro M U
      dsimp only [d']
      exact hd M U)

private theorem normalized_postcomp {A B V : Type u} (f : A → B) (g : B → B)
    (hf : HEq f (fun x : V ↦ x)) (hg : ∀ x, g x = x) :
    HEq (fun x ↦ g (f x)) (fun x : V ↦ x) :=
  (heq_of_eq (funext (fun x ↦ hg (f x)))).trans hf

private theorem restriction_scalar_iso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {RX SX RY SY : Sheaf J RingCat.{u + 1}}
    (a : RX ⟶ SX) (b : RY ⟶ SY) (p : RY ⟶ RX) (q : SY ⟶ SX)
    (h : p ≫ a = b ≫ q) :
    ∃ d : SheafOfModules.restrictScalars.{u + 1} a ⋙
          SheafOfModules.restrictScalars p ≅
        SheafOfModules.restrictScalars q ⋙ SheafOfModules.restrictScalars b,
      ∀ (M : SheafOfModules.{u + 1} SX) (U : Cᵒᵖ) (x : M.val.obj U),
        (d.hom.app M).val.app U x = x := by
  let e (M : SheafOfModules.{u + 1} SX) (U : Cᵒᵖ) :
      (((SheafOfModules.restrictScalars a ⋙
        SheafOfModules.restrictScalars p).obj M).val.obj U) ≅
      (((SheafOfModules.restrictScalars q ⋙
        SheafOfModules.restrictScalars b).obj M).val.obj U) :=
    (AddEquiv.toLinearEquiv
      (M := ↑(((SheafOfModules.restrictScalars a ⋙
        SheafOfModules.restrictScalars p).obj M).val.obj U))
      (M₂ := ↑(((SheafOfModules.restrictScalars q ⋙
        SheafOfModules.restrictScalars b).obj M).val.obj U))
      (by rfl) (fun r x ↦ by
        let smul : (SX.obj.obj U) → (M.val.obj U) → (M.val.obj U) := fun r x ↦ r • x
        change smul ((a.hom.app U) ((p.hom.app U) r)) x =
          smul ((q.hom.app U) ((b.hom.app U) r)) x
        exact congrArg (fun z ↦ smul z x)
          (congrArg (fun f : RY ⟶ SX ↦ (f.hom.app U) r) h))).toModuleIso
  let d : SheafOfModules.restrictScalars.{u + 1} a ⋙
      SheafOfModules.restrictScalars p ≅
      SheafOfModules.restrictScalars q ⋙ SheafOfModules.restrictScalars b :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget RY).preimageIso
        (PresheafOfModules.isoMk (e M) (by intro U V f; ext x; rfl)))
      (by intro M N f; ext U x; rfl)
  exact ⟨d, fun _ _ _ ↦ rfl⟩

private theorem restriction_whisker_iso_app
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A B : Type*} [Category A] [Category B]
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S)
    (F : A ⥤ SheafOfModules.{u + 1} S) (G : A ⥤ B)
    (H : B ⥤ SheafOfModules.{u + 1} S) (K : B ⥤ SheafOfModules.{u + 1} R)
    (e : F ≅ G ⋙ H) (d : H ⋙ SheafOfModules.restrictScalars a ≅ K)
    (M : A) (U : Cᵒᵖ) (x : (F.obj M).val.obj U) :
    (((Functor.isoWhiskerRight e (SheafOfModules.restrictScalars a) ≪≫
      Functor.isoWhiskerLeft G d).hom.app M).val.app U x) =
        (d.hom.app (G.obj M)).val.app U ((e.hom.app M).val.app U x) := rfl

set_option maxHeartbeats 200000 in
-- Compare the given residue maps before transporting the sectionwise identity.
private theorem restrictionTower_level (W : Scheme.{u}) (n : ℕ) :
    ∃ d : (systemRestriction l E F i W ⋙ coefficientSequenceRestriction l E W) ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      (coefficientSequenceRestriction l F W ⋙
        (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l F W)
          (scalarReductionSource l E W)).obj (completedRestriction l E F i W)) ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n),
      ∀ M U, HEq (fun x ↦ (d.hom.app M).val.app U x)
        (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  let J := ProEt.topology W
  let q (L : Type u) [NormedField L] [NormedAlgebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l L W n)
  let b := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (completedCoefficientMap l E F i W)
  let c := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (integralScalarQuotientSheafMap l E F i W n)
  have hres : q E ≫ c = b ≫ q F := by
    have hh := completed_map_projection l E F i W n
    let H := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    exact ((H.map_comp _ _).symm.trans
      ((congrArg H.map hh).trans (H.map_comp _ _))).symm
  obtain ⟨d₁, hd₁⟩ := restriction_scalar_iso c b (q E) (q F) hres
  obtain ⟨d₀', hd₀'⟩ := system_restriction_evaluation l E F i W n
  let d := Functor.isoWhiskerRight d₀' (SheafOfModules.restrictScalars (q E)) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l F W n) d₁
  have hd : ∀ M U, HEq (fun x ↦ (d.hom.app M).val.app U x)
      (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
    intro M U
    exact (heq_of_eq (funext (fun x ↦ restriction_whisker_iso_app (q E)
      _ _ _ _ d₀' d₁ M U x))).trans
      (normalized_postcomp
        (fun x ↦ (d₀'.hom.app M).val.app U x)
        (fun x ↦ (d₁.hom.app ((coefficientSequenceEvaluation l F W n).obj M)).val.app U x)
        (hd₀' M U) (hd₁ ((coefficientSequenceEvaluation l F W n).obj M) U))
  have hL : (systemRestriction l E F i W ⋙ coefficientSequenceRestriction l E W) ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) =
      systemRestriction l E F i W ⋙ coefficientSequenceEvaluation l E W n ⋙
        SheafOfModules.restrictScalars (q E) :=
    congrArg (systemRestriction l E F i W ⋙ ·)
      (coefficientSequenceRestriction_evaluation l E W n)
  have hR : (coefficientSequenceRestriction l F W ⋙
      (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l F W)
        (scalarReductionSource l E W)).obj (completedRestriction l E F i W)) ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) =
      (coefficientSequenceEvaluation l F W n ⋙ SheafOfModules.restrictScalars (q F)) ⋙
        SheafOfModules.restrictScalars b :=
    congrArg (· ⋙ completedRestriction l E F i W)
      (coefficientSequenceRestriction_evaluation l F W n)
  exact iso_section_transport hL hR d
    (fun M U ↦ M.val.obj (op (n, U.unop))) hd

set_option maxHeartbeats 200000 in
-- Assemble the level comparisons with the sectionwise transition formulas.
attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- Restriction after forgetting a semilinear system equals termwise completed scalar
restriction, by the identity on underlying sections. This retains the strict diagram.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: the completed inclusion followed by a target finite projection equals the
source finite projection followed by the same-index quotient inclusion. Thus the two
restricted coefficient actions agree. Identity section maps commute with all index
arrows; sectionwise faithfulness proves uniqueness. No quotient flatness is used. -/
theorem restrictionTower_existsUnique (W : Scheme.{u}) :
    ∃! d : systemRestriction l E F i W ⋙ coefficientSequenceRestriction.{u, u} l E W ≅
        coefficientSequenceRestriction.{u, u} l F W ⋙
          (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource.{u, u} l F W)
            (scalarReductionSource.{u, u} l E W)).obj (completedRestriction l E F i W),
      ∀ (M : coefficientSequenceModules.{u, u} l F W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (x : (((coefficientSequenceRestriction.{u, u} l E W).obj
          ((systemRestriction l E F i W).obj M)).obj (op n)).val.obj U),
        HEq (((d.hom.app M).app (op n)).val.app U x) x := by
  let A := systemRestriction l E F i W ⋙ coefficientSequenceRestriction l E W
  let B := coefficientSequenceRestriction l F W ⋙
    (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l F W)
      (scalarReductionSource l E W)).obj (completedRestriction l E F i W)
  let d (n : ℕ) := (restrictionTower_level l E F i W n).choose
  have hd (n : ℕ) := (restrictionTower_level l E F i W n).choose_spec
  have htype (L : Type u) [NormedField L] [NormedAlgebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (M : coefficientSequenceModules l L W)
      (n : ℕ) (U : W.ProEtᵒᵖ) :
      ((((coefficientSequenceRestriction l L W).obj M).obj (op n)).val.obj U :
        Type (u + 1)) = (M.val.obj (op (n, U.unop)) : Type (u + 1)) := by
    exact tower_section_type l L W M n U
  have hn (M : coefficientSequenceModules l F W) (m n : ℕᵒᵖ) (h : m ⟶ n) :
      (A.obj M).map h ≫ (d n.unop).hom.app M =
        (d m.unop).hom.app M ≫ (B.obj M).map h := by
    ext U x
    have hAm := htype E ((systemRestriction l E F i W).obj M) m.unop U
    have hAn := htype E ((systemRestriction l E F i W).obj M) n.unop U
    have hBm := htype F M m.unop U
    have hBn := htype F M n.unop U
    have htA := tower_transition_sections l E W
      ((systemRestriction l E F i W).obj M) m.unop n.unop (leOfHom h.unop) U
    have htB := tower_transition_sections l F W
      M m.unop n.unop (leOfHom h.unop) U
    have hh : (homOfLE (leOfHom h.unop)).op = h := Subsingleton.elim _ _
    simp only [hh] at htA htB
    exact congrFun (normalized_square hAm hAn hBm hBn
      (fun x ↦ ((A.obj M).map h).val.app U x)
      (fun x ↦ ((d n.unop).hom.app M).val.app U x)
      (fun x ↦ ((d m.unop).hom.app M).val.app U x)
      (fun x ↦ ((B.obj M).map h).val.app U x)
      (fun x : M.val.obj (op (m.unop, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE (leOfHom h.unop)) (𝟙 U.unop)).op x)
      htA (hd n.unop M U) (hd m.unop M U) htB) x
  obtain ⟨e, he⟩ := assemble_level_isos A B (fun n ↦ d n.unop) hn
  apply ExistsUnique.intro e
  · intro M n U x
    rw [he M (op n)]
    have hh := hd n M U
    have hs := htype E ((systemRestriction l E F i W).obj M) n U
    have ht := htype F M n U
    exact heq_apply_of_heq hs ht hh x
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  rw [he M n]
  exact eq_of_heq ((he' M n.unop U x).trans
    (heq_apply_of_heq
      (htype E ((systemRestriction l E F i W).obj M) n.unop U)
      (htype F M n.unop U) (hd n.unop M U) x).symm)

end TowerComparisonProof

/-- The uniquely section-normalized strict tower comparison.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def restrictionTower (W : Scheme.{u}) :
    systemRestriction l E F i W ⋙ coefficientSequenceRestriction.{u, u} l E W ≅
      coefficientSequenceRestriction.{u, u} l F W ⋙
        (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource.{u, u} l F W)
          (scalarReductionSource.{u, u} l E W)).obj (completedRestriction l E F i W) :=
  (restrictionTower_existsUnique l E F i W).exists.choose

attribute [local irreducible] restrictionTower

private theorem restriction_preserves_tower_limits
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S) :
    PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.restrictScalars.{u + 1} a) := by
  let U := SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.toPresheaf R.obj
  let V := SheafOfModules.forget.{u + 1} S ⋙ PresheafOfModules.toPresheaf S.obj
  let e : SheafOfModules.restrictScalars.{u + 1} a ⋙ U ≅ V :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have : PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.restrictScalars.{u + 1} a ⋙ U) :=
    preservesLimitsOfShape_of_natIso e.symm
  have : ReflectsLimitsOfShape ℕᵒᵖ U :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ U

private theorem limit_comparison_existsUnique
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ C]
    (R : B ⥤ C) [PreservesLimitsOfShape ℕᵒᵖ R]
    (V : A ⥤ ℕᵒᵖ ⥤ B) (U : A ⥤ ℕᵒᵖ ⥤ C)
    (e : U ≅ V ⋙ (Functor.whiskeringRight ℕᵒᵖ B C).obj R) :
    ∃! d : V ⋙ lim ⋙ R ≅ U ⋙ lim,
      ∀ (M : A) (n : ℕᵒᵖ), d.hom.app M ≫ limit.π (U.obj M) n ≫
        (e.hom.app M).app n = R.map (limit.π (V.obj M) n) := by
  let d : V ⋙ lim ⋙ R ≅ U ⋙ lim :=
    Functor.isoWhiskerLeft V (preservesLimitNatIso R) ≪≫
      Functor.isoWhiskerRight e.symm lim
  have hd (M : A) (n : ℕᵒᵖ) : d.hom.app M ≫ limit.π (U.obj M) n ≫
      (e.hom.app M).app n = R.map (limit.π (V.obj M) n) := by
    change ((preservesLimitIso R (V.obj M)).hom ≫ lim.map (e.inv.app M)) ≫ _ ≫ _ = _
    simp only [Category.assoc, lim_map, limMap_π_assoc,
      ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
    change (preservesLimitIso R (V.obj M)).hom ≫
      limit.π (V.obj M ⋙ R) n ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact preservesLimitIso_hom_π R (V.obj M) n
  apply ExistsUnique.intro d hd
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  apply (cancel_mono ((e.hom.app M).app n)).mp
  simpa only [Category.assoc] using (hd' M n).trans (hd M n).symm

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- The ordinary limit comparison is fixed by every actual strict-tower projection.
Source: Stacks 0A07; blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: coefficient restriction creates limits, as it leaves the underlying abelian
sheaf unchanged. Its projection cone, followed by restrictionTower inverse, is a
limiting cone on the restricted strict system. The limit universal property supplies
the displayed isomorphism and proves uniqueness from these projection equations. -/
theorem ordinaryLimitRestriction_existsUnique (W : Scheme.{u}) :
    ∃! d : ordinarySystemLimit l F W ⋙ completedRestriction l E F i W ≅
        systemRestriction l E F i W ⋙ ordinarySystemLimit l E W,
      ∀ (M : coefficientSequenceModules.{u, u} l F W) (n : ℕ),
        d.hom.app M ≫
            limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
              ((systemRestriction l E F i W).obj M)) (op n) ≫
            ((restrictionTower l E F i W).hom.app M).app (op n) =
          (completedRestriction l E F i W).map
            (limit.π ((coefficientSequenceRestriction.{u, u} l F W).obj M) (op n)) := by
  let R := completedRestriction l E F i W
  have : PreservesLimitsOfShape ℕᵒᵖ R := restriction_preserves_tower_limits
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedCoefficientMap l E F i W))
  obtain ⟨d, hd, hu⟩ := limit_comparison_existsUnique R
    (coefficientSequenceRestriction l F W)
    (systemRestriction l E F i W ⋙ coefficientSequenceRestriction l E W)
    (restrictionTower l E F i W)
  exact ⟨d, fun M n ↦ hd M (op n), fun d' hd' ↦ hu d' (fun M n ↦ hd' M n.unop)⟩

/-- The canonical ordinary limit/restriction comparison.
Source: blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def ordinaryLimitRestriction (W : Scheme.{u}) :
    ordinarySystemLimit l F W ⋙ completedRestriction l E F i W ≅
      systemRestriction l E F i W ⋙ ordinarySystemLimit l E W :=
  (ordinaryLimitRestriction_existsUnique l E F i W).exists.choose

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- Zero preservation of the displayed ordinary composite.
Source: blueprint proof Steps 10--12; Stacks 03DA
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: Restriction is additive sectionwise and the sectionwise inverse limit preserves zero. Their
composite therefore maps each zero arrow to zero. -/
@[instance] theorem systemRestrictionLimit_zero (W : Scheme.{u}) :
    (systemRestriction l E F i W ⋙ ordinarySystemLimit l E W).PreservesZeroMorphisms := by
  constructor
  intro X Y
  have := coefficientConstantTowerLimitAdditive l E W
  change lim.map ((coefficientSequenceRestriction l E W).map
    ((systemRestriction l E F i W).map 0)) = 0
  simp only [Functor.map_zero]

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- Zero preservation of the opposite ordinary normalization composite.
Source: blueprint proof Steps 10--12; Stacks 03DA
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: both factors are additive on section morphisms and map zero to zero.
Their composite therefore maps the zero arrow between any two modules to zero. -/
theorem systemLimitRestriction_zero (W : Scheme.{u}) :
    (ordinarySystemLimit l F W ⋙ completedRestriction l E F i W).PreservesZeroMorphisms := by
  constructor
  intro X Y
  change (completedRestriction l E F i W).map
    ((ordinarySystemLimit l F W).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

attribute [local irreducible] ordinaryLimitRestriction

/-- The exact universal normalization equation on whole complexes.
Source: blueprint proof Steps 10--12; Stacks 06YY and 0D6E
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def IsLimitRestrictionNormalized (W : Scheme.{u})
    (d : coefficientSequenceLimit.{u, u} l F W ⋙
          (completedRestriction l E F i W).mapDerivedCategory ≅
        derivedSystemRestriction l E F i W ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  letI := systemRestrictionLimit_zero l E F i W
  letI := systemLimitRestriction_zero l E F i W
  ∀ K : CochainComplex (coefficientSequenceModules.{u, u} l F W) ℤ,
    (completedRestriction l E F i W).mapDerivedCategory.map ((limitUnit l F W).app K) ≫
        d.hom.app (DerivedCategory.Q.obj K) ≫
        (coefficientSequenceLimit.{u, u} l E W).map
          ((systemRestriction l E F i W).mapDerivedCategoryFactors.hom.app K) =
      (completedRestriction l E F i W).mapDerivedCategoryFactors.hom.app
          (((ordinarySystemLimit l F W).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryLimitRestriction l E F i W) (.up ℤ)).hom.app
            K) ≫
        (limitUnit l E W).app
          (((systemRestriction l E F i W).mapHomologicalComplex (.up ℤ)).obj K)

open SheafOfModules

/-- Derived limit/restriction is normalized by the real universal comparison on whole
complexes, not selected by evaluated derived arrows.
Source: Stacks 0D6E and 0A07; blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: form the two actual universal-unit transformations from the ordinary limit
square. On functorial K-injective system resolutions both are invertible, by restricted
system acyclicity for the target projection cone and for its composite with the completed
coefficient map. Fully faithful precomposition with derived localization descends their
comparison. Naturality along the resolution map proves the displayed normalization on
all complexes, and cancellation on resolutions proves uniqueness. Scalar restriction
need not preserve K-injectives. -/
theorem limitRestriction_existsUnique (W : Scheme.{u}) :
    ∃! d : coefficientSequenceLimit.{u, u} l F W ⋙
          (completedRestriction l E F i W).mapDerivedCategory ≅
        derivedSystemRestriction l E F i W ⋙ coefficientSequenceLimit.{u, u} l E W,
      IsLimitRestrictionNormalized l E F i W d := by
  let J := coefficientSequenceTopology (ProEt.topology W)
  let hsite : EssentiallySmall.{u + 1} (ℕ × W.ProEt) := essentiallySmallSelf.{0} _
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    @SheafOfModules.hasSheafify_coefficientUniverse _ _ hsite J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse _ _ hsite J
  let : IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules.{u, u} l F W) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l F W)).1
  let P := CochainComplex.kInjectiveResolutionFunctor.{u + 1}
    (coefficientSequenceModules.{u, u} l F W)
  let q := CochainComplex.toKInjectiveResolution.{u + 1}
    (coefficientSequenceModules.{u, u} l F W)
  let R := completedRestriction l E F i W
  let V := systemRestriction l E F i W
  let S := coefficientSequenceLimit l F W ⋙ R.mapDerivedCategory
  let T := V.mapDerivedCategory ⋙ coefficientSequenceLimit l E W
  let U := V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
    coefficientSequenceLimit l E W
  let κ : DerivedCategory.Q ⋙ T ≅ U :=
    Functor.isoWhiskerRight V.mapDerivedCategoryFactors (coefficientSequenceLimit l E W)
  let O := (ordinarySystemLimit l F W).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⋙ R.mapDerivedCategory
  let α : O ⟶ DerivedCategory.Q ⋙ S :=
    Functor.whiskerRight (limitUnit l F W) R.mapDerivedCategory
  have := systemRestrictionLimit_zero l E F i W
  have := systemLimitRestriction_zero l E F i W
  let β : O ⟶ U :=
    Functor.whiskerLeft ((ordinarySystemLimit l F W).mapHomologicalComplex (.up ℤ))
        R.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        (NatIso.mapHomologicalComplex (ordinaryLimitRestriction l E F i W) (.up ℤ)).hom
        DerivedCategory.Q ≫
      Functor.whiskerLeft (V.mapHomologicalComplex (.up ℤ)) (limitUnit l E W)
  have hu (I : CochainComplex (coefficientSequenceModules.{u, u} l F W) ℤ) [I.IsKInjective] :
      IsIso ((limitUnit l F W).app I) ∧
        IsIso ((limitUnit l E W).app ((V.mapHomologicalComplex (.up ℤ)).obj I)) := by
    obtain ⟨hF, hE⟩ := coefficientRestrictionLimitAcyclicity l E F i W
      (restrictionTower l E F i W) I
    constructor
    · unfold limitUnit limitUnitApp
      infer_instance
    · unfold limitUnit limitUnitApp
      infer_instance
  have hα (K : CochainComplex (coefficientSequenceModules.{u, u} l F W) ℤ) :
      IsIso (α.app (P.obj K)) := by
    have := (hu (P.obj K)).1
    change IsIso (R.mapDerivedCategory.map ((limitUnit l F W).app (P.obj K)))
    infer_instance
  have hβ (K : CochainComplex (coefficientSequenceModules.{u, u} l F W) ℤ) :
      IsIso (β.app (P.obj K)) := by
    have := (hu (P.obj K)).2
    dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  obtain ⟨d, hd, huniq⟩ := Localization.resolutionNormalizedComparison
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) P q
    (fun K ↦ (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ K).2)
    O S T U κ α β hα hβ
  exact ⟨d, hd, fun e he ↦ huniq e he⟩

/-- The normalized whole-system derived limit comparison.
Source: blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def limitRestriction (W : Scheme.{u}) :
    coefficientSequenceLimit.{u, u} l F W ⋙
        (completedRestriction l E F i W).mapDerivedCategory ≅
      derivedSystemRestriction l E F i W ⋙ coefficientSequenceLimit.{u, u} l E W :=
  (limitRestriction_existsUnique l E F i W).exists.choose

attribute [local semireducible] scalarSystemMap

/-- Reduction/scalar balancing is the conjugate of the specified limit restriction
square under the actual scalar and reduction adjunctions. This defines the comparison
on the whole derived ringed sequence site.
Source: blueprint proof Steps 10--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def reductionScalar (W : Scheme.{u})
    (RE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (RF : CoefficientDerivedSystemCalculus.{u, u} l F W) :
    pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙ RF.reduction ≅
      RE.reduction ⋙ (systemScalarData l E F i W).scalar.T :=
  (((pbcDerivedScalarAdjunction (completedCoefficientMap l E F i W)).comp
    RF.adjunction).ofNatIsoRight (limitRestriction l E F i W)).leftAdjointUniq
      (RE.adjunction.comp (systemScalarData l E F i W).scalar.adjunction)

end WeilConjectures.CompactSupportCondensedRealization
