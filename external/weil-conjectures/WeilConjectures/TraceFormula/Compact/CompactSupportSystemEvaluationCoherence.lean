/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.TraceFormula.Compact.CompactSupportSystemNormalizedPresentation
import WeilConjectures.TraceFormula.Compact.CompactSupportCompletedRestrictionTransition
import WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageRestrictionTransition

/-! # Compact-support system evaluation coherence

Source: Weil conjectures blueprint, `prop-trf-rational-frobenius-integral-model.proof.md`,
clause (3), second paragraph (blueprint: lem-trf-compact-support-system-evaluation-coherence).

`CompactSupportSystemEvaluationWitness` states normalization of the actual geometric
comparison maps, their compatibility with the two specified transition definitions,
and the four unit and counit equations. `compactSupportSystemEvaluationCoherence`
supplies this witness and its presentation before any inverse limit is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u c₁ c₂ d₁ d₂ v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalization of the actual finite coefficient square on all K-injective models.
Source: node proof step 2, Zheng 4.10
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def compactSupportCoefficientSquareNormalized
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] {m n : ℕ} (h : n ≤ m) : Prop :=
  letI := normalizedDVRModuleRes_limits l E Z h
  letI := normalizedDVRModuleRes_colimits l E Z h
  letI := normalizedDVRModuleRes_limits l E Y h
  letI := normalizedDVRModuleRes_colimits l E Y h
  CompactSupportDerivedSquareNormalization
    (compactSupportLevelDirectImage l E p n) (compactSupportLevelDirectImage l E p m)
    (normalizedDVRModuleRes l E Z h) (normalizedDVRModuleRes l E Y h)
    (D.operations.ordinaryCoefficientComparison h) (D.operations.derivedCoefficientComparison h)

/-- Normalization of actual direct-image evaluation on arbitrary evaluated resolutions.
Source: node proof step 2, Stacks 0D6E
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def compactSupportDirectImageEvaluationNormalized
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] (n : ℕ) : Prop :=
  letI := coefficientSequenceEvaluation_additiveInstance l E Z n
  letI := coefficientSequenceEvaluation_additiveInstance l E Y n
  letI := coefficientSequenceEvaluation_limits l E Z n
  letI := coefficientSequenceEvaluation_colimits l E Z n
  letI := coefficientSequenceEvaluation_limits l E Y n
  letI := coefficientSequenceEvaluation_colimits l E Y n
  CompactSupportDerivedSquareNormalization
    (integralComparisonSequenceDirectImage l E p) (compactSupportLevelDirectImage l E p n)
    (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
    (D.pOrdinaryEvaluation n).symm (D.pRightEvaluation n).symm

/-- The unit equation for the two comparison maps of an evaluated adjunction.
Source: node final clause, SemilinearSections.AdjunctionEvaluation.unit
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportUnitEvaluation
    {C : Type c₁} {D : Type c₂} {c : Type d₁} {d : Type d₂}
    [Category.{v} C] [Category.{v} D] [Category.{v} c] [Category.{v} d]
    (E₀ : C ⥤ c) (F₀ : D ⥤ d)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L₀ : c ⥤ d} {R₀ : d ⥤ c} (level : L₀ ⊣ R₀)
    (left : L ⋙ F₀ ≅ E₀ ⋙ L₀) (right : R ⋙ E₀ ≅ F₀ ⋙ R₀) : Prop :=
  ∀ M : C,
    E₀.map (adj.unit.app M) ≫ right.hom.app (L.obj M) ≫
      R₀.map (left.hom.app M) = level.unit.app (E₀.obj M)

/-- The counit equation for the same two evaluated comparison maps.
Source: node final clause, SemilinearSections.AdjunctionEvaluation.counit
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportCounitEvaluation
    {C : Type c₁} {D : Type c₂} {c : Type d₁} {d : Type d₂}
    [Category.{v} C] [Category.{v} D] [Category.{v} c] [Category.{v} d]
    (E₀ : C ⥤ c) (F₀ : D ⥤ d)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L₀ : c ⥤ d} {R₀ : d ⥤ c} (level : L₀ ⊣ R₀)
    (left : L ⋙ F₀ ≅ E₀ ⋙ L₀) (right : R ⋙ E₀ ≅ F₀ ⋙ R₀) : Prop :=
  ∀ N : D,
    L₀.map (right.hom.app N) ≫ level.counit.app (F₀.obj N) =
      left.inv.app (R.obj N) ≫ F₀.map (adj.counit.app N)

/-- Identity on sections for the ordinary quotient restriction square.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def compactSupportOrdinaryCoefficientSectionsNormalized
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
      (N : normalizedDVRModules l E Z n) (V : Y.ProEtᵒᵖ),
      HEq (fun x ↦ ((D.operations.ordinaryCoefficientComparison h).hom.app N).val.app V x)
        (fun x : N.val.obj ((Scheme.proEtaleBaseChange p).op.obj V) ↦ x)

/-- Identity on sections for the slice-restriction evaluation of the open presentation.
With the open presentation's unit and counit evaluation equations, this fixes its
extension evaluation `e_n J = j_! e_n`, so `theta` and the target transition use the
canonical open identification rather than one twisted by a levelwise automorphism.
Source: node statement, `e_n J_j^str = j_! e_n`; proof step 3, Stacks 03DJ
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def compactSupportOpenRestrictionSectionsNormalized
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ (n : ℕ) N V x,
    HEq (((D.operations.instances.jOperations.openSystems.restrictionEvaluation n).hom.app
      N).val.app V x) x

/-- Identity on sections for the ordinary system direct-image evaluation.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def compactSupportOrdinaryDirectImageSectionsNormalized
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ (n : ℕ) (N : coefficientSequenceModules l E Z)
      (V : Y.ProEtᵒᵖ)
      (x : ((integralComparisonSequenceDirectImage l E p ⋙
        coefficientSequenceEvaluation l E Y n).obj N).val.obj V),
      HEq (((D.pOrdinaryEvaluation n).hom.app N).val.app V x) x

/-- Compatibility with the actual source tower and the specified target transition.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportSystemTransitionCompatibility
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p]
    (theta : ∀ n : ℕ, compactSupportSystemSourceLevel l E (D := D) n ≅
      compactSupportSystemTargetLevel l E (D := D) n) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
      (M : coefficientSequenceDerived l E X),
      compactSupportSystemSourceTransition l E (D := D) h M ≫ (theta n).hom.app M =
        (theta m).hom.app M ≫ compactSupportSystemTargetTransition l E (D := D) h M

/-- Unit compatibility for evaluation of the actual open adjunction.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportSystemOpenUnitCompatibility
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ n : ℕ,
      CompactSupportUnitEvaluation
        (coefficientSequenceDerivedEvaluation l E X n)
        (coefficientSequenceDerivedEvaluation l E Z n)
        (L := compactSupportCanonicalJSystem l E j D.operations.instances.jOperations)
        (R := IntegralOpenReduction.P l E j D.operations.instances.jOperations)
        (L₀ := compactSupportCanonicalJLevel l E j D.operations.instances.jOperations n)
        (R₀ := (IntegralOpenReduction.finiteRestriction l E j
          D.operations.instances.jOperations n).mapDerivedCategory)
        (IntegralOpenReduction.systemAdjunction l E j D.operations.instances.jOperations)
        (compactSupportCanonicalJLevelAdjunction l E j D.operations.instances.jOperations n)
        (D.jLeftEvaluation n) (D.jRightEvaluation n)

/-- Counit compatibility for evaluation of the actual open adjunction.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportSystemOpenCounitCompatibility
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ n : ℕ,
      CompactSupportCounitEvaluation
        (coefficientSequenceDerivedEvaluation l E X n)
        (coefficientSequenceDerivedEvaluation l E Z n)
        (L := compactSupportCanonicalJSystem l E j D.operations.instances.jOperations)
        (R := IntegralOpenReduction.P l E j D.operations.instances.jOperations)
        (L₀ := compactSupportCanonicalJLevel l E j D.operations.instances.jOperations n)
        (R₀ := (IntegralOpenReduction.finiteRestriction l E j
          D.operations.instances.jOperations n).mapDerivedCategory)
        (IntegralOpenReduction.systemAdjunction l E j D.operations.instances.jOperations)
        (compactSupportCanonicalJLevelAdjunction l E j D.operations.instances.jOperations n)
        (D.jLeftEvaluation n) (D.jRightEvaluation n)

/-- Unit compatibility for evaluation of the actual direct-image adjunction.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportSystemDirectImageUnitCompatibility
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ n : ℕ,
      CompactSupportUnitEvaluation
        (coefficientSequenceDerivedEvaluation l E Y n)
        (coefficientSequenceDerivedEvaluation l E Z n)
        (L := integralComparisonDerivedSequencePullback l E p)
        (R := (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor)
        (L₀ := (compactSupportLevelPullback l E p n).mapDerivedCategory)
        (R₀ := (compactSupportLevelDirectImage l E p n).rightDerivedFunctor)
        (compactSupportCanonicalPAdjunction l E p) (compactSupportCanonicalPLevelAdjunction l E p n)
        (D.pLeftEvaluation n) (D.pRightEvaluation n)

/-- Counit compatibility for evaluation of the actual direct-image adjunction.
Source: node statement, proof steps 2--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportSystemDirectImageCounitCompatibility
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] : Prop :=
  ∀ n : ℕ,
      CompactSupportCounitEvaluation
        (coefficientSequenceDerivedEvaluation l E Y n)
        (coefficientSequenceDerivedEvaluation l E Z n)
        (L := integralComparisonDerivedSequencePullback l E p)
        (R := (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor)
        (L₀ := (compactSupportLevelPullback l E p n).mapDerivedCategory)
        (R₀ := (compactSupportLevelDirectImage l E p n).rightDerivedFunctor)
        (compactSupportCanonicalPAdjunction l E p) (compactSupportCanonicalPLevelAdjunction l E p n)
        (D.pLeftEvaluation n) (D.pRightEvaluation n)

/-- A whole-tower comparison using the two fixed transition definitions.
The four final conjuncts state unit and counit compatibility of the same component
comparisons that define `theta`; they are conclusions of the existence theorem below.
Source: node statement, final three sentences; proof steps 4--6
(blueprint: lem-trf-compact-support-system-evaluation-coherence). -/
def CompactSupportSystemEvaluationWitness
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [D : CompactSupportSystemEvaluationData l E X Z Y j p] :=
  { theta : ∀ n : ℕ, compactSupportSystemSourceLevel l E (D := D) n ≅
    compactSupportSystemTargetLevel l E (D := D) n //
    -- ordinaryCoefficientSections
    compactSupportOrdinaryCoefficientSectionsNormalized l E (D := D) ∧
    -- derivedCoefficientNormalization
    (∀ {m n : ℕ} (h : n ≤ m),
      compactSupportCoefficientSquareNormalized l E (D := D) h) ∧
    -- openRestrictionSections
    compactSupportOpenRestrictionSectionsNormalized l E (D := D) ∧
    -- jEvaluation_canonical
    (∀ n : ℕ, (D.jLeftEvaluation n) =
      compactSupportCanonicalJEvaluation l E j D.operations.instances.jOperations n) ∧
    -- pOrdinaryEvaluationSections
    compactSupportOrdinaryDirectImageSectionsNormalized l E (D := D) ∧
    -- pEvaluation_canonical
    (∀ n : ℕ,
      compactSupportDirectImageEvaluationNormalized l E (D := D) n) ∧
    -- theta_canonical
    (∀ n : ℕ, theta n = compactSupportSystemEvaluationIso l E (D := D) n) ∧
    -- transition_compatibility
    CompactSupportSystemTransitionCompatibility l E (D := D) theta ∧
    -- j_unit
    CompactSupportSystemOpenUnitCompatibility l E (D := D) ∧
    -- j_counit
    CompactSupportSystemOpenCounitCompatibility l E (D := D) ∧
    -- p_unit
    CompactSupportSystemDirectImageUnitCompatibility l E (D := D) ∧
    -- p_counit
    CompactSupportSystemDirectImageCounitCompatibility l E (D := D) }

private theorem restriction_mate_transpose
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {L : C ⥤ D} {R : D ⥤ C} {L' : A ⥤ B} {R' : B ⥤ A}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ A} {H : D ⥤ B}
    (β : TwoSquare R H G R') {M : C} {N : D} (f : M ⟶ R.obj N) :
    (adj'.homEquiv _ _)
        (((mateEquiv adj adj').symm β).app M ≫
          H.map ((adj.homEquiv _ _).symm f)) =
      G.map f ≫ β.app N := by
  have hu : G.map (adj.unit.app M) ≫ β.app (L.obj M) =
      adj'.unit.app (G.obj M) ≫
        R'.map (((mateEquiv adj adj').symm β).app M) :=
    unit_mateEquiv_symm adj adj' β M
  rw [adj'.homEquiv_unit, R'.map_comp, ← Category.assoc, ← hu, Category.assoc]
  have hn := β.naturality ((adj.homEquiv _ _).symm f)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]
  change G.map ((adj.homEquiv _ _) ((adj.homEquiv _ _).symm f)) ≫ _ = _
  rw [Equiv.apply_symm_apply]

private theorem evaluated_tower_square
    {C D A : Type*} [Category C] [Category D] [Category A]
    (R : C ⥤ A) (S : D ⥤ A) (Q : D ⥤ C) (q : Q ⋙ R ≅ S)
    {a b c : C} {a' b' c' : D} {P P' : A}
    (i : P ≅ R.obj a) (i' : P' ≅ S.obj a')
    (j : a ≅ b) (j' : a' ≅ b') (k : b ≅ c) (k' : b' ≅ c')
    (t : P ⟶ P') (v : a ⟶ Q.obj a') (w : b ⟶ Q.obj b')
    (ht : t ≫ i'.hom = i.hom ≫ R.map v ≫ q.hom.app a')
    (hv : v ≫ Q.map j'.hom = j.hom ≫ w) :
    t ≫ i'.hom ≫ S.map j'.hom ≫ S.map k'.hom =
      (i.hom ≫ R.map j.hom ≫ R.map k.hom) ≫
        R.map (k.inv ≫ w) ≫ q.hom.app b' ≫ S.map k'.hom := by
  calc
    _ = i.hom ≫ R.map v ≫ q.hom.app a' ≫ S.map j'.hom ≫ S.map k'.hom := by
      rw [← Category.assoc t, ht]
      simp only [Category.assoc]
    _ = i.hom ≫ R.map (v ≫ Q.map j'.hom) ≫ q.hom.app b' ≫ S.map k'.hom := by
      rw [R.map_comp]
      have hn := q.hom.naturality j'.hom
      dsimp only [Functor.comp_map] at hn
      simp only [Category.assoc]
      rw [← reassoc_of% hn]
    _ = i.hom ≫ R.map (j.hom ≫ w) ≫ q.hom.app b' ≫ S.map k'.hom := by rw [hv]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc]

/-- Coherent evaluation of the actual strict compact-support system before any limit.
Index `n : ℕ` denotes positive exponent `n+1`. The theorem supplies the canonical
presentation and its natural level isomorphisms, the equation for every actual tower
transition, and both unit and counit equations for each geometric adjunction.

Source: Weil blueprint `prop-trf-rational-frobenius-integral-model.proof.md`, clause (3),
second paragraph (blueprint: lem-trf-compact-support-system-evaluation-coherence).
Proof plan:
1. The ringed sequence site realizes ordinary strict quotient-linear systems, with
componentwise exact evaluation and simultaneous K-injective resolutions, by
`def-coef-ringed-sequence-site` and `lem-coef-semilinear-derived-sections`.
2. The canonical sectionwise direct image is `integralComparisonSequenceDirectImage p`.
Its coefficient map is constant-section base change. The coefficient identifications
`p⁻¹ B_n = B_n` commute with all quotients by
`prop-weil-pbc-proetale-constant-ring-map` and `def-weil-proetale-inverse-image`.
The semilinear calculus gives its derived evaluations, normalized on arbitrary
K-injective resolutions by CompactSupportDerivedSquareNormalization. It also gives
the identity-on-sections coefficient square and its normalized derived square.
3. The pro-etale open localization and `lem-pur-site-restriction-module-adjunction-exact`
give the exact, section-normalized slice extension and restriction on whole systems.
Its finite evaluations are the localizations of IntegralOpenReduction.extensionEvaluation.
Slice restriction keeps every section, so its evaluation is the identity on sections;
the open unit/counit evaluation equations then fix the extension evaluation itself.
Thus N=J M has the real transitions obtained by extending the input transitions.
4. Transpose the normalized restriction square under the finite quotient adjunctions.
This is b. The actual transition of N has adjunct t^N, so semilinear derived sections
identifies the extension-form direct-image transition with Rp_n(t^N) composed with b.
Transpose under the same coefficient adjunction on Y and apply Res_m. The actual
projection composition gives compactSupportSystemTargetTransition. No arbitrary
transition family, cartesianness, quotient-flatness or evaluated K-injectivity is used.
5. Exact termwise completed restriction identifies ev_n U with Res_n e_n through
coefficientRestrictedEvaluationIso. Composing the direct-image and open evaluations
is compactSupportSystemEvaluationIso. The transition equation identifies the two
whole towers; natural isomorphisms ensure naturality for every derived morphism.
6. The canonical ordinary adjunctions descend to their normalized derived adjunctions.
Their unit and counit evaluation identities are the four explicit witness conclusions.
All these constructions precede any inverse limit. -/
theorem compactSupportSystemEvaluationCoherence
    {X Z Y : Scheme.{t}} {j : X ⟶ Z} {p : Z ⟶ Y} [IsOpenImmersion j]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] :
    ∃ D : CompactSupportSystemEvaluationData l E X Z Y j p,
      Nonempty (CompactSupportSystemEvaluationWitness l E (D := D)) := by
  obtain ⟨D, hcoef, hcoeff, hopen, hj, hp, hpn, hju, hjc, hpu, hpc⟩ :=
    compactSupportSystemNormalizedPresentation l E (j := j) (p := p)
  let := D
  refine ⟨D, ⟨⟨fun n ↦ compactSupportSystemEvaluationIso l E (D := D) n,
    hcoef, hcoeff, hopen, hj, hp, hpn, fun _ ↦ rfl, ?_, hju, hjc, hpu, hpc⟩⟩⟩
  intro m n h M
  let N := (compactSupportCanonicalJSystem l E j D.operations.instances.jOperations).obj M
  let P := (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor.obj N
  have he := compactSupportCompletedRestrictionTransition l E Y h P
  have hd := compactSupportDirectImageRestrictionTransition l E hcoef hcoeff hp hpn h N
  have hm := restriction_mate_transpose (D.operations.scalarZ h) (D.operations.scalarY h)
    (TwoSquare.mk _ _ _ _ (D.operations.derivedCoefficientComparison h).hom)
    ((coefficientSequenceDerivedTransition l E Z h).app N)
  have ht :
      (coefficientSequenceDerivedTransition l E Y h).app P ≫
        (normalizedDVRRes l E Y h).map ((D.pRightEvaluation n).hom.app N) =
      (D.pRightEvaluation m).hom.app N ≫
        ((D.operations.scalarY h).homEquiv _ _)
          (compactSupportSystemExtensionTransition l E (D := D) h M) := by
    rw [hd]
    exact congrArg (fun f ↦ (D.pRightEvaluation m).hom.app N ≫ f) hm.symm
  have hs := evaluated_tower_square
    (coefficientFiniteDerivedRestriction l E Y m)
    (coefficientFiniteDerivedRestriction l E Y n) (normalizedDVRRes l E Y h)
    (compactSupportSystemRestrictionComp l E Y h)
    ((coefficientRestrictedEvaluationIso l E Y m).app P)
    ((coefficientRestrictedEvaluationIso l E Y n).app P)
    ((D.pRightEvaluation m).app N) ((D.pRightEvaluation n).app N)
    ((compactSupportLevelDirectImage l E p m).rightDerivedFunctor.mapIso
      ((D.jLeftEvaluation m).app M))
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.mapIso
      ((D.jLeftEvaluation n).app M))
    ((compactSupportConstantTowerTransition l E Y h).app
      ((coefficientSequenceDerivedRestriction l E Y).obj P))
    ((coefficientSequenceDerivedTransition l E Y h).app P)
    (((D.operations.scalarY h).homEquiv _ _)
      (compactSupportSystemExtensionTransition l E (D := D) h M)) he ht
  exact hs

end WeilConjectures
