/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor

/-! # Quotient unit sections of an ordinary tensor system

Source: Stacks 03CZ and 03D7; the sequence site preceding 0941.
All constructions are actual normalized adjunction units. The generic laws prevent
kernel checking from expanding the completed coefficient ring at each application.
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
section GenericLaw
universe a b c v₁ v₂ v₃
private structure QuotientUnitLaw
    {C : Type a} {D : Type b} {D' : Type c}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} D']
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {F' : C ⥤ D'} {G' : D' ⥤ C} (adj' : F' ⊣ G')
    (T : D' ⥤ D) (e : T ⋙ G ≅ G') : Prop where
  unit : ∀ X : C,
    HEq (adj.unit.app X ≫ G.map ((coefficientQuotientNatTrans adj adj' T e).app X))
      (adj'.unit.app X ≫ e.inv.app (F'.obj X))

private theorem quotientUnitLaw
    {C : Type a} {D : Type b} {D' : Type c}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} D']
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {F' : C ⥤ D'} {G' : D' ⥤ C} (adj' : F' ⊣ G')
    (T : D' ⥤ D) (e : T ⋙ G ≅ G') : QuotientUnitLaw adj adj' T e := by
  constructor
  intro X
  exact heq_of_eq ((adj.homEquiv X (T.obj (F'.obj X))).apply_symm_apply _)
private structure QuotientMateLaw
    {C : Type a} {D : Type b} {D' : Type c}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} D']
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {F' : C ⥤ D'} {G' : D' ⥤ C} (adj' : F' ⊣ G')
    (T : D' ⥤ D) (e : T ⋙ G ≅ G') (q : F ⟶ F' ⋙ T) : Prop where
  app_eq : ∀ M, q.app M = (coefficientQuotientNatTrans adj adj' T e).app M

universe d e r₀
/-- The actual adjunction unit section, returned in the native target module.
Keeping this carrier explicit avoids unfolding restriction-of-scalars actions.
Source: Stacks 03D7. -/
@[irreducible] def normalizedUnitSection
    {C : Type d} [Category.{e} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r₀}} (f : R ⟶ S)
    {F : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    (M : SheafOfModules.{r₀} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (F.obj M).val.obj U :=
  (adj.unit.app M).val.app U x

private structure QuotientSectionUnitLaw
    {C : Type d} [Category.{e} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r₀}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : SheafOfModules.restrictScalars.{r₀} g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars h)
    {F : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    {F' : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} T}
    (adj' : F' ⊣ SheafOfModules.restrictScalars h) : Prop where
  unit : ∀ (M : SheafOfModules.{r₀} R) (U : Cᵒᵖ) (x : M.val.obj U),
    HEq (((coefficientQuotientNatTrans adj adj' (SheafOfModules.restrictScalars g)
      (eqToIso he)).app M).val.app U (normalizedUnitSection f adj M U x))
      (normalizedUnitSection h adj' M U x)

private theorem quotientSectionUnitLaw
    {C : Type d} [Category.{e} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r₀}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : SheafOfModules.restrictScalars.{r₀} g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars h)
    {F : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    {F' : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} T}
    (adj' : F' ⊣ SheafOfModules.restrictScalars h) :
    QuotientSectionUnitLaw f g h he adj adj' := by
  constructor
  intro M U x
  have hu := (quotientUnitLaw adj adj' (SheafOfModules.restrictScalars g)
    (eqToIso he)).unit M
  have hx := congrArg (fun k ↦ k.val.app U x) (eq_of_heq hu)
  have hy := whisker_transport_section_heq he (𝟭 _) (F'.obj M) U
    ((adj'.unit.app M).val.app U x)
  have hr := restrict_apply_heq f
    ((coefficientQuotientNatTrans adj adj' (SheafOfModules.restrictScalars g)
      (eqToIso he)).app M) U
    ((adj.unit.app M).val.app U x) ((adj.unit.app M).val.app U x) (HEq.refl _)
  unfold normalizedUnitSection
  exact hr.symm.trans ((heq_of_eq hx).trans hy)

private structure TransportedUnitLaw
    {C : Type d} [Category.{e} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r₀}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    {F : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    {F' : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} T}
    (adj' : F' ⊣ SheafOfModules.restrictScalars h) (M : SheafOfModules.{r₀} R)
    {A : SheafOfModules.{r₀} S} {B : SheafOfModules.{r₀} T}
    (em : A ≅ F.obj M) (en : B ≅ F'.obj M)
    (τ : A ⟶ (SheafOfModules.restrictScalars g).obj B) : Prop where
  unit : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
    HEq (τ.val.app U (em.inv.val.app U (normalizedUnitSection f adj M U x)))
      (en.inv.val.app U (normalizedUnitSection h adj' M U x))

private theorem transportedUnitLaw
    {C : Type d} [Category.{e} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r₀}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : SheafOfModules.restrictScalars.{r₀} g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars h)
    {F : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    {F' : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} T}
    (adj' : F' ⊣ SheafOfModules.restrictScalars h) (M : SheafOfModules.{r₀} R)
    {A : SheafOfModules.{r₀} S} {B : SheafOfModules.{r₀} T}
    (em : A ≅ F.obj M) (en : B ≅ F'.obj M)
    (τ : A ⟶ (SheafOfModules.restrictScalars g).obj B)
    (q : F ⟶ F' ⋙ SheafOfModules.restrictScalars g)
    (hq : QuotientMateLaw adj adj' (SheafOfModules.restrictScalars g) (eqToIso he) q)
    (ht : τ ≫ (SheafOfModules.restrictScalars g).map en.hom = em.hom ≫ q.app M) :
    TransportedUnitLaw f g h adj adj' M em en τ := by
  constructor
  intro U x
  let xm := em.inv.val.app U (normalizedUnitSection f adj M U x)
  have hh := congrArg (fun z ↦ z ≫ (SheafOfModules.restrictScalars g).map en.inv) ht
  have hm : τ = em.hom ≫ q.app M ≫ (SheafOfModules.restrictScalars g).map en.inv := by
    simp only [Category.assoc, ← Functor.map_comp, en.hom_inv_id] at hh
    rw [(SheafOfModules.restrictScalars g).map_id B, Category.comp_id] at hh
    exact hh
  have hs := congrArg (fun z ↦ z.val.app U xm) hm
  have hi := congrArg (fun z ↦ z.val.app U (normalizedUnitSection f adj M U x))
    em.inv_hom_id
  have hc := (quotientSectionUnitLaw f g h he adj adj').unit M U x
  have hqm := (heq_of_eq (congrArg (fun z ↦ z.val.app U
    (normalizedUnitSection f adj M U x)) (hq.app_eq M))).trans hc
  have hqx := (heq_of_eq (congrArg (fun z ↦ (q.app M).val.app U z) hi)).trans hqm
  have hr := restrict_apply_heq g en.inv U ((q.app M).val.app U (em.hom.val.app U xm))
    (normalizedUnitSection h adj' M U x) hqx
  exact (heq_of_eq hs).trans hr

end GenericLaw

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  integralScalarReduction completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SemilinearSections.systemMap
  scalarReductionExtension scalarReductionExistence coefficientOrdinaryQuotient
  coefficientQuotientNatTrans coefficientOrdinaryQuotientComponent

/-- The completed coefficient projection, viewed as a ring-sheaf map.
Source: the quotient tower preceding Stacks 0941. -/
abbrev coefficientProjection (n : ℕ) :
    SheafOfModules.derivedChangeRingIndependentCoefficients (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) ⟶ integralCoefficientSheaf l E W n :=
  (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)

/-- The quotient tensor adjunction with its recorded sectionwise unit normalization.
The chosen witness fixes the unit on every section, rather than choosing arbitrary data.
Source: `scalarReductionExtension_adjunction`, Stacks 03CZ and 03D7. -/
def quotientAdjunction (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose
attribute [local irreducible] quotientAdjunction

/-- The normalized quotient tensor unit section.
Source: Stacks 03CZ and 03D7. -/
@[irreducible] def finiteUnitSection (M : scalarReductionSource l E W) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarReductionExtension l E W n).obj M).val.obj U :=
  normalizedUnitSection (coefficientProjection l E W n) (quotientAdjunction l E W n) M U x

private theorem quotient_nat_eq_mate {m n : ℕ} (h : n ≤ m) :
    coefficientOrdinaryQuotient l E W h =
      coefficientQuotientNatTrans (quotientAdjunction l E W m)
        (quotientAdjunction l E W n) (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h)) := by
  unfold coefficientOrdinaryQuotient
  symm
  apply (coefficientOrdinaryQuotient_exists l E W h).choose_spec.2
  intro M
  unfold coefficientOrdinaryQuotientComponent quotientAdjunction
  rfl

private theorem quotient_mate_law {m n : ℕ} (h : n ≤ m) :
    QuotientMateLaw (quotientAdjunction l E W m) (quotientAdjunction l E W n)
      (normalizedDVRModuleRes l E W h) (eqToIso (coefficientRestrictionComp l E W h))
      (coefficientOrdinaryQuotient l E W h) := by
  constructor
  intro M
  exact congrArg (fun q ↦ q.app M) (quotient_nat_eq_mate l E W h)

private theorem tensor_unit_law (M : CompletionUnit.OrdinaryModel l E W)
    (K : scalarReductionSource l E W) (n : ℕ) :
    TransportedUnitLaw (coefficientProjection l E W (n + 1))
      (normalizedDVRQuotient l E W (Nat.le_succ n)) (coefficientProjection l E W n)
      (quotientAdjunction l E W (n + 1)) (quotientAdjunction l E W n) K
      ((M.evaluation (n + 1)).app K) ((M.evaluation n).app K)
      ((coefficientSequenceTransition l E W (Nat.le_succ n)).app (M.tensor.obj K)) :=
  transportedUnitLaw (coefficientProjection l E W (n + 1))
    (normalizedDVRQuotient l E W (Nat.le_succ n)) (coefficientProjection l E W n)
    (coefficientRestrictionComp l E W (Nat.le_succ n))
    (quotientAdjunction l E W (n + 1)) (quotientAdjunction l E W n) K
    ((M.evaluation (n + 1)).app K) ((M.evaluation n).app K)
    ((coefficientSequenceTransition l E W (Nat.le_succ n)).app (M.tensor.obj K))
    (coefficientOrdinaryQuotient l E W (Nat.le_succ n))
    (quotient_mate_law l E W (Nat.le_succ n)) (M.transition K (Nat.le_succ n))

/-- The quotient unit transported into the supplied ordinary system model.
Source: Stacks 03D7 and the sequence-site construction preceding 0941. -/
@[irreducible] def quotientUnitSection (M : CompletionUnit.OrdinaryModel l E W)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    ((coefficientSequenceEvaluation l E W n).obj (M.tensor.obj K)).val.obj U :=
  ((M.evaluation n).inv.app K).val.app U (finiteUnitSection l E W K n U x)

private theorem quotientUnitSection_evaluation (M : CompletionUnit.OrdinaryModel l E W)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    ((M.evaluation n).hom.app K).val.app U (quotientUnitSection l E W M K n U x) =
      finiteUnitSection l E W K n U x := by
  unfold quotientUnitSection
  exact congrArg (fun f ↦ f.val.app U (finiteUnitSection l E W K n U x))
    ((M.evaluation n).app K).inv_hom_id

/-- Quotient unit sections are compatible with the successor of the ordinary tensor model.

Source: Stacks 03D7; sequence-site quotient construction preceding 0941.
(blueprint: stage3-pur-extension-quotient-unit-successor).

Proof: the ordinary quotient is the mate of composition of restriction functors.
The adjunction Hom equivalence sends its defining mate back to the lower unit.
Restriction and its composition comparison preserve underlying sections.
Conjugate this unit identity by the two evaluation isomorphisms, using the
transition clause of the given model, and cancel each isomorphism with its inverse.
This proves the formula for every section, including the zero section and n = 0. -/
theorem quotientUnitSection_transition (M : CompletionUnit.OrdinaryModel l E W)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    HEq (((coefficientSequenceTransition l E W (Nat.le_succ n)).app
      (M.tensor.obj K)).val.app U (quotientUnitSection l E W M K (n + 1) U x))
      (quotientUnitSection l E W M K n U x) := by
  unfold quotientUnitSection finiteUnitSection
  exact (tensor_unit_law l E W M K n).unit U x

end CoefficientExtensionAssociation
end WeilConjectures
