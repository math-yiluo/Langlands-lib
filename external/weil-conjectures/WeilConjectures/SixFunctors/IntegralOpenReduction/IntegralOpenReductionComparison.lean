/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModel
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.CanonicalOpenRestrictionModel
import WeilConjectures.SixFunctors.OpenRestrictionCompleteness.OpenRestrictionCompleteness
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SixFunctors.IntegralOpenReduction.NormalizedOpenSections
import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenExtensionComplete

/-!
# Strict reduction and normalized realization of integral open extension

Source: Stacks Project, Tags 0GL1 and 0E8I; blueprint `fix-prop-coherence`,
open-factor sentence (blueprint: lem-sf-integral-open-reduction-comparison).
The natural index n denotes exponent n+1. Site and coefficient sizes are independent.

## Main definitions

- `Coefficients`: constant-section and quotient-normalized transport to the actual open slice.
- `Operations`: the localized extension/restriction functors on modules and strict systems.
- `Comparison`: strict representative normalization and realized adjunction identities.

## Main statements

- `integralOpenReductionComparison`: existence of the specified comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.IntegralOnSlice.completionUnit WeilConjectures.IntegralOnSlice.completion
  WeilConjectures.IntegralOnSlice.completionComparison WeilConjectures.IntegralOnSlice.roosUnit
  WeilConjectures.IntegralOnSlice.augmentation

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOpenReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

private def inverseUnitIso
    {I C D : Type*} [Category* I] [Category* C] [Category* D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    (A : I ⥤ C) (B : I ⥤ D) (r : A ⋙ R ≅ B)
    (h : ∀ i, IsIso (adj.unit.app (A.obj i))) : B ⋙ L ≅ A := by
  letI (i : I) := h i
  refine NatIso.ofComponents
    (fun i ↦ L.mapIso (r.symm.app i) ≪≫ (asIso (adj.unit.app (A.obj i))).symm) ?_
  intro i k f
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.comp_map, asIso_inv]
  apply (cancel_mono (adj.unit.app (A.obj k))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn := adj.unit.naturality (A.map f)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [hn, IsIso.inv_hom_id_assoc]
  rw [← L.map_comp, ← L.map_comp]
  exact congrArg L.map (r.inv.naturality f)

private theorem inverseUnitIso_normalization
    {I C D : Type*} [Category* I] [Category* C] [Category* D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    (A : I ⥤ C) (B : I ⥤ D) (r : A ⋙ R ≅ B)
    (h : ∀ i, IsIso (adj.unit.app (A.obj i))) (i : I) :
    R.map ((inverseUnitIso adj A B r h).hom.app i) ≫ r.hom.app i =
      adj.counit.app (B.obj i) := by
  let := h i
  change R.map (L.map (r.inv.app i) ≫ inv (adj.unit.app (A.obj i))) ≫ _ = _
  rw [R.map_comp, Functor.map_inv, adj.inv_map_unit]
  have hn := adj.counit.naturality (r.inv.app i)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  have hn' := congrArg (fun f ↦ f ≫ r.hom.app i) hn
  simp only [Category.assoc, Iso.inv_hom_id_app] at hn'
  exact (Category.assoc _ _ _).trans
    (hn'.trans (Category.comp_id (adj.counit.app (B.obj i))))

private theorem inverse_unit_natural
    {C D : Type*} [Category* C] [Category* D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    {K H : C} (f : K ⟶ H) [IsIso (adj.unit.app H)] :
    adj.unit.app K ≫ L.map (R.map f) ≫ inv (adj.unit.app H) = f := by
  have hn := adj.unit.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem realize_counit_composite
    {C D : Type*} [Category* C] [Category* D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    {K H : C} {A B : D} (f : K ⟶ H)
    (a : R.obj K ⟶ A) (b : A ⟶ B) (c : B ⟶ R.obj H)
    (h : a ≫ b ≫ c = R.map f) [IsIso (adj.unit.app H)] :
    (adj.unit.app K ≫ L.map a) ≫ L.map b ≫ L.map c ≫ inv (adj.unit.app H) = f := by
  simp only [Category.assoc, ← L.map_comp_assoc]
  rw [h]
  exact inverse_unit_natural adj f

private theorem comparisonOfModel
    (hlX : IsUnit (l : Γ(X, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤)))
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (o : Operations l E j) (tensor : TensorComparison l E j o)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (c : OpenSemilinearTensor.Comparison l E j o SX SU AX AU tensor)
    (hext : ∀ K, complete l E U K → complete l E X ((shriek l E j o).obj K)) :
    Nonempty (Comparison l E j o SX SU tensor) := by
  classical
  let hInvX (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        hlX.map ((X.presheaf.germ ⊤ x (by trivial)) ≫ X.residue x).hom).invertible
  let hInvU (x : U) : Invertible (l : U.residueField x) :=
    (show IsUnit (l : U.residueField x) from by
      simpa only [map_natCast] using
        hlU.map ((U.presheaf.germ ⊤ x (by trivial)) ≫ U.residue x).hom).invertible
  let : ∀ x : X, Invertible (l : X.residueField x) := hInvX
  let : ∀ x : U, Invertible (l : U.residueField x) := hInvU
  have hX := purNormalizedReconstruction l E X hlX SX
  have hU := purNormalizedReconstruction l E U hlU SU
  have hcall := @CanonicalOpenRestriction.canonicalOpenRestrictionModel.{t, u}
    l ‹Fact l.Prime› E ‹Field E› ‹Algebra ℚ_[l] E› ‹FiniteDimensional ℚ_[l] E›
    U X j ‹IsOpenImmersion j› o SU SX
  have hcall' := hcall c.r tensor
  obtain ⟨s, hmate, _hmodel⟩ := hcall' (by
    intro Q hQ
    obtain ⟨cU, cX, hsquare⟩ := c.model Q hQ.1 hQ.2
    refine ⟨⟨c.kflat Q hQ.1 hQ.2, c.preservesFlatTerms Q hQ.1 hQ.2⟩,
      _, _, cU.iso, cX.iso, AU.complexEvaluation l E Q,
      AX.complexEvaluation l E _,
      OpenSemilinearTensor.ordinaryChain l E j o AX AU c.ordinary Q,
      cU.presentation, cU.augmentation, cX.presentation, cX.augmentation, hsquare, ?_⟩
    intro n i
    exact c.components (Q.X i) n)
  clear hcall' hcall _hmodel
  have hc : ∀ H, complete l E X H → complete l E U ((star l E j o).obj H) :=
    fun H hH ↦ (OpenRestrictionCompleteness.openRestrictionComplete l E j o H hH).1
  have hsu (K) : SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
      s.hom.app ((shriek l E j o).obj K) ≫ (P l E j o).map (c.r.hom.app K) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K) := by
    rw [hmate, ← Category.assoc]
    rw [show SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
        ((mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
          (TwoSquare.mk _ _ _ _ c.r.inv)).app ((shriek l E j o).obj K)) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K) ≫
          (P l E j o).map (c.r.inv.app K) from
      unit_mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
        (TwoSquare.mk _ _ _ _ c.r.inv) K]
    simp [← Functor.map_comp]
  have hsc (H) : SX.reduction.map ((openAdjunction l E j o).counit.app H) =
      c.r.hom.app ((star l E j o).obj H) ≫ (J l E j o).map (s.hom.app H) ≫
        (systemAdjunction l E j o).counit.app (SX.reduction.obj H) := by
    rw [hmate]
    rw [show (J l E j o).map
        ((mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
          (TwoSquare.mk _ _ _ _ c.r.inv)).app H) ≫
        (systemAdjunction l E j o).counit.app (SX.reduction.obj H) =
        c.r.inv.app ((star l E j o).obj H) ≫
          SX.reduction.map ((openAdjunction l E j o).counit.app H) from
      mateEquiv_counit (openAdjunction l E j o) (systemAdjunction l E j o)
        (TwoSquare.mk _ _ _ _ c.r.inv) H]
    simp
  let di := inverseUnitIso SX.adjunction
    ((complete l E U).ι ⋙ shriek l E j o)
    ((complete l E U).ι ⋙ SU.reduction ⋙ J l E j o)
    (isoWhiskerLeft (complete l E U).ι c.r)
    (fun K ↦ hX.2 _ (hext _ K.property))
  let bi := inverseUnitIso SU.adjunction
    ((complete l E X).ι ⋙ star l E j o)
    ((complete l E X).ι ⋙ SX.reduction ⋙ P l E j o)
    (isoWhiskerLeft (complete l E X).ι s)
    (fun H ↦ hU.2 _ (hc _ H.property))
  let uU (K : (complete l E U).FullSubcategory) :=
    @asIso _ _ _ _ (SU.adjunction.unit.app K.obj) (hU.2 _ K.property)
  let uX (H : (complete l E X).FullSubcategory) :=
    @asIso _ _ _ _ (SX.adjunction.unit.app H.obj) (hX.2 _ H.property)
  refine ⟨{
    r := isoWhiskerLeft (complete l E U).ι c.r
    extensionComplete := fun K ↦ hext K.obj K.property
    restrictionComplete := fun H ↦ hc H.obj H.property
    s := isoWhiskerLeft (complete l E X).ι s
    unitU := uU
    unitUHom := fun _ ↦ rfl
    unitX := uX
    unitXHom := fun _ ↦ rfl
    d := di
    dFormula := fun _ ↦ rfl
    reductionD := fun K ↦ inverseUnitIso_normalization SX.adjunction _ _ _ _ K
    pullRealization := bi
    pullFormula := fun _ ↦ rfl
    systemUnit := fun K ↦ hsu K.obj
    systemCounit := fun H ↦ (hsc H.obj).symm
    realizedUnit := ?_
    realizedCounit := ?_
    strictModel := ?_ }⟩
  · intro K
    let : IsIso (SU.adjunction.unit.app
        ((star l E j o).obj ((shriek l E j o).obj K.obj))) :=
      hU.2 _ (hc _ (hext _ K.property))
    have ht : (systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj) ≫
        (P l E j o).map (c.r.inv.app K.obj) ≫
        s.inv.app ((shriek l E j o).obj K.obj) =
        SU.reduction.map ((openAdjunction l E j o).unit.app K.obj) := by
      rw [← hsu K.obj]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [(P l E j o).map_id]
      simp only [Category.id_comp, Iso.hom_inv_id_app]
      erw [Category.comp_id]
    dsimp only [bi, inverseUnitIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, asIso_inv, Iso.app_hom, uU, asIso_hom,
      isoWhiskerLeft_inv, whiskerLeft_app, Functor.comp_obj, ObjectProperty.ι_obj]
    simp only [← Functor.map_comp_assoc]
    rw [ht]
    exact @inverse_unit_natural _ _ _ _ _ _ SU.adjunction K.obj
      ((star l E j o).obj ((shriek l E j o).obj K.obj))
      ((openAdjunction l E j o).unit.app K.obj)
      (hU.2 _ (hc _ (hext _ K.property)))
  · intro H
    dsimp only [di, inverseUnitIso, NatIso.ofComponents_inv_app, Iso.trans_inv,
      Iso.symm_inv, Functor.mapIso_inv, asIso_hom, Iso.app_inv, uX, asIso_inv,
      isoWhiskerLeft_hom, whiskerLeft_app, Functor.comp_obj]
    exact @realize_counit_composite _ _ _ _ _ _ SX.adjunction _ H.obj _ _
      ((openAdjunction l E j o).counit.app H.obj)
      (c.r.hom.app ((star l E j o).obj H.obj))
      ((J l E j o).map (s.hom.app H.obj))
      ((systemAdjunction l E j o).counit.app (SX.reduction.obj H.obj))
      (hsc H.obj).symm (hX.2 H.obj H.property)
  · intro Q hQ hf hcomplete
    obtain ⟨cU, cX, hsquare⟩ := c.model Q hQ hf
    refine ⟨c.kflat Q hQ hf, _, _, cU.iso, cX.iso,
      AU.complexEvaluation l E Q, AX.complexEvaluation l E _,
      OpenSemilinearTensor.ordinaryChain l E j o AX AU c.ordinary Q,
      cU.presentation, cU.augmentation, cX.presentation, cX.augmentation, hsquare, ?_⟩
    intro n i
    exact c.components (Q.X i) n

/-- Strict completed open reduction, its inverse-unit realization, and adjunction
normalization. Source: Stacks 0GL1, 0E8I and 0941; `fix-prop-coherence`, open factor
(blueprint: lem-sf-integral-open-reduction-comparison).
Proof: choose the two reduction/total-limit calculi with their coherence packages.
Normalize the semilinear open localization on sections using the identity-block
case of block repetition. The simultaneous open tensor-model theorem then supplies
the strict reduction comparison on every flat-term K-flat representative, with its
specified coefficient components and its augmentation. Quasi-compact open extension
preserves the actual quotient completeness predicate: its exact termwise functor
preserves countable products and the uniformizer scalar, hence transports the
principal-completion construction. Normalized reconstruction makes the actual units
invertible on complete objects and the actual counits invertible on normalized
systems. The canonical restriction model supplies the inverse extension mate.
Restriction preserves completeness. Form inverse-unit realizations pointwise;
naturality makes them natural isomorphisms, and the mate unit/counit identities
and the adjunction triangle identities give all strict system and realized
unit/counit equations. Retain these equations in Comparison; obtain its
StrictModel directly from the same simultaneous tensor-model representatives.
No equality of derived morphisms is inferred from their finite evaluations. -/
theorem integralOpenReductionComparison [QuasiCompact j]
    (_hlX : IsUnit (l : Γ(X, ⊤))) (_hlU : IsUnit (l : Γ(U, ⊤))) :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SU : CoefficientDerivedSystemCalculus l E U)
      (_cX : CoefficientDerivedSystemCoherence l E X SX)
      (_cU : CoefficientDerivedSystemCoherence l E U SU)
      (o : Operations l E j) (tensor : TensorComparison l E j o),
      Nonempty (Comparison l E j o SX SU tensor) := by
  classical
  obtain ⟨SX, ⟨cX⟩⟩ := coefficientDerivedSystemEvaluationCalculus l E X
  obtain ⟨SU, ⟨cU⟩⟩ := coefficientDerivedSystemEvaluationCalculus l E U
  obtain ⟨sections, hsections⟩ := normalizedOpenSections l E j
  obtain ⟨o, AX, AU, tensor, _ho, ⟨c⟩⟩ :=
    OpenSemilinearTensor.openSemilinearTensorModel l E j _hlX _hlU SX SU cX cU
      sections hsections
  exact ⟨SX, SU, cX, cU, o, tensor,
    comparisonOfModel l E j _hlX _hlU SX SU o tensor AX AU c
      (integralOpenExtensionComplete l E j _hlX _hlU o)⟩

end WeilConjectures.IntegralOpenReduction
