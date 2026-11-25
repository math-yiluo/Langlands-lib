/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence

/-! # A component of strict quotient-system coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] sequenceDirectComp

private theorem sequenceComp_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :
    integralComparisonSequenceComposition l E h k =
      (Adjunction.leftAdjointCompIso
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k))
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k)))
        (sequenceDirectComp l E h k)).symm := by
  unfold integralComparisonSequenceComposition
  obtain ⟨d, he, hd⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec
  have hde : d = sequenceDirectComp l E h k := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hd M U.unop.1 U.unop.2 x).trans
      (sequenceDirectComp_apply l E h k M U x).symm
  apply (conjugateIsoEquiv
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k)))).injective
  rw [he, hde]
  apply Iso.ext
  exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).symm

private abbrev sequenceAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)

private theorem sequenceDirectTransport (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} {f g : X ⟶ Y} (e : f = g)
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : Y.ProEt)
    (m : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U))) :
    ((eqToIso (congrArg (integralComparisonSequenceDirectImage l E) e)).hom.app N).val.app
        (op (n, U)) m =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
        (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U) e.symm))).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem sequenceDirectMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} (f : X ⟶ Y)
    {N N' : coefficientSequenceModules l E X} (a : N ⟶ N') (n : ℕ) (U : Y.ProEt)
    (m : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U))) :
    (((integralComparisonSequenceDirectImage l E f).map a).val.app (op (n, U))) m =
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U)) m := rfl

private theorem sequenceDirectRestriction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E X) (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, V))) :
    (((integralComparisonSequenceDirectImage l E f).obj N).val.map
      (CategoryTheory.Prod.mkHom (𝟙 n) a).op) m =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n) ((Scheme.proEtaleBaseChange f).map a)).op m := rfl

private def genericSiteComp
    {C : Type*} [Category C] [HasPullbacks C] (P Q : MorphismProperty C)
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MorphismProperty.Over.pullback P Q (f ≫ g) ≅
      MorphismProperty.Over.pullback P Q g ⋙ MorphismProperty.Over.pullback P Q f :=
  MorphismProperty.Over.pullbackComp f g

private def siteComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.proEtaleBaseChange (f ≫ g) ≅
      Scheme.proEtaleBaseChange g ⋙ Scheme.proEtaleBaseChange f :=
  genericSiteComp (@WeaklyEtale) ⊤ f g

private theorem sequenceDirectCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y Z W : Scheme.{t}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) :
    Functor.isoWhiskerLeft (integralComparisonSequenceDirectImage l E j)
        (sequenceDirectComp l E h k) ≪≫ sequenceDirectComp l E j (h ≫ k) =
      (Functor.associator (integralComparisonSequenceDirectImage l E j)
        (integralComparisonSequenceDirectImage l E h)
        (integralComparisonSequenceDirectImage l E k)).symm ≪≫
        Functor.isoWhiskerRight (sequenceDirectComp l E j h)
          (integralComparisonSequenceDirectImage l E k) ≪≫ sequenceDirectComp l E (j ≫ h) k ≪≫
        eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, U⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  erw [sequenceDirectMap l E k ((sequenceDirectComp l E j h).hom.app N) n U]
  erw [sequenceDirectComp_apply l E j h N (op (n, (Scheme.proEtaleBaseChange k).obj U))]
  erw [sequenceDirectComp_apply l E (j ≫ h) k N (op (n, U))]
  conv_rhs => erw [sequenceDirectTransport l E (Category.assoc j h k) N n U]
  conv_lhs => erw [sequenceDirectComp_apply l E h k
    ((integralComparisonSequenceDirectImage l E j).obj N) (op (n, U)) m]
  conv_lhs => erw [sequenceDirectComp_apply l E j (h ≫ k) N (op (n, U))]
  let a := (siteComp j (h ≫ k)).hom.app U
  let b := (siteComp h k).hom.app U
  refine Eq.trans (b := N.val.map (CategoryTheory.Prod.mkHom (𝟙 n) a).op
    (N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
      ((Scheme.proEtaleBaseChange j).map b)).op m)) ?_ ?_
  · dsimp only [a, b, siteComp, genericSiteComp]
    exact congrArg (fun z ↦ N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
      ((siteComp j (h ≫ k)).hom.app U)).op z)
      (sequenceDirectRestriction l E j N n ((siteComp h k).hom.app U) m)
  · apply restriction_pasting N.val
    apply CategoryTheory.Prod.hom_ext
    · rfl
    · dsimp only [CategoryTheory.prod_comp, CategoryTheory.Prod.mkHom, a, b,
        siteComp, genericSiteComp]
      exact site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U

private theorem sequenceOrdinaryCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z W : Scheme.{t}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (M : coefficientSequenceModules l E X) :
    (integralComparisonSequenceComposition l E j (h ≫ k)).hom.app M ≫
        (integralComparisonSequencePullback l E j).map
          ((integralComparisonSequenceComposition l E h k).hom.app M) =
      (eqToIso (congrArg (integralComparisonSequencePullback l E)
        (Category.assoc j h k).symm)).hom.app M ≫
        (integralComparisonSequenceComposition l E (j ≫ h) k).hom.app M ≫
        (integralComparisonSequenceComposition l E j h).hom.app
          ((integralComparisonSequencePullback l E k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (sequenceAdjunction l E k) (sequenceAdjunction l E h)
    (sequenceAdjunction l E j)
    (sequenceAdjunction l E (h ≫ k)) (sequenceAdjunction l E (j ≫ h))
    (sequenceAdjunction l E (j ≫ h ≫ k))
    (sequenceDirectComp l E h k) (sequenceDirectComp l E j h)
    ((sequenceDirectComp l E (j ≫ h) k) ≪≫
      eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.assoc j h k)))
    (sequenceDirectComp l E j (h ≫ k)) (sequenceDirectCoherence l E j h k)
  have ht := mate_transport (fun f ↦ (integralComparisonSequenceDirectImage l E f).leftAdjoint)
    (integralComparisonSequenceDirectImage l E) (fun f ↦ sequenceAdjunction l E f)
    (sequenceAdjunction l E k) (sequenceAdjunction l E (j ≫ h))
    (Category.assoc j h k)
    (sequenceDirectComp l E (j ≫ h) k)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  dsimp only [sequenceAdjunction] at hi
  dsimp only [integralComparisonSequencePullback]
  simp only [sequenceComp_eq,
    Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.comp_id, Category.assoc, eqToIso.inv,
    Functor.comp_obj, eqToHom_app] at hi ⊢
  exact hi.symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedSequenceTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (integralComparisonSequencePullback l E) e))).hom =
      eqToHom (congrArg (integralComparisonDerivedSequencePullback l E) e) := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

/-- Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
(blueprint: lem-trf-sequence-derived-associativity).
Proof: Apply the ordinary three-arrow coherence equation to the exact sequence pullback functors.
The comparison map of the derived functor construction commutes with composition and equality
transport. Whisker the ordinary equation with the localization, replace each comparison by its
defining derived comparison, and cancel the canonical localization isomorphisms. This gives the
displayed equation with the associativity equality transported in the indicated direction. -/
theorem sequenceDerivedCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y Z W V : Scheme.{t}} (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
    (S : coefficientSequenceDerived l E V) :
    (eqToHom (congrArg (integralComparisonDerivedSequencePullback l E)
      (Category.assoc j h k))).app S ≫
      (integralComparisonSystemComposition l E j (h ≫ k)).hom.app S ≫
      (integralComparisonDerivedSequencePullback l E j).map
        ((integralComparisonSystemComposition l E h k).hom.app S) =
      (integralComparisonSystemComposition l E (j ≫ h) k).hom.app S ≫
      (integralComparisonSystemComposition l E j h).hom.app
        ((integralComparisonDerivedSequencePullback l E k).obj S) := by
  let F := integralComparisonSequencePullback l E k
  let G := integralComparisonSequencePullback l E h
  let H := integralComparisonSequencePullback l E j
  let F02 := integralComparisonSequencePullback l E (h ≫ k)
  let F13 := integralComparisonSequencePullback l E (j ≫ h)
  let a02 := integralComparisonSequenceComposition l E h k
  let a13 := integralComparisonSequenceComposition l E j h
  let a0 := integralComparisonSequenceComposition l E j (h ≫ k)
  let a1 := integralComparisonSequenceComposition l E (j ≫ h) k
  let e := eqToIso (congrArg (integralComparisonSequencePullback l E) (Category.assoc j h k).symm)
  have ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13 := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact sequenceOrdinaryCoherence l E j h k N
  have hh := descend_coherence F G H F02 F13
    (integralComparisonSequencePullback l E (j ≫ h ≫ k))
    (integralComparisonSequencePullback l E ((j ≫ h) ≫ k)) a02 a13 a0 a1 e ho
  have hm := NatTrans.congr_app hh S
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  have he := congrArg (fun t ↦ t.app S)
    (derivedSequenceTransport l E (Category.assoc j h k).symm)
  change (Functor.mapDerivedCategoryNatIso e).hom.app S = _ at he
  rw [he] at hm
  let transport := eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
    (Category.assoc j h k).symm)
  have hm' : (integralComparisonSystemComposition l E j (h ≫ k)).hom.app S ≫
      (integralComparisonDerivedSequencePullback l E j).map
        ((integralComparisonSystemComposition l E h k).hom.app S) =
      transport.hom.app S ≫ (integralComparisonSystemComposition l E (j ≫ h) k).hom.app S ≫
        (integralComparisonSystemComposition l E j h).hom.app
          ((integralComparisonDerivedSequencePullback l E k).obj S) := by
    dsimp only [F, G, H, F02, F13, a0, a1, a02, a13] at hm
    dsimp only [transport, eqToIso]
    simpa only [integralComparisonSystemComposition, integralComparisonDerivedSequencePullback,
      Functor.comp_obj,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using hm
  have hf := congrArg (fun t ↦ transport.inv.app S ≫ t) hm'
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hf
  simpa only [Category.assoc, transport, eqToIso.inv] using hf

end WeilConjectures
