/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackSystemModels
public import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence

/-! # Scalar extension carries the integral pullback compositor: heterogeneous-equality lemmas

Source: Stacks Project, Tags 06YY, 07A4, 0941 and 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).

For a coefficient inclusion E to L, completed scalar extension carries the specified
integral composition comparison at E to the one at L, conjugated by the canonical
scalar/pullback comparisons. Both sides are compared after the fully faithful coherent
reduction at L: the system-level composition clause of integralPullbackComposition at
E and at L, the system scalar comparison, the pullback/scalar square of
scalarExtensionTowerCoherence, and whole-system mixed coherence.
The rationalized statement follows by localization on pure tensors.

This file holds the compositor/derived heterogeneous-equality lemmas used by
IntegralPullbackCompositionScalar.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Composition

universe v₁ v₂ v₃ w₁ w₂ w₃ in
/-- Mates under equal right adjoints, stated across two presentations of the categories:
if the right-adjoint data agree up to the displayed equalities and the two mates agree,
then the left-adjoint comparisons agree. Source: elementary category theory
(blueprint: lem-pod-integral-pullback-composition-scalar). Proof: substitute all
equalities and use injectivity of conjugateIsoEquiv. -/
private theorem compositor_heq {C C' : Type w₁} {D D' : Type w₂} {F F' : Type w₃}
    {iC : Category.{v₁} C} {iD : Category.{v₂} D} {iF : Category.{v₃} F}
    {iC' : Category.{v₁} C'} {iD' : Category.{v₂} D'} {iF' : Category.{v₃} F'}
    (hC : C = C') (hD : D = D') (hF : F = F')
    (hiC : HEq iC iC') (hiD : HEq iD iD') (hiF : HEq iF iF')
    (Gk : D ⥤ C) (Gk' : D' ⥤ C') (Gh : F ⥤ D) (Gh' : F' ⥤ D') (Ghk : F ⥤ C)
    (Ghk' : F' ⥤ C')
    [Gk.IsRightAdjoint] [Gh.IsRightAdjoint] [Ghk.IsRightAdjoint]
    [Gk'.IsRightAdjoint] [Gh'.IsRightAdjoint] [Ghk'.IsRightAdjoint]
    (ek : HEq Gk Gk') (eh : HEq Gh Gh') (ehk : HEq Ghk Ghk')
    (a : Ghk.leftAdjoint ≅ Gk.leftAdjoint ⋙ Gh.leftAdjoint)
    (a' : Ghk'.leftAdjoint ≅ Gk'.leftAdjoint ⋙ Gh'.leftAdjoint)
    (d : Gh ⋙ Gk ≅ Ghk) (d' : Gh' ⋙ Gk' ≅ Ghk')
    (ha : conjugateIsoEquiv ((Adjunction.ofIsRightAdjoint Gk).comp
      (Adjunction.ofIsRightAdjoint Gh)) (Adjunction.ofIsRightAdjoint Ghk) a = d)
    (ha' : conjugateIsoEquiv ((Adjunction.ofIsRightAdjoint Gk').comp
      (Adjunction.ofIsRightAdjoint Gh')) (Adjunction.ofIsRightAdjoint Ghk') a' = d')
    (hd : HEq d d') :
    HEq a a' := by
  subst hC hD hF
  obtain rfl := eq_of_heq hiC
  obtain rfl := eq_of_heq hiD
  obtain rfl := eq_of_heq hiF
  obtain rfl := eq_of_heq ek
  obtain rfl := eq_of_heq eh
  obtain rfl := eq_of_heq ehk
  apply heq_of_eq
  apply (conjugateIsoEquiv ((Adjunction.ofIsRightAdjoint Gk).comp
      (Adjunction.ofIsRightAdjoint Gh)) (Adjunction.ofIsRightAdjoint Ghk)).injective
  rw [ha, ha', eq_of_heq hd]

-- Every comparison of the two presentations is made by `rfl` with transparency checks
-- relaxed, inside the separate equality arguments; the mate equations are used at their
-- own presentations, so no cross-presentation unification is needed.
/-- The ordinary composition comparisons of finite-system and integral-comparison inverse
image agree (heterogeneous form): both are the conjugate of the same sectionwise
fibre-product comparison.
Source: Stacks 03D8, 0D6D (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: the direct images agree definitionally; apply compositor_heq to the two
defining mate equations and compare the direct-image composites sectionwise. -/
theorem finiteSystemComposition_heq_integralComparison {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    HEq (finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k)
      (integralComparisonSequenceComposition l E h k) := by
  have e1 := (finiteSystemComposition_existsUnique (integralSystemRings l E)
      (integralSystemTransition l E) h k).exists.choose_spec.choose_spec
  unfold finiteSystemAdjunction ProEtale.VaryingRing.moduleAdj at e1
  have e2 :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec.choose_spec
  refine (compositor_heq (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in exact HEq.rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in exact HEq.rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in exact HEq.rfl)
    (finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) k)
    (integralComparisonSequenceDirectImage l E k)
    (finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) h)
    (integralComparisonSequenceDirectImage l E h)
    (finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (integralComparisonSequenceDirectImage l E (h ≫ k))
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in exact HEq.rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in exact HEq.rfl)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in exact HEq.rfl)
    (finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k)
    (integralComparisonSequenceComposition l E h k) _ _ e1.1 e2.1 ?_)
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  apply heq_of_eq
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  apply Iso.ext
  ext M U x
  exact (e1.2 M U.unop.1 U.unop.2 x).trans (e2.2 M U.unop.1 U.unop.2 x).symm

/-- The ordinary composition comparisons of finite-system and integral-comparison inverse
image agree: both are the conjugate of the same sectionwise fibre-product comparison.
Source: Stacks 03D8, 0D6D (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: finiteSystemComposition_heq_integralComparison. -/
theorem finiteSystemComposition_eq_integralComparison {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k =
      integralComparisonSequenceComposition l E h k :=
  eq_of_heq (finiteSystemComposition_heq_integralComparison l E h k)

universe v₁ v₂ v₃ w₁ w₂ w₃ t₁ t₂ t₃ in
/-- Derived composition comparisons across two presentations. Source: elementary
(blueprint: lem-pod-integral-pullback-composition-scalar). Proof: substitute. -/
private theorem derivedCompositor_heq {C C' : Type w₁} {D D' : Type w₂} {E' E'' : Type w₃}
    [iC : Category.{v₁} C] [iC' : Category.{v₁} C'] [iD : Category.{v₂} D]
    [iD' : Category.{v₂} D'] [iE : Category.{v₃} E'] [iE' : Category.{v₃} E'']
    [aC : Abelian C] [aC' : Abelian C'] [aD : Abelian D] [aD' : Abelian D']
    [aE : Abelian E'] [aE' : Abelian E'']
    [dC : HasDerivedCategory.{t₁} C] [dC' : HasDerivedCategory.{t₁} C']
    [dD : HasDerivedCategory.{t₂} D] [dD' : HasDerivedCategory.{t₂} D']
    [dE : HasDerivedCategory.{t₃} E'] [dE' : HasDerivedCategory.{t₃} E'']
    (hC : C = C') (hD : D = D') (hE : E' = E'')
    (hiC : HEq iC iC') (hiD : HEq iD iD') (hiE : HEq iE iE')
    (haC : HEq aC aC') (haD : HEq aD aD') (haE : HEq aE aE')
    (hdC : HEq dC dC') (hdD : HEq dD dD') (hdE : HEq dE dE')
    (F : C ⥤ D) (F' : C' ⥤ D') (G : D ⥤ E') (G' : D' ⥤ E'')
    [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [F'.Additive] [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
    [G'.Additive] [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
    (H : C ⥤ E') (H' : C' ⥤ E'')
    [H.Additive] [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [H'.Additive] [Limits.PreservesFiniteLimits H'] [Limits.PreservesFiniteColimits H']
    (eF : HEq F F') (eG : HEq G G') (eH : HEq H H')
    (a : H ≅ F ⋙ G) (a' : H' ≅ F' ⋙ G') (ha : HEq a a') :
    HEq (Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm)
      (Functor.mapDerivedCategoryNatIso a' ≪≫ (Functor.mapDerivedCategoryCompIso F' G').symm) := by
  subst hC hD hE
  obtain rfl := eq_of_heq hiC
  obtain rfl := eq_of_heq hiD
  obtain rfl := eq_of_heq hiE
  obtain rfl := eq_of_heq haC
  obtain rfl := eq_of_heq haD
  obtain rfl := eq_of_heq haE
  obtain rfl := eq_of_heq hdC
  obtain rfl := eq_of_heq hdD
  obtain rfl := eq_of_heq hdE
  obtain rfl := eq_of_heq eF
  obtain rfl := eq_of_heq eG
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq ha
  rfl

universe v₁ v₂ v₃ w₁ w₂ w₃ t₁ t₂ t₃ in
/-- The forward maps of the two derived compositors agree across presentations. -/
private theorem derivedCompositor_hom_heq {C C' : Type w₁} {D D' : Type w₂} {E' E'' : Type w₃}
    [iC : Category.{v₁} C] [iC' : Category.{v₁} C'] [iD : Category.{v₂} D]
    [iD' : Category.{v₂} D'] [iE : Category.{v₃} E'] [iE' : Category.{v₃} E'']
    [aC : Abelian C] [aC' : Abelian C'] [aD : Abelian D] [aD' : Abelian D']
    [aE : Abelian E'] [aE' : Abelian E'']
    [dC : HasDerivedCategory.{t₁} C] [dC' : HasDerivedCategory.{t₁} C']
    [dD : HasDerivedCategory.{t₂} D] [dD' : HasDerivedCategory.{t₂} D']
    [dE : HasDerivedCategory.{t₃} E'] [dE' : HasDerivedCategory.{t₃} E'']
    (hC : C = C') (hD : D = D') (hE : E' = E'')
    (hiC : HEq iC iC') (hiD : HEq iD iD') (hiE : HEq iE iE')
    (haC : HEq aC aC') (haD : HEq aD aD') (haE : HEq aE aE')
    (hdC : HEq dC dC') (hdD : HEq dD dD') (hdE : HEq dE dE')
    (F : C ⥤ D) (F' : C' ⥤ D') (G : D ⥤ E') (G' : D' ⥤ E'')
    [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [F'.Additive] [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
    [G'.Additive] [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
    (H : C ⥤ E') (H' : C' ⥤ E'')
    [H.Additive] [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [H'.Additive] [Limits.PreservesFiniteLimits H'] [Limits.PreservesFiniteColimits H']
    (eF : HEq F F') (eG : HEq G G') (eH : HEq H H')
    (a : H ≅ F ⋙ G) (a' : H' ≅ F' ⋙ G') (ha : HEq a a') :
    HEq (Functor.mapDerivedCategoryNatIso a ≪≫
      (Functor.mapDerivedCategoryCompIso F G).symm).hom
      (Functor.mapDerivedCategoryNatIso a' ≪≫
        (Functor.mapDerivedCategoryCompIso F' G').symm).hom := by
  have he := derivedCompositor_heq hC hD hE hiC hiD hiE haC haD haE hdC hdD hdE
    F F' G G' H H' eF eG eH a a' ha
  subst hC hD hE
  obtain rfl := eq_of_heq hiC
  obtain rfl := eq_of_heq hiD
  obtain rfl := eq_of_heq hiE
  obtain rfl := eq_of_heq haC
  obtain rfl := eq_of_heq haD
  obtain rfl := eq_of_heq haE
  obtain rfl := eq_of_heq hdC
  obtain rfl := eq_of_heq hdD
  obtain rfl := eq_of_heq hdE
  obtain rfl := eq_of_heq eF
  obtain rfl := eq_of_heq eG
  obtain rfl := eq_of_heq eH
  exact heq_of_eq (congrArg Iso.hom (eq_of_heq he))

/-- Compare the ordinary inverse images once, before passing to derived categories. -/
private theorem finiteSystemPullback_heq_integralComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) f)
      (integralComparisonSequencePullback l E f) := by
  apply HEq.rfl

/-- The finite-system composition comparison of integral pullback is the whole-system
comparison of the integral comparison sequence systems.
Source: Stacks 03D8, 0D6D (blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: both are the localizations of the same ordinary comparison. -/
theorem finiteSystemDerivedComposition_eq_integralComparison {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemDerivedComposition (integralSystemRings l E) (integralSystemTransition l E) h k =
      integralComparisonSystemComposition l E h k := by
  have hh := derivedCompositor_hom_heq
    (dC := SemilinearSections.hasDerived _ _)
    (dD := SemilinearSections.hasDerived _ _)
    (dE := SemilinearSections.hasDerived _ _)
    (F := finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) k)
    (F' := integralComparisonSequencePullback l E k)
    (G := finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) h)
    (G' := integralComparisonSequencePullback l E h)
    (H := finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (H' := integralComparisonSequencePullback l E (h ≫ k))
    (a := finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k)
    (a' := integralComparisonSequenceComposition l E h k)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      apply HEq.rfl) (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact finiteSystemPullback_heq_integralComparison l E k)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact finiteSystemPullback_heq_integralComparison l E h)
    (by set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact finiteSystemPullback_heq_integralComparison l E (h ≫ k))
    (finiteSystemComposition_heq_integralComparison l E h k)
  -- Compare forward maps before using extensionality, and unfold the presentation
  -- aliases explicitly when matching their dependent morphism types.
  with_unfolding_all exact Iso.ext (eq_of_heq hh)

end Composition

end WeilConjectures
