/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # The finite-system compositor is the strict sequence compositor

Source: Stacks 0D6D and 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent finite systems with the positive uniformizer quotients are the strict
quotient systems on the ringed sequence site, and their inverse images are the same
left adjoints of the same sectionwise direct images. Both compositors are the mates of
the sectionwise fibre-product pasting map, hence they agree, before and after
localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite-system adjunction is the universal adjunction of the strict sequence
direct image.
Source: Stacks 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem finiteSystemAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystemAdjunction (integralSystemRings l E) (integralSystemTransition l E) f =
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f) :
        finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) f ⊣
          finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) f) :=
  rfl

-- Identify the category and functor data before comparing the mates. This keeps each
-- adjunction in its own presentation throughout the sectionwise calculation.
universe v₁ v₂ v₃ w₁ w₂ w₃ in
private theorem finiteSystemCompositor_heq_of_mates
    {C C' : Type w₁} {D D' : Type w₂} {F F' : Type w₃}
    {iC : Category.{v₁} C} {iD : Category.{v₂} D} {iF : Category.{v₃} F}
    {iC' : Category.{v₁} C'} {iD' : Category.{v₂} D'} {iF' : Category.{v₃} F'}
    (hC : C = C') (hD : D = D') (hF : F = F')
    (hiC : HEq iC iC') (hiD : HEq iD iD') (hiF : HEq iF iF')
    (Gk : D ⥤ C) (Gk' : D' ⥤ C') (Gh : F ⥤ D) (Gh' : F' ⥤ D') (Ghk : F ⥤ C)
    (Ghk' : F' ⥤ C')
    [raGk : Gk.IsRightAdjoint] [raGh : Gh.IsRightAdjoint] [raGhk : Ghk.IsRightAdjoint]
    [raGk' : Gk'.IsRightAdjoint] [raGh' : Gh'.IsRightAdjoint] [raGhk' : Ghk'.IsRightAdjoint]
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

private theorem finiteSystemComposition_heq {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    HEq (finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k)
      (integralComparisonSequenceComposition l E h k) := by
  have e1 := (finiteSystemComposition_existsUnique (integralSystemRings l E)
      (integralSystemTransition l E) h k).exists.choose_spec.choose_spec
  unfold finiteSystemAdjunction ProEtale.VaryingRing.moduleAdj at e1
  have e2 :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec.choose_spec
  -- Defer the equality proofs until both presentations have been inferred.
  refine finiteSystemCompositor_heq_of_mates
    (raGk := ProEtale.VaryingRing.push_isRightAdjoint _ _ k)
    (raGk' := integralComparisonSequenceRightAdjoint l E k)
    (raGh := ProEtale.VaryingRing.push_isRightAdjoint _ _ h)
    (raGh' := integralComparisonSequenceRightAdjoint l E h)
    (raGhk := ProEtale.VaryingRing.push_isRightAdjoint _ _ (h ≫ k))
    (raGhk' := integralComparisonSequenceRightAdjoint l E (h ≫ k))
    (by rfl) (by rfl) (by rfl) (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) k)
    (integralComparisonSequenceDirectImage l E k)
    (finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) h)
    (integralComparisonSequenceDirectImage l E h)
    (finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (integralComparisonSequenceDirectImage l E (h ≫ k))
    (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k)
    (integralComparisonSequenceComposition l E h k) _ _ e1.1 e2.1 ?_
  apply heq_of_eq
  apply Iso.ext
  ext M U x
  exact (e1.2 M U.unop.1 U.unop.2 x).trans (e2.2 M U.unop.1 U.unop.2 x).symm

/-- The finite-system compositor is the strict sequence compositor.
Source: Stacks 0D6D, 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: both are characterized as the unique mates of the sectionwise fibre-product
pasting isomorphism for the same direct images and adjunctions. -/
theorem finiteSystemComposition_eq {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k =
      integralComparisonSequenceComposition l E h k := by
  exact eq_of_heq (finiteSystemComposition_heq l E h k)

-- Localization respects these identifications, including the chosen derived categories.
universe v₁ v₂ v₃ w₁ w₂ w₃ t₁ t₂ t₃ in
private theorem finiteSystemDerivedCompositor_heq
    {C C' : Type w₁} {D D' : Type w₂} {E' E'' : Type w₃}
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
    [addF : F.Additive] [limF : Limits.PreservesFiniteLimits F]
    [colF : Limits.PreservesFiniteColimits F]
    [addG : G.Additive] [limG : Limits.PreservesFiniteLimits G]
    [colG : Limits.PreservesFiniteColimits G]
    [addF' : F'.Additive] [limF' : Limits.PreservesFiniteLimits F']
    [colF' : Limits.PreservesFiniteColimits F']
    [addG' : G'.Additive] [limG' : Limits.PreservesFiniteLimits G']
    [colG' : Limits.PreservesFiniteColimits G']
    (H : C ⥤ E') (H' : C' ⥤ E'')
    [addH : H.Additive] [limH : Limits.PreservesFiniteLimits H]
    [colH : Limits.PreservesFiniteColimits H]
    [addH' : H'.Additive] [limH' : Limits.PreservesFiniteLimits H']
    [colH' : Limits.PreservesFiniteColimits H']
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

private theorem finiteSystemDerivedComposition_heq {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    HEq (finiteSystemDerivedComposition (integralSystemRings l E)
      (integralSystemTransition l E) h k) (integralComparisonSystemComposition l E h k) := by
  -- Supply the exactness witnesses directly to avoid searching across presentations.
  exact finiteSystemDerivedCompositor_heq
    (addF := finiteSystemPullbackAdditive
      (integralSystemRings l E) (integralSystemTransition l E) k)
    (addF' := integralComparisonSequencePullbackAdditive l E k)
    (limF := finiteSystemPullbackLimits
      (integralSystemRings l E) (integralSystemTransition l E) k)
    (limF' := integralComparisonSequencePullbackLimits l E k)
    (colF := finiteSystemPullbackColimits
      (integralSystemRings l E) (integralSystemTransition l E) k)
    (colF' := integralComparisonSequencePullbackColimits l E k)
    (addG := finiteSystemPullbackAdditive
      (integralSystemRings l E) (integralSystemTransition l E) h)
    (addG' := integralComparisonSequencePullbackAdditive l E h)
    (limG := finiteSystemPullbackLimits
      (integralSystemRings l E) (integralSystemTransition l E) h)
    (limG' := integralComparisonSequencePullbackLimits l E h)
    (colG := finiteSystemPullbackColimits
      (integralSystemRings l E) (integralSystemTransition l E) h)
    (colG' := integralComparisonSequencePullbackColimits l E h)
    (addH := finiteSystemPullbackAdditive
      (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (addH' := integralComparisonSequencePullbackAdditive l E (h ≫ k))
    (limH := finiteSystemPullbackLimits
      (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (limH' := integralComparisonSequencePullbackLimits l E (h ≫ k))
    (colH := finiteSystemPullbackColimits
      (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (colH' := integralComparisonSequencePullbackColimits l E (h ≫ k))
    (F := finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) k)
    (F' := integralComparisonSequencePullback l E k)
    (G := finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) h)
    (G' := integralComparisonSequencePullback l E h)
    (H := finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k))
    (H' := integralComparisonSequencePullback l E (h ≫ k))
    (a := finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k)
    (a' := integralComparisonSequenceComposition l E h k)
    (by rfl) (by rfl) (by rfl)
    (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (finiteSystemComposition_heq l E h k)

/-- The derived finite-system compositor is the derived strict sequence compositor.
Source: Stacks 0D6D, 015F
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem finiteSystemDerivedComposition_eq {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemDerivedComposition (integralSystemRings l E) (integralSystemTransition l E) h k =
      integralComparisonSystemComposition l E h k := by
  exact eq_of_heq (finiteSystemDerivedComposition_heq l E h k)

end WeilConjectures
