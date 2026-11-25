/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueProperFormulas
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorProduct
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import all WeilConjectures.AlgebraicGeometry.FiniteStrataCompletion.FiniteStrataCompletionDetection
import all WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsIntegralFiniteModelCompleteness
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
/-!
# Proper base change with integral adic coefficients

Source: blueprint main-20261015, chap-Construction-of-f,
`sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.md`
(blueprint: proposition-proper-direct-image-constructible-complexes).

## Main statements

* `integralProperDirectImageAndFormulas`: proper direct image, derived Nakayama, and the
  proper base change and projection formula isomorphisms for integral coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.IsDerivedComplete

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem integral_complete_of_bounded_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : DerivedCategory (AdicCompletion.Modules l E T))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T K) :
    IsDerivedComplete l E T K := by
  let := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.integerRing l E) T).1
  obtain ⟨hi, ht⟩ := complete_triangulated l E T
  let := hi
  let := ht
  exact DerivedCategory.prop_of_bounded (IsDerivedComplete l E T)
    (IsConstantModelConstructible (DerivedNakayama.integerRing l E) T)
    (complete_sheaf l E T) K hK.1 hK.2

private theorem integral_pull_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (f : T ⟶ S)
    (K : DerivedCategory (AdicCompletion.Modules l E S))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S K) :
    IsDerivedComplete l E T
      ((upperStar (DerivedNakayama.integerRing l E) f).mapDerivedCategory.obj K) := by
  classical
  let R := DerivedNakayama.integerRing l E
  let C := T.affineCover.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage
  obtain ⟨P, hP, _, _, hres⟩ :=
    StrictCompletionRestriction.strict_completion_restriction_comparison l E
  apply (FiniteStrataCompletion.presentation_complete l E T (P T) (hP T) _).mpr
  apply ((condensed_cover_restriction_conservative (Mon.mk R) T C).1 _ _ _).mpr
  intro i
  let : IsAffine (C.X i) := by
    change IsAffine (T.affineCover.X i)
    infer_instance
  let : IsOpenImmersion (C.f i) := by
    change IsOpenImmersion (T.affineCover.f i)
    infer_instance
  have hi : IsImmersion (C.f i) := inferInstance
  obtain ⟨_, ⟨cmp⟩⟩ := hres (C.f i)
    (MorphismProperty.le_multiplicativeClosure _ _ (.inl hi))
  have hbc := pullback_bounded_constructible R (C.f i ≫ f)
    (fun M hM ↦ pullback_constructible R (C.f i ≫ f) M hM) K hK
  have hc := integral_complete_of_bounded_constructible l E (C.X i) _ hbc
  have he := (leftDerivedUpperStarIsoMapDerivedCategory R (C.f i ≫ f)).app K ≪≫
    (profinitePointModuleDerivedComp R (C.f i) f).app K
  have hc' := (FiniteStrataCompletion.complete_iso l E he).mp hc
  have hu := (FiniteStrataCompletion.presentation_complete l E (C.X i)
    (P (C.X i)) (hP (C.X i)) _).mp hc'
  apply (isIso_comp_right_iff _ (cmp.derived.hom.app _)).mp
  rw [cmp.unit]
  exact hu

/-- Proper direct image, derived Nakayama, and the two canonical proper formulas
for bounded constructible integral adic complexes.
Source: blueprint main-20261015, chap-Construction-of-f,
`sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.md`
(blueprint: proposition-proper-direct-image-constructible-complexes).

Proof:
1. The internal residue criterion gives completeness and a bounded constructible finite-Tor
   first reduction for K. Internal direct-image limits gives completeness of Rp_*K and
   the canonical first-reduction comparison. The existing proper integral finiteness proof
   gives bounded constructibility of Rp_*K.
2. The first-reduction Nakayama theorem gives vanishing of any complete complex with zero
   first reduction, without a boundedness hypothesis.
3. For an arbitrary map from a scheme T to a qcqs scheme, a bounded constructible integral
   input has complete pullback: on every affine chart of T, bounded constructible pullback
   and the qcqs completeness argument apply. The strict completion presentation commutes
   with the covering open immersions and its unit. Covering restrictions detect whether
   that unit is invertible, proving completeness on T. This does not require T to be
   finite type or quasi-compact.
4. Apply step 3 to g and g', and internal direct-image limits to p'. This makes both
   exchange endpoints complete, even for arbitrary base-changed schemes. Bounded
   constructible pullback, integral tensor closure, proper integral finiteness and qcqs
   completeness similarly make both projection endpoints complete.
5. The residue criterion puts the input first reductions in Dctf. The separate finite
   reduction step integralResidueProperFormulas identifies reduction of each canonical
   arrow with its finite-coefficient formula, through the normalized scalar, tensor,
   pullback and direct-image comparisons, and applies finite proper base change.
6. The first-reduction isomorphism criterion applied to the complete endpoints proves
   invertibility of the actual ambient exchange and ordinary uncompleted projection map.
-/
theorem integralProperDirectImageAndFormulas
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      IsDerivedComplete l E Y
        ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) ∧
      Nonempty
        ((AdicCompletion.derivedReduction l E Y 0).obj
            ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) ≅
          (moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) p).obj
            ((AdicCompletion.derivedReduction l E X 0).obj K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y
        ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K)) ∧
    (∀ (C : DerivedCategory (AdicCompletion.Modules l E X)),
      IsDerivedComplete l E X C →
      IsZero ((AdicCompletion.derivedReduction l E X 0).obj C) → IsZero C) ∧
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g)
      (K : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      IsIso ((condensedAmbientExchange (DerivedNakayama.integerRing l E) sq).app K)) ∧
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X))
      (M : DerivedCategory (AdicCompletion.Modules l E Y)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y M →
      IsIso (moduleObjectProjectionMap (DerivedNakayama.integerRing l E) p K M)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  have hl (y : Y) : IsUnit (l : Y.presheaf.stalk y) :=
    isUnit_natCast_stalk_of_ringChar_ne l Fact.out (Y ↘ Spec (.of k)) y
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨hχ, hpush⟩ := internal_integral_direct_image_limits l E p
    let := hχ
    obtain ⟨hcomplete, hiso⟩ := hpush K
    have hsource := ((internal_integral_residue_criterion l E X).1 K).mp hK
    exact ⟨hcomplete hsource.1, ⟨@asIso _ _ _ _ _ hiso⟩,
      proper_integralModel_bounded l E p hl K hK⟩
  · intro C hC hzero
    exact ((derived_nakayama_first_reduction l E X).1 C hC hzero).2
  · intro X' Y' g p' g' sq K hK
    have hpush := proper_integralModel_bounded l E p hl K hK
    have hleft := integral_pull_complete l E g _ hpush
    have hleft' := (FiniteStrataCompletion.complete_iso l E
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.integerRing l E) g).symm.app _)).mp hleft
    have hpull := integral_pull_complete l E g' K hK
    have hpull' := (FiniteStrataCompletion.complete_iso l E
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.integerRing l E) g').symm.app K)).mp hpull
    obtain ⟨hχ, hpush'⟩ := internal_integral_direct_image_limits l E p'
    let := hχ
    have hright := (hpush' _).1 hpull'
    apply (derived_nakayama_first_reduction l E Y').2.2.2 _ _
      ((condensedAmbientExchange (DerivedNakayama.integerRing l E) sq).app K)
      hleft' hright
    exact (integralResidueProperFormulas l E k p).1 g p' g' sq K
      (((internal_integral_residue_criterion l E X).1 K).mp hK).2
  · intro K M hK hM
    have htensor := (integralTensorProduct.{u, u + 1} l E k (ringChar k)
      (Fact.out : (ringChar k).Prime).pos
      (Fact.out : ringChar k ≠ l)).1
    have hpush := proper_integralModel_bounded l E p hl K hK
    have hleft := integral_complete_of_bounded_constructible l E Y _
      (htensor Y _ M hpush hM)
    have hpull := pullback_bounded_constructible (DerivedNakayama.integerRing l E) p
      (fun N hN ↦ pullback_constructible (DerivedNakayama.integerRing l E) p N hN)
      M hM
    have hright := integral_complete_of_bounded_constructible l E Y _
      (proper_integralModel_bounded l E p hl _ (htensor X K _ hK hpull))
    apply (derived_nakayama_first_reduction l E Y).2.2.2 _ _
      (moduleObjectProjectionMap (DerivedNakayama.integerRing l E) p K M)
      hleft hright
    exact (integralResidueProperFormulas l E k p).2 K M
      (((internal_integral_residue_criterion l E X).1 K).mp hK).2
      (((internal_integral_residue_criterion l E Y).1 M).mp hM).2

end AlgebraicGeometry.ProEtale.CondensedRing
