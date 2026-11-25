/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenPrefixBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemClopenTailBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemIntrinsicLambdaExpansion

/-! Forward bridge equation for the proper/open lambda word.
(blueprint: lem-sf-integral-system-proper-open-lambda-bridge). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem BridgeWord.paste {C : Type*} [Category C] (d : BridgeWord C)
    (ho : d.f = d.a ≫ d.b ≫ d.c ≫ d.d ≫ d.e)
    (hz : d.g = d.x ≫ d.y ≫ d.z ≫ d.w ≫ d.n)
    (ht : d.c ≫ d.d ≫ d.e ≫ d.v = d.j ≫ d.k ≫ d.z ≫ d.w ≫ d.n)
    (hp : d.a ≫ d.b ≫ d.j ≫ d.k = d.t ≫ d.t' ≫ d.x ≫ d.y) :
    d.f ≫ d.v = d.t ≫ d.t' ≫ d.g := by
  calc
    d.f ≫ d.v = (d.a ≫ d.b) ≫ (d.c ≫ d.d ≫ d.e ≫ d.v) := by
      rw [ho]; simp only [Category.assoc]
    _ = (d.a ≫ d.b) ≫ (d.j ≫ d.k ≫ d.z ≫ d.w ≫ d.n) :=
      congrArg ((d.a ≫ d.b) ≫ ·) ht
    _ = (d.a ≫ d.b ≫ d.j ≫ d.k) ≫ (d.z ≫ d.w ≫ d.n) := by
      simp only [Category.assoc]
    _ = (d.t ≫ d.t' ≫ d.x ≫ d.y) ≫ (d.z ≫ d.w ≫ d.n) :=
      congrArg (· ≫ (d.z ≫ d.w ≫ d.n)) hp
    _ = d.t ≫ d.t' ≫ d.g := by rw [hz]; simp only [Category.assoc]

/-- The chosen proper/open lambda word transports to the intrinsic lambda word.
Source: Stacks 0F7B and blueprint fix-prop-coherence. The proof decomposes the word
into cartesian, restriction, clopen, and compositor factors, applies their bridge
squares, and pastes them. This is strictly the forward factor identity used by the
assigned adjunct theorem and contains no gamma or adjunct normalization.
(blueprint: lem-sf-integral-system-proper-open-lambda-bridge). -/
theorem properOpenLambda_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (properOpenLambda l E o c a k r p i h).hom.app M ≫ (b.push l E r).hom.app M =
      (pull l E i).map ((Operations.push l E o p).map ((b.shriek l E k).hom.app M) ≫
        (b.push l E p).hom.app
          ((ProEtale.SemilinearProperOpen.J (scalarRings l E)
            (scalarTransitions l E) k).obj M)) ≫
      (b.pull l E i).hom.app
        ((ProEtale.SemilinearProperOpen.J (scalarRings l E)
          (scalarTransitions l E) k ⋙ ProEtale.SemilinearProperOpen.R
            (scalarRings l E) (scalarTransitions l E) p).obj M) ≫
      (ProEtale.SemilinearProperOpen.lambda
        (scalarRings l E) (scalarTransitions l E) k r p i h).hom.app M := by
  let d := properOpenBridgeWord l E o c a b k r p i h M
  have he := lambdaWord_expansions l E o c a b k r p i h M
  have ht := clopenTail_bridge l E o c a b k r p i h M
  have hp := properOpenPrefix_bridge l E o c a b k r p i h M
  have hw := d.paste he.1 he.2 ht hp
  dsimp only [d] at hw
  unfold properOpenBridgeWord at hw
  exact hw

end WeilConjectures.IntegralSystemRealization
