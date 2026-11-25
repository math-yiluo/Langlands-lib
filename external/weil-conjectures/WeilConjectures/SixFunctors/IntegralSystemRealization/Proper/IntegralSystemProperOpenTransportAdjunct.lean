/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportAdjunctBridge

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

structure ProperOpenTransportAdjunct (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o) where
  gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p
  adjunct : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (o.extension i).adj.homEquiv _ _ ((gamma k r p i h).app M) =
        (properOpenLambda l E o c a k r p i h).inv.app M

/-- Transported gamma through the canonical bridge. -/
def transportedGamma (o : Operations l E) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
      Operations.shriek l E o k ⋙ Operations.push l E o p := by
  let es : Operations.push l E o r ⋙ Operations.shriek l E o i ≅
      ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r ⋙
        ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i :=
    Functor.isoWhiskerRight (b.push l E r) _ ≪≫
      Functor.isoWhiskerLeft _ (b.shriek l E i)
  let et : ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) k ⋙
      ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p ≅
      Operations.shriek l E o k ⋙ Operations.push l E o p :=
    Functor.isoWhiskerLeft _ (b.push l E p).symm ≪≫
      Functor.isoWhiskerRight (b.shriek l E k).symm _
  exact es.hom ≫ ProEtale.SemilinearProperOpen.gamma
    (scalarRings l E) (scalarTransitions l E) k r p i h ≫ et.hom

/--
Adjunct normalization for the bridge-transported intrinsic gamma.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0F7B and 07A7.
The proof transports the intrinsic `gamma_adjunct` equation across the bridge
isomorphisms and identifies the resulting mate with `properOpenLambda`.
(blueprint: lem-sf-integral-system-proper-open-transport-adjunct-normalization)
-/
theorem transportedGamma_adjunct (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o) :
    ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (o.extension i).adj.homEquiv _ _
          ((transportedGamma l E o b k r p i h).app M) =
        (properOpenLambda l E o c a k r p i h).inv.app M := by
  intro U V W Z k r p i hk hi qk qi hr hp h M
  apply (cancel_mono ((b.pull l E i).hom.app
    ((Operations.shriek l E o k ⋙ Operations.push l E o p).obj M))).1
  rw [transportedGamma]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Category.assoc]
  exact transportedGamma_adjunct_bridge l E o c a b k r p i h M

/-- Existence of the adjunct-normalized transported gamma.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0F7B and 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-adjunct).
-/
theorem integralSystemProperOpenTransportAdjunct (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) (b : CanonicalBridge l E o) :
    Nonempty (ProperOpenTransportAdjunct l E o c a b) := by
  refine ⟨{ gamma := transportedGamma l E o b, adjunct := ?_ }⟩
  exact transportedGamma_adjunct l E o c a b

end WeilConjectures.IntegralSystemRealization
