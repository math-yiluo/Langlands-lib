/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralSystemNativeBridgeData

/-! The concrete morphism diagram for bridge pasting.
(blueprint: def-sf-integral-system-proper-open-bridge-word). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- A five-factor word and the smaller prefix and tail words used to compare it.
Source: blueprint fix-prop-coherence, proper/open lambda factors.
(blueprint: def-sf-integral-system-proper-open-bridge-word). -/
structure BridgeWord (C : Type w) [Category.{v} C] where
  A : C
  B : C
  D : C
  F : C
  G : C
  H : C
  I : C
  J : C
  K : C
  L : C
  N : C
  O : C
  P : C
  Q : C
  a : A ⟶ B
  b : B ⟶ D
  c : D ⟶ F
  d : F ⟶ G
  e : G ⟶ H
  v : H ⟶ I
  j : D ⟶ J
  k : J ⟶ K
  t : A ⟶ L
  t' : L ⟶ Q
  x : Q ⟶ N
  y : N ⟶ K
  z : K ⟶ O
  w : O ⟶ P
  n : P ⟶ I
  f : A ⟶ H
  g : Q ⟶ I

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual cartesian, restriction, clopen, compositor and bridge components.
Every field is constructed by the given operations; no witness is chosen.
Source: blueprint fix-prop-coherence, proper/open transport.
(blueprint: def-sf-integral-system-proper-open-bridge-word). -/
@[irreducible] def properOpenBridgeWord
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) : BridgeWord (System l E W) where
  A := _
  B := _
  D := _
  F := _
  G := _
  H := _
  I := _
  J := _
  K := _
  L := _
  N := _
  O := _
  P := _
  Q := _
  a := (cartesianConjugate l E o c a p i).hom.app ((Operations.shriek l E o k).obj M)
  b := (Operations.push l E o (pullback.snd p i)).map
    ((restrictFactor l E o c a k r p i h).hom.app M)
  c := (Operations.push l E o (pullback.snd p i)).map
    ((a.clopen (ProEtale.StrictTower.squareLift k r p i h)).hom.app M)
  d := (c.pushComp l E (ProEtale.StrictTower.squareLift k r p i h)
    (pullback.snd p i)).hom.app M
  e := (eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h))).hom.app M
  v := (nativeBridge l E o b r).hom.app M
  j := (nativeBridge l E o b (pullback.snd p i)).hom.app
    ((Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h)).obj M)
  k := (nativeR l E
    (pullback.snd p i)).map
      ((nativeShriek l E o b (ProEtale.StrictTower.squareLift k r p i h)).hom.app M)
  t := (pull l E i).map ((Operations.push l E o p).map ((nativeShriek l E o b k).hom.app M) ≫
    (nativeBridge l E o b p).hom.app ((nativeJ l E k).obj M))
  t' := (b.pull l E i).hom.app ((nativeJ l E k ⋙ nativeR l E p).obj M)
  x := (ProEtale.SemilinearProperOpen.cartesianConjugate (scalarRings l E)
    (scalarTransitions l E) p i).hom.app ((nativeJ l E k).obj M)
  y := (nativeR l E
    (pullback.snd p i)).map ((ProEtale.SemilinearProperOpen.restrictFactor
      (scalarRings l E) (scalarTransitions l E) k r p i h).hom.app M)
  z := (nativeR l E
    (pullback.snd p i)).map ((nativeOpen l E
      (ProEtale.StrictTower.squareLift k r p i h)).app M)
  w := (nativeComp l E
    (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i)).hom.app M
  n := nativeREq l E (pullback.lift_snd k r h) M
  f := (properOpenLambda l E o c a k r p i h).hom.app M
  g := (ProEtale.SemilinearProperOpen.lambda (scalarRings l E)
    (scalarTransitions l E) k r p i h).hom.app M

end WeilConjectures.IntegralSystemRealization
