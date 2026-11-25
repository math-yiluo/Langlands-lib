/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.HorizontalMateTransport
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralSystemOpenCompositorBridge

/-! Horizontal pasting for the canonically transported proper/open mate. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
private structure HorizontalData
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F] where
  K : A ⥤ B
  L : B ⥤ E
  I : C ⥤ D
  J : D ⥤ F
  R : A ⥤ C
  P : B ⥤ D
  Q : E ⥤ F
  Kc : A ⥤ E
  Ic : C ⥤ F
  ck : K ⋙ L ≅ Kc
  ci : I ⋙ J ≅ Ic
  g₁ : R ⋙ I ⟶ K ⋙ P
  g₂ : P ⋙ J ⟶ L ⋙ Q
  g₀ : R ⋙ Ic ⟶ Kc ⋙ Q
  horizontal (M : A) :
    ci.hom.app (R.obj M) ≫ g₀.app M ≫ Q.map (ck.inv.app M) =
      J.map (g₁.app M) ≫ g₂.app (K.obj M)

private structure HorizontalBridge
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (d : HorizontalData (A := A) (B := B) (C := C) (D := D) (E := E) (F := F))
    (K : A ⥤ B) (L : B ⥤ E) (I : C ⥤ D) (J : D ⥤ F)
    (R : A ⥤ C) (P : B ⥤ D) (Q : E ⥤ F) (Kc : A ⥤ E) (Ic : C ⥤ F) where
  eK : K ≅ d.K
  eL : L ≅ d.L
  eI : I ≅ d.I
  eJ : J ≅ d.J
  eR : R ≅ d.R
  eP : P ≅ d.P
  eQ : Q ≅ d.Q
  eKc : Kc ≅ d.Kc
  eIc : Ic ≅ d.Ic

private theorem transport_horizontal_data
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {K : A ⥤ B} {L : B ⥤ E} {I : C ⥤ D} {J : D ⥤ F}
    {R : A ⥤ C} {P : B ⥤ D} {Q : E ⥤ F} {Kc : A ⥤ E} {Ic : C ⥤ F}
    (d : HorizontalData (A := A) (B := B) (C := C) (D := D) (E := E) (F := F))
    (v : HorizontalBridge d K L I J R P Q Kc Ic)
    (ck : K ⋙ L ≅ Kc) (ci : I ⋙ J ≅ Ic)
    (g₁ : R ⋙ I ⟶ K ⋙ P) (g₂ : P ⋙ J ⟶ L ⋙ Q) (g₀ : R ⋙ Ic ⟶ Kc ⋙ Q)
    (hk : ∀ M, ck.hom.app M ≫ v.eKc.hom.app M =
      v.eL.hom.app (K.obj M) ≫ d.L.map (v.eK.hom.app M) ≫ d.ck.hom.app M)
    (hi : ∀ M, ci.hom.app M ≫ v.eIc.hom.app M =
      v.eJ.hom.app (I.obj M) ≫ d.J.map (v.eI.hom.app M) ≫ d.ci.hom.app M)
    (h₁ : ∀ M, g₁.app M ≫ v.eP.hom.app (K.obj M) ≫ d.P.map (v.eK.hom.app M) =
      v.eI.hom.app (R.obj M) ≫ d.I.map (v.eR.hom.app M) ≫ d.g₁.app M)
    (h₂ : ∀ M, g₂.app M ≫ v.eQ.hom.app (L.obj M) ≫ d.Q.map (v.eL.hom.app M) =
      v.eJ.hom.app (P.obj M) ≫ d.J.map (v.eP.hom.app M) ≫ d.g₂.app M)
    (h₀ : ∀ M, g₀.app M ≫ v.eQ.hom.app (Kc.obj M) ≫ d.Q.map (v.eKc.hom.app M) =
      v.eIc.hom.app (R.obj M) ≫ d.Ic.map (v.eR.hom.app M) ≫ d.g₀.app M)
    (M : A) :
    ci.hom.app (R.obj M) ≫ g₀.app M ≫ Q.map (ck.inv.app M) =
      J.map (g₁.app M) ≫ g₂.app (K.obj M) := by
  exact horizontalMateTransport v.eK v.eL v.eI v.eJ v.eR v.eP v.eQ v.eKc v.eIc
    ck ci g₁ g₂ g₀ hk hi h₁ h₂ h₀ M (d.horizontal M)

private structure HorizontalWitness
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {K : A ⥤ B} {L : B ⥤ E} {I : C ⥤ D} {J : D ⥤ F}
    {R : A ⥤ C} {P : B ⥤ D} {Q : E ⥤ F} {Kc : A ⥤ E} {Ic : C ⥤ F}
    (ck : K ⋙ L ≅ Kc) (ci : I ⋙ J ≅ Ic)
    (g₁ : R ⋙ I ⟶ K ⋙ P) (g₂ : P ⋙ J ⟶ L ⋙ Q) (g₀ : R ⋙ Ic ⟶ Kc ⋙ Q)
    where
  d : HorizontalData (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
  v : HorizontalBridge d K L I J R P Q Kc Ic
  hk : ∀ M, ck.hom.app M ≫ v.eKc.hom.app M =
      v.eL.hom.app (K.obj M) ≫ d.L.map (v.eK.hom.app M) ≫ d.ck.hom.app M
  hi : ∀ M, ci.hom.app M ≫ v.eIc.hom.app M =
      v.eJ.hom.app (I.obj M) ≫ d.J.map (v.eI.hom.app M) ≫ d.ci.hom.app M
  h₁ : ∀ M, g₁.app M ≫ v.eP.hom.app (K.obj M) ≫ d.P.map (v.eK.hom.app M) =
      v.eI.hom.app (R.obj M) ≫ d.I.map (v.eR.hom.app M) ≫ d.g₁.app M
  h₂ : ∀ M, g₂.app M ≫ v.eQ.hom.app (L.obj M) ≫ d.Q.map (v.eL.hom.app M) =
      v.eJ.hom.app (P.obj M) ≫ d.J.map (v.eP.hom.app M) ≫ d.g₂.app M
  h₀ : ∀ M, g₀.app M ≫ v.eQ.hom.app (Kc.obj M) ≫ d.Q.map (v.eKc.hom.app M) =
      v.eIc.hom.app (R.obj M) ≫ d.Ic.map (v.eR.hom.app M) ≫ d.g₀.app M

private def nativeHorizontalData (C₀ : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, C₀ (n + 1) ⟶ C₀ n)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
    (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) :
    HorizontalData
      (A := ProEtale.SemilinearProperOpen.Derived C₀ τ A)
      (B := ProEtale.SemilinearProperOpen.Derived C₀ τ B₀)
      (C := ProEtale.SemilinearProperOpen.Derived C₀ τ C)
      (D := ProEtale.SemilinearProperOpen.Derived C₀ τ D)
      (E := ProEtale.SemilinearProperOpen.Derived C₀ τ E₀)
      (F := ProEtale.SemilinearProperOpen.Derived C₀ τ F) where
  K := ProEtale.SemilinearProperOpen.J C₀ τ k
  L := ProEtale.SemilinearProperOpen.J C₀ τ ll
  I := ProEtale.SemilinearProperOpen.J C₀ τ i
  J := ProEtale.SemilinearProperOpen.J C₀ τ j
  R := ProEtale.SemilinearProperOpen.R C₀ τ r
  P := ProEtale.SemilinearProperOpen.R C₀ τ p
  Q := ProEtale.SemilinearProperOpen.R C₀ τ q
  Kc := ProEtale.SemilinearProperOpen.J C₀ τ (k ≫ ll)
  Ic := ProEtale.SemilinearProperOpen.J C₀ τ (i ≫ j)
  ck := ProEtale.SemilinearProperOpen.jComp C₀ τ k ll
  ci := ProEtale.SemilinearProperOpen.jComp C₀ τ i j
  g₁ := ProEtale.SemilinearProperOpen.gamma C₀ τ k r p i h₁
  g₂ := ProEtale.SemilinearProperOpen.gamma C₀ τ ll p q j h₂
  g₀ := ProEtale.SemilinearProperOpen.gamma C₀ τ (k ≫ ll) r q (i ≫ j) h
  horizontal := (ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting C₀ τ).2.1
    k ll i j r p q h₁ h₂ h

attribute [local irreducible] CanonicalBridge.push CanonicalBridge.shriek Compositors.openComp
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.rightDerivedFunctor constantSheaf
  HasDerivedCategory.standard DerivedCategory.Q Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryFactors
  ProEtale.SemilinearProperOpen.R ProEtale.SemilinearProperOpen.J
  ProEtale.SemilinearProperOpen.jComp ProEtale.SemilinearProperOpen.gamma

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CommRingCat.hasForgetToRingCat

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def chosenHorizontalData
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
    (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) :
    HorizontalData (A := System l E A) (B := System l E B₀)
      (C := System l E C) (D := System l E D) (E := System l E E₀) (F := System l E F) :=
  nativeHorizontalData (scalarRings l E) (scalarTransitions l E) k ll i j r p q h₁ h₂ h

private def chosenHorizontalBridge (o : Operations l E) (b : CanonicalBridge l E o)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
    (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) :
    HorizontalBridge (chosenHorizontalData l E k ll i j r p q h₁ h₂ h)
      (Operations.shriek l E o k) (Operations.shriek l E o ll) (Operations.shriek l E o i)
      (Operations.shriek l E o j) (Operations.push l E o r) (Operations.push l E o p)
      (Operations.push l E o q) (Operations.shriek l E o (k ≫ ll)) (Operations.shriek l E o (i ≫
        j)) where
  eK := b.shriek l E k
  eL := b.shriek l E ll
  eI := b.shriek l E i
  eJ := b.shriek l E j
  eR := b.push l E r
  eP := b.push l E p
  eQ := b.push l E q
  eKc := b.shriek l E (k ≫ ll)
  eIc := b.shriek l E (i ≫ j)

section
attribute [local irreducible] chosenHorizontalData chosenHorizontalBridge

private theorem chosen_compositors (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
    (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) :
    let d := chosenHorizontalData l E k ll i j r p q h₁ h₂ h
    let v := chosenHorizontalBridge l E o b k ll i j r p q h₁ h₂ h
    (∀ M, (c.openComp l E k ll).hom.app M ≫ v.eKc.hom.app M =
      v.eL.hom.app ((Operations.shriek l E o k).obj M) ≫ d.L.map (v.eK.hom.app M) ≫
        d.ck.hom.app M) ∧
    (∀ M, (c.openComp l E i j).hom.app M ≫ v.eIc.hom.app M =
      v.eJ.hom.app ((Operations.shriek l E o i).obj M) ≫ d.J.map (v.eI.hom.app M) ≫
        d.ci.hom.app M) := by
  dsimp only
  delta chosenHorizontalBridge chosenHorizontalData nativeHorizontalData
  exact ⟨integralSystemOpenCompositorBridge l E o c b k ll,
    integralSystemOpenCompositorBridge l E o c b i j⟩

private theorem chosen_canonical (o : Operations l E)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (hgamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫ (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M)
    {A C E₀ B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
    (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) :
    let d := chosenHorizontalData l E k ll i j r p q h₁ h₂ h
    let v := chosenHorizontalBridge l E o b k ll i j r p q h₁ h₂ h
    (∀ M, (gamma k r p i h₁).app M ≫ v.eP.hom.app ((Operations.shriek l E o k).obj M) ≫
      d.P.map (v.eK.hom.app M) =
      v.eI.hom.app ((Operations.push l E o r).obj M) ≫ d.I.map (v.eR.hom.app M) ≫ d.g₁.app M) ∧
    (∀ M, (gamma ll p q j h₂).app M ≫ v.eQ.hom.app ((Operations.shriek l E o ll).obj M) ≫
      d.Q.map (v.eL.hom.app M) =
      v.eJ.hom.app ((Operations.push l E o p).obj M) ≫ d.J.map (v.eP.hom.app M) ≫ d.g₂.app M) ∧
    (∀ M, (gamma (k ≫ ll) r q (i ≫ j) h).app M ≫ v.eQ.hom.app ((Operations.shriek l E o (k ≫
      ll)).obj M) ≫ d.Q.map (v.eKc.hom.app M) =
      v.eIc.hom.app ((Operations.push l E o r).obj M) ≫ d.Ic.map (v.eR.hom.app M) ≫
        d.g₀.app M) := by
  dsimp only
  delta chosenHorizontalBridge chosenHorizontalData nativeHorizontalData
  exact ⟨hgamma k r p i h₁, hgamma ll p q j h₂,
    hgamma (k ≫ ll) r q (i ≫ j) h⟩

/- STATEMENT-DISPUTED (repaired): the old theorem asserted quadratic pasting for
arbitrary gamma. Negating the canonical family disproves it on nonzero identity
diagrams when 2 is nonzero. The added equation fixes the canonical normalization. -/

/-- Horizontal proper/open transport pasting for the canonically normalized gamma.
The bridge and its componentwise equation are supplied by the existing transport core.
Source: Stacks 0F7C, 0F7D and 0F7F; Zheng Lemma 4.10.
(blueprint: lem-sf-integral-system-proper-open-transport-pasting-horizontal).
Proof: transport the intrinsic equation through the canonical bridge; naturality and
inverse cancellation identify the resulting composite. -/
theorem integralSystemProperOpenTransportPastingHorizontal
    (o : Operations l E) (c : Compositors l E o)
    (_a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (hgamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫ (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
      (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) (M : System l E A),
      (c.openComp l E i j).hom.app ((Operations.push l E o r).obj M) ≫
          (gamma (k ≫ ll) r q (i ≫ j) h).app M ≫
          (Operations.push l E o q).map ((c.openComp l E k ll).inv.app M) =
        (Operations.shriek l E o j).map ((gamma k r p i h₁).app M) ≫
          (gamma ll p q j h₂).app ((Operations.shriek l E o k).obj M)  := by
  intro A C E₀ B₀ D F k ll i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
  let d := chosenHorizontalData l E k ll i j r p q h₁ h₂ h
  let v := chosenHorizontalBridge l E o b k ll i j r p q h₁ h₂ h
  have hc := chosen_compositors l E o c b k ll i j r p q h₁ h₂ h
  have hg := chosen_canonical l E o gamma b hgamma k ll i j r p q h₁ h₂ h
  have hw : Nonempty (HorizontalWitness
      (c.openComp l E k ll) (c.openComp l E i j)
      (gamma k r p i h₁) (gamma ll p q j h₂) (gamma (k ≫ ll) r q (i ≫ j) h)) :=
    ⟨{ d := d, v := v, hk := hc.1, hi := hc.2,
       h₁ := hg.1, h₂ := hg.2.1, h₀ := hg.2.2 }⟩
  obtain ⟨w⟩ := hw
  exact transport_horizontal_data w.d w.v
    (c.openComp l E k ll) (c.openComp l E i j)
    (gamma k r p i h₁) (gamma ll p q j h₂) (gamma (k ≫ ll) r q (i ≫ j) h)
    w.hk w.hi w.h₁ w.h₂ w.h₀ M

end
end WeilConjectures.IntegralSystemRealization
