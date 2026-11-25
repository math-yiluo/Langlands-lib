/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData

/-! Explicit integral-system types for the canonical semilinear bridge data.
(blueprint: def-sf-integral-system-native-bridge-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] CanonicalBridge.pull Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard DerivedCategory.Q
  Functor.leftAdjoint Adjunction.leftAdjointUniq
  CanonicalBridge.push CanonicalBridge.shriek Compositors.pushComp
  ProEtale.SemilinearProperOpen.R
  ProEtale.SemilinearProperOpen.J ProEtale.SemilinearProperOpen.adj
  ProEtale.SemilinearProperOpen.jAdj

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift

/-- The prescribed semilinear datum, with its integral-system category explicit.
Source: blueprint fix-prop-coherence, canonical proper/open comparison.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeR {X Y : Scheme.{u}} (f : X ⟶ Y) :
    System l E X ⥤ System l E Y :=
  ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) f

/-- The prescribed semilinear datum, with its integral-system category explicit.
Source: blueprint fix-prop-coherence, canonical proper/open comparison.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeJ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    System l E X ⥤ System l E Y :=
  ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) f

/-- The prescribed semilinear datum, with its integral-system category explicit.
Source: blueprint fix-prop-coherence, canonical proper/open comparison.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeBridge (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Operations.push l E o f ≅ nativeR l E f :=
  b.push l E f

/-- The prescribed semilinear datum, with its integral-system category explicit.
Source: blueprint fix-prop-coherence, canonical proper/open comparison.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeShriek (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Operations.shriek l E o f ≅ nativeJ l E f :=
  b.shriek l E f

/-- The prescribed semilinear datum, with its integral-system category explicit.
Source: blueprint fix-prop-coherence, canonical proper/open comparison.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    nativeJ l E f ⟶ nativeR l E f :=
  ProEtale.SemilinearProperOpen.openToS (scalarRings l E) (scalarTransitions l E) f

/-- The prescribed semilinear datum, with its integral-system category explicit.
Source: blueprint fix-prop-coherence, canonical proper/open comparison.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeComp {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W) :
    nativeR l E s ⋙ nativeR l E q ≅ nativeR l E (s ≫ q) :=
  ProEtale.SemilinearProperOpen.sComp (scalarRings l E) (scalarTransitions l E) s q

/-- Equality transport for the prescribed direct functor, typed on integral systems.
Source: blueprint fix-prop-coherence, the final direct-compositor equality transport.
(blueprint: def-sf-integral-system-native-bridge-data). -/
def nativeREq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : System l E X) :
    (nativeR l E f).obj M ⟶ (nativeR l E g).obj M :=
  (eqToIso (congrArg (nativeR l E) h)).hom.app M

end WeilConjectures.IntegralSystemRealization
