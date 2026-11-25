/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor

/-! # Fixed coefficient coordinates for finite projection calculations

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The full constructible inclusion followed by the inverse coefficient realization.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def coordinates (X : SixFunctorSpace D) :=
  (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
    (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse

/-- Direct image in fixed coefficient coordinates.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def fixedDirect {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  (AlgebraicGeometry.ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      f.hom.left).rightDerivedFunctor

/-- The canonical fixed coefficient adjunction.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def fixedAdjunction {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    fixedDerivedPull (C := C) (E := E) (n := n) f ⊣
      fixedDirect (C := C) (E := E) (n := n) f :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) f.hom.left

/-- The tensor coordinate comparison cancels precisely the coefficient unit.
Source: the proper-factor calculation (blueprint: def-sf-finite-projection-fixed-coordinates). -/
def tensorCoordinates (S : SixFunctorFiniteOperations D C E n hn)
    (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj
        (((partialTensor S X).obj K).obj L) ≅
      ((fixedTensor (C := C) (E := E) (n := n) X).obj
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).obj
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L.obj) :=
  ((realization (C := C) (E := E) (n := n) (hn := hn) X).unitIso.app _).symm

attribute [local irreducible] realization

end WeilConjectures.CompactSupportFiniteProjection
