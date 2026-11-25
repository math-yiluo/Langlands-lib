/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # Finite-Tor coordinates for reduction of integral operations

Source: the residue-Tor and normalized reduction steps of the integral projection formula.
(blueprint: def-sf-integral-projection-reduction-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.IntegralProjectionReduction

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)

/-- The finite stage already recorded in the integral normalization.
Source: def-fix-six-functor-datum
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
abbrev stage := d.integralNormalization.finiteLevels m

/-- The specified reduction to the full bounded constructible finite category.
Source: def-fix-six-functor-datum
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
abbrev reduction (_d : SixFunctorOperationDatum D C E n hn) (m : ℕ)
    (X : SixFunctorSpace D) := sixFunctorIntegralReduction D C E m X

/-- Each integral input reduces to a finite-Tor object, by integral residue Tor.
Source: lemma-bounds-finite-reductions--2
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
theorem reduction_finiteTor (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left
      ((reduction d m X).obj K).obj := by
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
    (by simpa using ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
      (X.obj.hom.residueFieldAlgebraMap x)) :
      IsUnit (C.l : X.obj.left.residueField x)).invertible
  have h : finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
    rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact K.property
  obtain ⟨a, b, _, ht⟩ := h.2
  exact ⟨((reduction d m X).obj K).property, a, b, ht m⟩

/-- Reduction with its proved finite-Tor membership. No object or arrow is changed.
Source: the integral residue-Tor criterion
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def torReduction (X : SixFunctorSpace D) :
    sfIntegralConstructibleCategory C.l E X.obj.left ⥤
      finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left :=
  (finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).lift
    (reduction d m X ⋙
      (intrinsicFiniteTorsionConstructible C.l E (m + 1)
        (Nat.le_add_left 1 m) X.obj.left).ι)
    (reduction_finiteTor d m X)

/-- Pullback reduction, lifted through the full finite-Tor inclusion.
Source: the direct-adjunction comparison in integral normalization
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def pullIso {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (torReduction d m X).obj ((d.higher.integral.pull f).obj L) ≅
      (CompactSupportFiniteProjection.torPull (stage d m) f).obj
        ((torReduction d m Y).obj L) :=
  ObjectProperty.isoMk _
    ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
      (Nat.le_add_left 1 m) X.obj.left).ι.mapIso
        (((d.integralNormalization.reduction m).directAdjunction f).left.app L))

/-- A tensor comparison at every pair of integral inputs. Its finite target uses the
proved finite-Tor reduction of the second input.
Source: coefficient tensor associativity
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
abbrev TensorCoordinates :=
  ∀ (X : SixFunctorSpace D) (K L : sfIntegralConstructibleCategory C.l E X.obj.left),
    (reduction d m X).obj (((d.higher.integralTensor X).obj K).obj L) ≅
      ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
        ((reduction d m X).obj K)).obj ((torReduction d m X).obj L)

/-- Tensor followed by the recorded pullback comparison.
Source: coefficient tensor and inverse-image comparison
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def tensorPullIso (t : TensorCoordinates d m) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  t X K ((d.higher.integral.pull f).obj L) ≪≫
    ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
      ((reduction d m X).obj K)).mapIso (pullIso d m f L)

/-- Comparison of the source of one projection, using the specified support comparison.
Source: normalized coefficient comparison
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def sourceIso (t : TensorCoordinates d m) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  t Y ((d.higher.integral.support f c).obj K) L ≪≫
    ((CompactSupportFiniteProjection.partialTensor (stage d m) Y).mapIso
      (((d.integralNormalization.reduction m).supportAdjunction f c).left.app K)).app
        ((torReduction d m Y).obj L)

/-- Comparison of the target of one projection, using those same tensor coordinates.
Source: normalized coefficient comparison
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def targetIso (t : TensorCoordinates d m) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  ((d.integralNormalization.reduction m).supportAdjunction f c).left.app
      (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L)) ≪≫
    ((stage d m).finite.support f c).mapIso (tensorPullIso d m t f K L)

/-- The corresponding proper-projection source comparison, with the prescribed direct mate.
Source: normalized proper adjunction
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def properSourceIso (t : TensorCoordinates d m) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  t Y ((d.higher.integral.direct f).obj K) L ≪≫
    ((CompactSupportFiniteProjection.partialTensor (stage d m) Y).mapIso
      (((d.integralNormalization.reduction m).directAdjunction f).right.app K)).app
        ((torReduction d m Y).obj L)

/-- The proper-projection target comparison, retaining tensor and pullback coordinates.
Source: normalized proper adjunction
(blueprint: def-sf-integral-projection-reduction-coordinates). -/
def properTargetIso (t : TensorCoordinates d m) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  ((d.integralNormalization.reduction m).directAdjunction f).right.app
      (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L)) ≪≫
    ((stage d m).finite.direct f).mapIso (tensorPullIso d m t f K L)

end WeilConjectures.IntegralProjectionReduction
