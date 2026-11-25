/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Input normalization for the realized finite projection

Source: the defining coordinate equation of the compactification projection and
naturality of the canonical finite scalar-reduction comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  CategoryTheory.Functor.mapDerivedCategory sfIntrinsicModuleEquivalence
  ProEtale.projectionMapOfCompactification
attribute [local instance 100000] SheafOfModules.instAbelian
attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

private def reducedInputsMapArrowIso {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {f g : Arrow A} (e : f ≅ g) :
    Arrow.mk (F.map f.hom) ≅ Arrow.mk (F.map g.hom) :=
  F.mapArrow.mapIso e

private def reducedInputsArrowIso
    {A B T : Type*} [Category* A] [Category* B] [Category* T]
    {P Q : A ⥤ B ⥤ T} (α : P ⟶ Q) {K K' : A} {L L' : B}
    (eK : K ≅ K') (eL : L ≅ L') :
    Arrow.mk ((α.app K).app L) ≅ Arrow.mk ((α.app K').app L') :=
  Arrow.isoMk (((P.mapIso eK).app L) ≪≫ (P.obj K').mapIso eL)
    (((Q.mapIso eK).app L) ≪≫ (Q.obj K').mapIso eL) (by
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Arrow.mk_hom]
      rw [Category.assoc, (α.app K').naturality, ← Category.assoc,
        NatTrans.naturality_app, Category.assoc])

-- Convert coordinate endpoints while the coefficient category is still abstract.
private theorem coordinateInputsArrowIso
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {T : Type*} [Category* T] (F : DerivedCategory (Sheaf (ProEt.topology Y) A) ⥤ T)
    {K K' : DerivedCategory (Sheaf (ProEt.topology X) A)}
    {L L' : DerivedCategory (Sheaf (ProEt.topology Y) A)}
    (eK : K ≅ K') (eL : L ≅ L') :
    Nonempty (Arrow.mk (F.map (projectionTensorCoordinateComponent A c K L)) ≅
      Arrow.mk (F.map (((ProEtale.projectionMapOfCompactification A c).app K').app L'))) :=
  ⟨reducedInputsMapArrowIso F
    (reducedInputsArrowIso (ProEtale.projectionMapOfCompactification A c) eK eL)⟩

-- Fix the functor types before applying the generic coordinate transport.
private def normalizedForward (R : Type u) [CommRing R] [Finite R] (Y : Scheme.{u}) :
    DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} R))) ⥤ proEtaleDerivedCategory Y R :=
  (sfIntrinsicDerivedEquivalence Y R).functor

private def normalizedInverse (R : Type u) [CommRing R] [Finite R] (Y : Scheme.{u}) :
    proEtaleDerivedCategory Y R ⥤ DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
  (sfIntrinsicDerivedEquivalence Y R).inverse

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory in
/-- Normalize the two intrinsic scalar inputs of the realized finite projection.
Source: `finiteReductionIso` and the defining equation of the tensor-coordinate
component of the compactification projection in `def-exchange-projection`.
(blueprint: lem-sf-ordinary-projection-reduced-input-normalization-m4).

Proof: set A to the positive finite coefficient quotient. Evaluate finiteReductionIso
at K and at L and apply the inverse intrinsic realization functors to obtain
isomorphisms between the two versions of each native finite input. The fixed-scalar
compactification projection is a natural transformation of bifunctors, hence these
two isomorphisms induce a commutative square of its evaluated arrows. On the source
endpoint use the source bifunctor applied to the first isomorphism and then to the
second; on the target endpoint do the same with the target bifunctor. These are
isomorphisms, and the square commutes by naturality in both variables. Its source
arrow is the coordinate component by that component's defining equation. Apply the
forward intrinsic realization to this arrow isomorphism. The resulting arrows are
exactly the displayed arrows. Only naturality is involved: there is no completed
projection, proper scalar mate, open scalar comparison, or projection invertibility
assertion in this step. The argument includes zero objects, empty schemes, the
residue quotient and identity compactifications. -/
theorem integralOrdinaryProjection_reducedInputsNormalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
    Nonempty (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
      (projectionTensorCoordinateComponent (ModuleCat.{u + 1} (ULift.{u + 1} A)) c
        ((sfIntrinsicDerivedEquivalence X A).inverse.obj
          ((pbcDerivedExtend (a.map X)).obj K))
        ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
          ((pbcDerivedExtend (a.map Y)).obj L)))) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let eK := (normalizedInverse A X).mapIso
    ((PurCompactSupport.finiteReductionIso l E X n).app K)
  let eL := (normalizedInverse A Y).mapIso
    ((PurCompactSupport.finiteReductionIso l E Y n).app L)
  exact coordinateInputsArrowIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) c
    (normalizedForward A Y) eK eL

end WeilConjectures
