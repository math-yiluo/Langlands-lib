/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusWitnessedCompactification

/-! # Explicit finite ring-sheaf coordinates in the fixed-scalar presentation

The open and direct-image coordinates below are composites of the existing canonical
presentation comparisons. They construct the refinement comparison without selecting
an isomorphism from an existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Direct image of module sheaves through the specified scalar map.
Source: Stacks 03D1; the sectionwise module direct image
(blueprint: def-sf-finite-ring-fixed-coordinates). -/
def finiteScalarDirectImage {X Y : Scheme.{w}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{w + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{w + 1})
    (a : R ⟶ (proEtaleSheafDirectImage f CommRingCat.{w + 1}).obj S) :=
  SheafOfModules.pushforward.{w + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj R)
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj S)
    ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})⟩

/-- The finite ring-sheaf scalar map is the constant-section scalar map.
Source: Stacks 03D1 and 03D6; finiteDirectImage_eq's adjunction calculation
(blueprint: lem-sf-finite-ring-scalar-map-equality).

Proof: finite.pull is the inverse adjoint transpose of the constant-section map.
Apply the adjunction Hom equivalence again. Its inverse equation gives the
specified constant-section map, including identity maps and zero coefficient rings. -/
theorem finiteRingDirectImageMap_eq {U V : Scheme.{w}} (g : U ⟶ V) :
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    proEtaleRingDirectImageMap g (R.ring V) (R.ring U) (R.pull g) =
      proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)) := by
  exact ((proEtaleSheafAdjunction g CommRingCat.{w + 1}).homEquiv _ _).apply_symm_apply _

/-- The finite open comparison followed by the fixed realization comparison.
Source: Stacks 00YV and 03DI
(blueprint: def-sf-finite-ring-fixed-coordinates). -/
def finiteFixedOpenIso {U V : Scheme.{w}} (j : U ⟶ V) [IsOpenImmersion j] :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (sfIntrinsicDerivedEquivalence U A).functor ⋙
        (PurCompactSupport.openExtension R j).mapDerivedCategory ≅
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{w + 1} (ULift.{w + 1} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence V A).functor :=
  letI ringAdd : (PurCompactSupport.openExtension
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) j).Additive :=
    proEtaleRingOpenExtension_additive j
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring V)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring U)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull j)
  letI openAdd := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).1
  letI openLim := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  letI openColim := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let o := @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
    ringAdd openAdd _ _ openLim openColim (PurCompactSupport.finiteOpenIso l E n j)
  Functor.isoWhiskerLeft
      (sfIntrinsicDerivedEquivalence U (Padic.coefficientExtensionRing l E (n + 1))).functor
      o ≪≫
    FrobeniusExchange.fixedDerivedOpenModel (Padic.coefficientExtensionRing l E (n + 1)) j

/-- The separately derived finite direct-image comparison followed by realization.
Source: Stacks 00YV, 03D6 and 07A5
(blueprint: def-sf-finite-ring-fixed-coordinates). -/
def finiteFixedPushIso {U V : Scheme.{w}} (g : U ⟶ V) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (sfIntrinsicDerivedEquivalence U A).functor ⋙ PurCompactSupport.push R g ≅
      (AlgebraicGeometry.ProEtale.lowerStar
        (ModuleCat.{w + 1} (ULift.{w + 1} A)) g).rightDerivedFunctor ⋙
        (sfIntrinsicDerivedEquivalence V A).functor :=
  letI ringAdd : (proEtaleRingModuleDirectImage g
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring V)
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring U)
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g)).Additive :=
    proEtaleRingModuleDirectImage_additive g
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring V)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring U)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g)
  letI pushAdd := (proEtaleConstantModuleDirectImage_additive_leftExact g
    (Padic.coefficientExtensionRing l E (n + 1))).1
  let p := @Functor.rightDerivedFunctorNatIso _ _ _ _ _ _ _ _ _ _ _
    ringAdd pushAdd (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n g))
  Functor.isoWhiskerLeft
      (sfIntrinsicDerivedEquivalence U (Padic.coefficientExtensionRing l E (n + 1))).functor
      p ≪≫
    sfIntrinsicDerivedDirectImageComparison g (Padic.coefficientExtensionRing l E (n + 1))

/-- Open coordinates of the retained underlying object, including its equivalence counit.
Source: Stacks 00YV and 03DI
(blueprint: def-sf-finite-ring-fixed-coordinates). -/
def finiteFixedOpenAt {X Y : Scheme.{w}} (j : X ⟶ Y) [IsOpenImmersion j]
    (O : FrobeniusExchange.CompactOrigin (Padic.coefficientExtensionRing l E (n + 1)) X) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (PurCompactSupport.openExtension R j).mapDerivedCategory.obj O.K ≅
      (sfIntrinsicDerivedEquivalence Y A).functor.obj
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{w + 1} (ULift.{w + 1} A)) j).mapDerivedCategory.obj
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj O.K)) :=
  (PurCompactSupport.openExtension
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) j).mapDerivedCategory.mapIso
      ((sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).counitIso.app O.K).symm ≪≫
    (finiteFixedOpenIso l E n j).app
      ((sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj O.K)

/-- The concrete proper/open isomorphism in finite ring-sheaf coordinates.
It is the image of the specified fixed-scalar proper/open map, with the two open
coordinates and the separately derived direct-image coordinate inserted.
Source: compactification-coherence proof, first two paragraphs; Stacks 03DI and 0F7B
(blueprint: def-sf-finite-ring-fixed-coordinates). -/
def finiteFixedRefinementOpenIso {X Y : Scheme.{w}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin (Padic.coefficientExtensionRing l E (n + 1)) X) :
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (PurCompactSupport.openExtension R d.i).mapDerivedCategory.obj O.K ≅
      (PurCompactSupport.push R r.hom).obj
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj O.K) :=
  finiteFixedOpenAt l E n d.i O ≪≫
    (sfIntrinsicDerivedEquivalence d.Z
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
      (FrobeniusExchange.fixedRefinementOpen
        (Padic.coefficientExtensionRing l E (n + 1)) r O) ≪≫
    ((finiteFixedPushIso l E n r.hom).app
      ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        c.i).mapDerivedCategory.obj
          ((sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj O.K))).symm ≪≫
    (PurCompactSupport.push
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r.hom).mapIso
      (finiteFixedOpenAt l E n c.i O).symm

end WeilConjectures.ConstructibleExceptionalCoefficients
