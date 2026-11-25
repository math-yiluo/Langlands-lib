/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRingModel
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRestriction.NativeScalarOrdinaryRestrictionCube
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction.NativeScalarInverseDerivedRestrictionCube

/-! # Restriction and direct image under a coefficient-ring presentation

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites,
Tag 0D6E; blueprint scalar direct-image proof, Formal properties.
(blueprint: lem-sf-native-scalar-restriction-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.EquivalenceCubeTransport

namespace NativeScalarProof
universe u wA wB

private theorem liftFunctor
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] :
    (liftEquivalence e).functor = e.functor.mapDerivedCategory := rfl
end NativeScalarProof

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale
open TwoSquare

attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight
  nativeScalarIntegralExact

/-- The exact derived restriction along the two condensed coefficient inclusions, in order.
Source: the two extension/restriction adjunctions of the scalar direct-image proof.
(blueprint: lem-sf-native-scalar-restriction-cube). -/
def nativeScalarCompositeRestriction (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T)) :=
  (Mod.comap (coefficientMap
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T)).mapDerivedCategory ⋙
    (Mod.comap (padicIntegersToPadicSubfield T l E)).mapDerivedCategory

/-- The pasted inverse restriction/direct-image square. Its construction uses only
restriction and right derived direct image, not either scalar-extension mate.
Source: blueprint scalar direct-image proof, Formal properties.
(blueprint: lem-sf-native-scalar-restriction-cube). -/
def nativeScalarCompositeRestrictionSquare (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {U V : Scheme.{u}} (g : U ⟶ V) :
    TwoSquare (nativeScalarCompositeRestriction l E U)
      (CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) g)
      (CondensedRing.moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.1) g)
      (nativeScalarCompositeRestriction l E V) :=
  TwoSquare.mk _ _ _ _
      (CondensedRing.derivedComapLowerStarIso
        (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g).inv ≫ₕ
    TwoSquare.mk _ _ _ _
      (CondensedRing.derivedComapLowerStarIso
        (padicIntegersRingObjToContinuousMapRingObj l E) g).inv

/-- The inverse of the specified native restriction/direct-image comparison.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-native-scalar-restriction-cube). -/
def nativeRingRestrictionSquare {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {U V : Scheme.{u}} (g : U ⟶ V) :
    TwoSquare (proEtaleRingRestrictScalars (a.map U)).mapDerivedCategory
      (proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g))
      (proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g))
      (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory :=
  TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv

-- The concrete coefficient functors require elaborating the site and ring transports.
/-- Natural ring diagrams transport the restriction/direct-image cube.
The source and target coefficient systems are arbitrary. Only their ordinary ring
isomorphisms, coefficient square, and precomposition naturality are supplied.
No scalar-extension functor or scalar mate occurs in the conclusion.

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites, Tag 0D6E;
steps 3--4 of lem-sf-native-proper-scalar-mate-presentation.
(blueprint: lem-sf-native-scalar-restriction-cube).

Proof in words:
1. Restriction of scalars along the two inclusions is restriction along their composite:
use comapComp. Apply the internal/section module equivalence to this composite. Its
restriction comparison is identity on the underlying abelian sections, and the scalar
field of P supplies linearity after the two ring-isomorphism transports. This gives the
ordinary restriction comparison at every scheme, with no derived extension involved.
2. The integral_natural and closure_natural fields identify the sectionwise coefficient
adjuncts with the condensed ones. Direct image is evaluation at the same base-change
object. The identity on those sections therefore gives ordinary direct-image
comparisons for P.integralEquivalence and P.closureEquivalence. These presentation
equivalences are additive and exact. The ordinary cube commutes since both composites are the same
identity on underlying sections; faithfulness of the module forgetful functors proves
this as an equality of linear maps, including the coefficient transitions.
3. Localize the exact restriction comparison to obtain k. Derive the two ordinary
direct-image comparisons using the canonical right-derived composite isomorphisms.
Equivalences preserve K-injective complexes, so these comparisons x and y are
isomorphisms on all unbounded objects.
4. Normalize each derived comparison by its canonical cochain resolution unit.
The derived sectionwise restriction/direct-image comparison is the specified
proEtaleRingRestrictionDerivedDirectImage by its uniqueness theorem; the internal comparisons are
the two specified
derivedComapLowerStarIso. Their pasted normalization is the normalization of their
ordinary composite. Evaluate on K-injective representatives and cancel their invertible
resolution units. The ordinary cube from step 2 gives the displayed derived cube there.
Naturality and the existence of a K-injective representative of every derived object
give the cube everywhere. This does not assert that either scalar-extension mate is
invertible. The same argument works for identity morphisms and the empty site object. -/
theorem nativeScalarRestrictionCube
    (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    (P : NativeScalarRingModel l E a) :
    ∃ k : ∀ T : Scheme.{u},
        (proEtaleRingRestrictScalars (a.map T)).mapDerivedCategory ⋙
            (P.integralEquivalence T).functor.mapDerivedCategory ≅
          (P.closureEquivalence T).functor.mapDerivedCategory ⋙
            nativeScalarCompositeRestriction l E T,
      ∀ {U V : Scheme.{u}} (g : U ⟶ V),
        ∃ (x : proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g) ⋙
              (P.integralEquivalence V).functor.mapDerivedCategory ≅
            (P.integralEquivalence U).functor.mapDerivedCategory ⋙
              CondensedRing.moduleObjectDerivedPushforward
                (Profinite.padicIntegersRingObj l E.1) g)
          (y : proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g) ⋙
              (P.closureEquivalence V).functor.mapDerivedCategory ≅
            (P.closureEquivalence U).functor.mapDerivedCategory ⋙
              CondensedRing.moduleObjectDerivedPushforward
                (Profinite.padicAlgClRingObj l) g),
          ((nativeRingRestrictionSquare a g ≫ᵥ
              TwoSquare.mk _ _ _ _ (k V).hom).whiskerLeft y.hom) =
            ((TwoSquare.mk _ _ _ _ (k U).hom ≫ᵥ
                nativeScalarCompositeRestrictionSquare l E g).whiskerRight x.hom) := by
  let ordinary := NativeScalarRestriction.nativeScalarOrdinaryRestrictionCube.{u} l E a P
  let k := ordinary.choose
  have hk := @Exists.choose_spec _ _ ordinary
  refine ⟨NativeScalarDerivedRestriction.forwardRestriction l E a P k, ?_⟩
  intro U V g
  let x := (hk g).choose
  let y := (hk g).choose_spec.choose
  have h := (hk g).choose_spec.choose_spec
  refine ⟨NativeScalarDerivedRestriction.forwardIntegralPush l E a P g x,
    NativeScalarDerivedRestriction.forwardClosurePush l E a P g y, ?_⟩
  refine NatTrans.ext (funext fun N ↦ ?_)
  have hf := forwardCube
    (liftEquivalence (P.closureEquivalence U)) (liftEquivalence (P.integralEquivalence U))
    (liftEquivalence (P.closureEquivalence V)) (liftEquivalence (P.integralEquivalence V))
    (proEtaleRingRestrictScalars (a.map U)).mapDerivedCategory
    (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)).rightDerivedFunctor
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).rightDerivedFunctor
    (NativeScalarDerivedRestriction.compositeRestriction l E U)
    (NativeScalarDerivedRestriction.compositeRestriction l E V)
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor
    (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g).rightDerivedFunctor
    (NativeScalarDerivedRestriction.inverseRestriction l E a P k U)
    (NativeScalarDerivedRestriction.inverseRestriction l E a P k V)
    (NativeScalarDerivedRestriction.inverseIntegralPush l E a P g x)
    (NativeScalarDerivedRestriction.inverseClosurePush l E a P g y)
    (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))
    (NativeScalarDerivedRestriction.positiveSquare l E g)
    (NativeScalarDerivedRestriction.inverseCube l E a P k g x y h) N
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.hComp, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_id, Category.id_comp, Category.comp_id,
    nativeRingRestrictionSquare, nativeScalarCompositeRestrictionSquare,
    NativeScalarDerivedRestriction.positiveSquare, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NativeScalarDerivedRestriction.forwardRestriction,
    NativeScalarDerivedRestriction.forwardIntegralPush,
    NativeScalarDerivedRestriction.forwardClosurePush, NativeScalarProof.liftFunctor,
    Category.assoc,
    proEtaleRingDerivedDirectImage, CondensedRing.moduleObjectDerivedPushforward,
    nativeScalarCompositeRestriction, NativeScalarDerivedRestriction.compositeRestriction,
    Functor.whiskerLeft, Functor.whiskerRight, Functor.associator] using hf

end WeilConjectures.LocallyFiniteAdicCompactSupport
