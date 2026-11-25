/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarIntegralPresentation

/-! # Ring diagrams for native scalar transport

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-sf-native-scalar-ring-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale

/-- The section-ring map for the two actual condensed coefficient inclusions.
Source: Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-sf-native-scalar-ring-model). -/
def nativeScalarSectionMap (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    (T : Scheme.{u}) :
    InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T ⟶
      InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) T :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (CondensedRing.sectionRingMap T
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) T ≫
        coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T))

/-- A ring presentation is natural for the actual adjunct of the inverse-image ring map.
This is a pointwise equality on sections of the base-change site object.
Source: Bhatt--Scholze, Section 6.8; Stacks, Modules on Sites.
(blueprint: lem-sf-native-scalar-ring-model). -/
def NativeScalarRingNaturality (R : PurCompactSupport.Coefficients.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
      InternalModuleOperations.ring Λ T) : Prop :=
  ∀ {U V : Scheme.{u}} (g : U ⟶ V) (W : V.ProEtᵒᵖ)
      (s : (R.ring V).obj.obj W),
    (i U).hom.hom.app ((proEtaleBaseChange g).op.obj W)
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          (R.pull g).hom).hom.app W s) =
      (InternalModuleOperations.coefficientMap Λ g).hom.app W ((i V).hom.hom.app W s)

/-- An ordinary coefficient-ring diagram. Its fields mention neither complexes nor scalar mates.
The two ring isomorphisms identify scalar inclusions and precomposition maps.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-sf-native-scalar-ring-model). -/
structure NativeScalarRingModel (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S) where
  integral : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
    InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T
  closure : ∀ T : Scheme.{u}, (adicLisseForget T).obj (S.ring T) ≅
    InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) T
  scalar : ∀ T : Scheme.{u},
    (adicLisseForget T).map (a.map T) ≫ (closure T).hom =
      (integral T).hom ≫ nativeScalarSectionMap l E T
  integral_natural : NativeScalarRingNaturality R
    (Profinite.padicIntegersRingObj l E.1) integral
  closure_natural : NativeScalarRingNaturality S (Profinite.padicAlgClRingObj l) closure

namespace NativeScalarRingModel

/-- The integral module equivalence constructed from the supplied ring isomorphism.
Source: Stacks, Modules on Sites, Tag 00YV.
(blueprint: lem-sf-native-scalar-ring-model). -/
def integralEquivalence {l : ℕ} [Fact l.Prime] {E : Index l (PadicAlgCl l)}
    {R S : PurCompactSupport.Coefficients.{u}} {a : PurCompactSupport.Change R S}
    (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    pbcModules T (R.ring T) ≌
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T) :=
  (CondensedRing.ringModuleEquivalenceOfIso T (P.integral T).symm).trans
    (InternalModuleOperations.equivalence (Profinite.padicIntegersRingObj l E.1) T).symm

/-- The native-to-condensed module equivalence constructed from the supplied ring isomorphism.
Source: Stacks, Modules on Sites, Tag 00YV.
(blueprint: lem-sf-native-scalar-ring-model). -/
def closureEquivalence {l : ℕ} [Fact l.Prime] {E : Index l (PadicAlgCl l)}
    {R S : PurCompactSupport.Coefficients.{u}} {a : PurCompactSupport.Change R S}
    (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    pbcModules T (S.ring T) ≌
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) T) :=
  (CondensedRing.ringModuleEquivalenceOfIso T (P.closure T).symm).trans
    (InternalModuleOperations.equivalence (Profinite.padicAlgClRingObj l) T).symm

/-- An equivalence of these abelian categories preserves binary products and zero maps,
so it is additive. Source: Mathlib's additive_of_preserves_binary_products.
(blueprint: lem-sf-native-scalar-ring-model). -/
instance integralEquivalence_additive {l : ℕ} [Fact l.Prime]
    {E : Index l (PadicAlgCl l)} {R S : PurCompactSupport.Coefficients.{u}}
    {a : PurCompactSupport.Change R S} (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    (P.integralEquivalence T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the closure module equivalence, by preservation of products and zero maps.
Source: Mathlib's additive_of_preserves_binary_products.
(blueprint: lem-sf-native-scalar-ring-model). -/
instance closureEquivalence_additive {l : ℕ} [Fact l.Prime]
    {E : Index l (PadicAlgCl l)} {R S : PurCompactSupport.Coefficients.{u}}
    {a : PurCompactSupport.Change R S} (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    (P.closureEquivalence T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

end NativeScalarRingModel

private def sectionRingIso (T : Scheme.{u})
    {A B : Sheaf (ProEt.topology T) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (e : A ≅ B) [IsMonHom e.hom] :
    (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology T) A) ≅
      (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology T) B) where
  hom := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (CondensedRing.sectionRingMap T e.hom)
  inv := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (CondensedRing.sectionRingMap T e.inv)
  hom_inv_id := by
    ext W x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) e.hom_inv_id) W) x
  inv_hom_id := by
    ext W x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) e.inv_hom_id) W) x

private def nativeClosureIso (l : ℕ) [Fact l.Prime] [NativeRings.{u} l]
    (θ : ∀ T : Scheme.{u}, condensedRingObj (Profinite.padicAlgClRingObj l) T ≅
      abRing l T) (hθ : ∀ T, IsMonHom (θ T).hom) (T : Scheme.{u}) :
    (adicLisseForget T).obj ((nativeCoefficients l).ring T) ≅
      InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) T := by
  letI := hθ T
  exact (sectionRingIso T (θ T)).symm

private theorem nativeClosureIso_natural (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (θ : ∀ T : Scheme.{u}, condensedRingObj (Profinite.padicAlgClRingObj l) T ≅
      abRing l T) (hθ : ∀ T, IsMonHom (θ T).hom)
    (hn : ∀ (X Y : Scheme.{u}) (g : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) g ≫
        (lowerStar Ab.{u + 1} g).map (θ X).hom =
      (θ Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l g)) :
    NativeScalarRingNaturality (nativeCoefficients l) (Profinite.padicAlgClRingObj l)
      (nativeClosureIso l θ hθ) := by
  intro U V g W s
  change (abRing l V).obj.obj W at s
  have h := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : condensedRingObj (Profinite.padicAlgClRingObj l) V ⟶
      (lowerStar Ab.{u + 1} g).obj (abRing l U) ↦ f.hom) (hn U V g)) W)
      ((θ V).inv.hom.app W s)
  have he : (θ V).hom.hom.app W ((θ V).inv.hom.app W s) = s :=
    ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : abRing l V ⟶ abRing l V ↦ f.hom)
        (θ V).inv_hom_id) W) s
  have hc := (InternalModuleOperations.coefficientMap_existsUnique
    (Profinite.padicAlgClRingObj l) g).exists.choose_spec W
      ((θ V).inv.hom.app W s)
  change (θ U).inv.hom.app ((proEtaleBaseChange g).op.obj W) _ =
    (InternalModuleOperations.coefficientMap
      (Profinite.padicAlgClRingObj l) g).hom.app W ((θ V).inv.hom.app W s)
  change (InternalModuleOperations.coefficientMap
    (Profinite.padicAlgClRingObj l) g).hom.app W
      ((θ V).inv.hom.app W s) = _ at hc
  rw [hc]
  apply (ConcreteCategory.bijective_of_isIso ((θ U).hom.hom.app
    ((proEtaleBaseChange g).op.obj W))).1
  have hi := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : abRing l U ⟶ abRing l U ↦ f.hom)
      (θ U).inv_hom_id) ((proEtaleBaseChange g).op.obj W))
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      (N.pull g).hom).hom.app W s)
  change (θ U).hom.hom.app ((proEtaleBaseChange g).op.obj W)
      ((θ U).inv.hom.app ((proEtaleBaseChange g).op.obj W)
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          (N.pull g).hom).hom.app W s)) = _ at hi
  change (θ U).hom.hom.app ((proEtaleBaseChange g).op.obj W)
      ((condensedPushforwardHom (Profinite.padicAlgClRingObj l) g).hom.app W
        ((θ V).inv.hom.app W s)) =
    ((weilCoefficientsForgetAb l V).map (adicConstantSheafToLowerStar l g)).hom.app W
      ((θ V).hom.hom.app W ((θ V).inv.hom.app W s)) at h
  refine hi.trans (Eq.trans ?_ h.symm)
  refine Eq.trans ?_ (congrArg (fun z : (abRing l V).obj.obj W ↦
    ((weilCoefficientsForgetAb l V).map
      (adicConstantSheafToLowerStar l g)).hom.app W z) he.symm)
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact N.pull_normalized g W s x

private theorem nativeScalarChartValue (l : ℕ) [Fact l.Prime] [NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (θ : ∀ T : Scheme.{u}, condensedRingObj (Profinite.padicAlgClRingObj l) T ≅ abRing l T)
    (hchart : ∀ (T : Scheme.{u}) (F : PadicAlgCl.FiniteIntermediateField l)
      (W : T.ProEtᵒᵖ) (s : (condensedRingObj (Profinite.continuousMapRingObj F) T).obj.obj W)
      (x : W.unop.left),
      (((((upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl l F) ≫
        (θ T).hom).hom.app W) s).down.1 x) =
        (((chartComparison T F).hom.app W s).down x : PadicAlgCl l))
    (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
    (s : (InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T).obj.obj W)
    (x : W.unop.left) :
    letI := PadicAlgCl.normedFieldOfAlgebra l E.1
    (((θ T).hom.hom.app W ((nativeScalarSectionMap l E T).hom.app W s)).down.1 x) =
      (((chartComparison T (PadicAlgCl.integers l E.1)).hom.app W s).down x : E.1) := by
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  have h := hchart T E W
    ((coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) T).hom.app W s) x
  have hn := chartComparison_naturality T (PadicAlgCl.integers l E.1) E.1
    (PadicAlgCl.integers l E.1).toSubring.subtype continuous_subtype_val
  have hn' := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : condensedRingObj
      (Profinite.continuousMapRingObj (PadicAlgCl.integers l E.1)) T ⟶
      (sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf T E.1) ↦ f.hom) hn) W) s
  change (((θ T).hom.hom.app W
    ((coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T).hom.app W
      ((coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj l E) T).hom.app W s))).down.1 x) = _
  change (((θ T).hom.hom.app W
    ((coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T).hom.app W
      ((coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj l E) T).hom.app W s))).down.1 x) = _ at h
  rw [h]
  exact congrArg (fun t : ULift.{u + 1} C(W.unop.left, E.1) ↦ (t.down x : PadicAlgCl l)) hn'

/-- The completed/native coefficient change has a natural ordinary ring presentation.

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; the coefficient-identification
steps 1--3 of lem-sf-native-proper-scalar-mate-presentation.
(blueprint: lem-sf-native-scalar-ring-model).

Proof in words:
1. The normalized continuous integral comparison identifies the completed coefficient
ring for Coefficient E with continuous functions into its valuation ring. Shrink.algEquiv
identifies the size model with the original finite subfield. Its algebra linear equivalence
is bicontinuous over the complete base field; uniqueness of the extending absolute value
identifies the valuation subrings. Postcomposition gives the continuous integer-ring sheaf
isomorphism. The pulled condensed integral limit theorem and internal section reconstruction
then give integral. The finite quotient projections fix this isomorphism uniquely.
2. Apply the locally finite coefficient-ring realization and reconstruct its section ring.
Its inverse gives closure. Multiplication and the unit are preserved by the supplied
IsMonHom, so these are ring isomorphisms, not only abelian-sheaf isomorphisms.
3. Obtain a normalized CoefficientPresentation from coefficientPresentations_exists.
The continuous chart comparison commutes with integral inclusion, localization and
inclusion of the finite subfield into the closure. The normalization of CoefficientPresentation
therefore identifies the composite with its integralMap. The hypothesis ha identifies it
with a.map, giving scalar.
4. Take the inverse-image adjuncts. Both ring comparisons send the given coefficient
adjuncts to precomposition on continuous functions, by chart naturality and the native
pull_normalized equation. Equality on every site section proves integral_natural and
closure_natural. Empty schemes and zero section rings require no separate choice. -/
theorem exists_nativeScalarRingModel
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T) :
    Nonempty (NativeScalarRingModel l E a) := by
  obtain ⟨I, hI, hIn⟩ := exists_nativeScalarIntegralPresentation l E a ha
  obtain ⟨θ, hθ, hchart, hn⟩ := locallyFiniteCoefficientRing_realization l
  refine ⟨{ integral := I
            closure := nativeClosureIso l θ hθ
            scalar := ?_
            integral_natural := hIn
            closure_natural := nativeClosureIso_natural l θ hθ hn }⟩
  intro T
  ext W s
  change ((PurCompactSupport.completed l
    (Coefficient.{u} l (PadicAlgCl l) E)).ring T).obj.obj W at s
  apply (ConcreteCategory.bijective_of_isIso ((θ T).hom.hom.app W)).1
  change (θ T).hom.hom.app W ((θ T).inv.hom.app W ((a.map T).hom.app W s)) =
    (θ T).hom.hom.app W ((nativeScalarSectionMap l E T).hom.app W
      ((I T).hom.hom.app W s))
  have he := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : abRing l T ⟶ abRing l T ↦ f.hom)
      (θ T).inv_hom_id) W) ((a.map T).hom.app W s)
  change (θ T).hom.hom.app W
      ((θ T).inv.hom.app W ((a.map T).hom.app W s)) = (a.map T).hom.app W s at he
  refine he.trans ?_
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact (hI T W s x).trans
    (nativeScalarChartValue l E θ hchart T W ((I T).hom.hom.app W s) x).symm

end WeilConjectures.LocallyFiniteAdicCompactSupport
