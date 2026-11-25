/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node lemma-change-coefficients-internal-hom--1 (blueprint:
def-sf-finite-coefficient-site-scalar-arrow). Indices n and m below denote exponents n + 1 and m +
1; thus every positive exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private def finiteHomEncodingRestrictionGeneral
    (T : Scheme.{u}) (A B : Type u) [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (f : (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T A) ⟶
      (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T B))
    (hη : (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
        ProEtale.finiteCoefficientIntrinsicScalarMap T B =
      ProEtale.finiteCoefficientIntrinsicScalarMap T A ≫ f.hom) :
    SheafOfModules.restrictScalars f ⋙ Scheme.proEtaleModuleRestriction T A ≅
      Scheme.proEtaleModuleRestriction T B ⋙
        Sheaf.restrictScalars (ProEt.topology T) φ := by
  have hs (M : Scheme.proEtaleRingModules T (proEtaleConstantRing T B)) (V : T.ProEtᵒᵖ)
      (r : ULift.{u + 1, u} A) (x : M.val.obj V) :
      r • (show ((Scheme.proEtaleModuleRestriction T A).obj
        ((SheafOfModules.restrictScalars f).obj M)).obj.obj V from x) =
      φ r • (show ((Scheme.proEtaleModuleRestriction T B).obj M).obj.obj V from x) := by
    change f.hom.app V
      ((ProEtale.finiteCoefficientIntrinsicScalarMap T A).app V r) • x =
      (ProEtale.finiteCoefficientIntrinsicScalarMap T B).app V (φ r) • x
    exact congrArg (fun a ↦ a • x) (congrArg (fun a ↦ a.app V r) hη).symm
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ by
      let P := ((SheafOfModules.restrictScalars f ⋙
        Scheme.proEtaleModuleRestriction T A).obj M).obj.obj V
      let Q := ((Scheme.proEtaleModuleRestriction T B ⋙
        Sheaf.restrictScalars (ProEt.topology T) φ).obj M).obj.obj V
      exact
        { hom := ModuleCat.ofHom (X := P) (Y := Q)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := fun r x ↦ hs M V r x }
          inv := ModuleCat.ofHom (X := Q) (Y := P)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := fun r x ↦ (hs M V r x).symm }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl))) ?_
  intros
  apply Sheaf.hom_ext
  ext V x
  rfl

private theorem finiteHomEncodingRestrictionGeneral_sections
    (T : Scheme.{u}) (A B : Type u) [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (f : (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A) ⟶
      (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B))
    (hη : (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
        ProEtale.finiteCoefficientIntrinsicScalarMap T B =
      ProEtale.finiteCoefficientIntrinsicScalarMap T A ≫ f.hom)
    (M : Scheme.proEtaleRingModules T (proEtaleConstantRing T B))
    (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (((finiteHomEncodingRestrictionGeneral T A B φ f hη).hom.app M).hom.app V) x = x := rfl

private def finiteHomRealizationIsoGeneral (T : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B] :
    𝟭 _ ≅ ProEtale.finiteCoefficientIntrinsicRealization T B ⋙
      Scheme.proEtaleModuleRestriction T B :=
  NatIso.ofComponents (fun M ↦ by
    letI := ProEtale.realizationRestrictionUnit_isIso T B M
    exact asIso (ProEtale.realizationRestrictionUnit T B M)) (by
    intro M N f
    ext U x
    exact ConcreteCategory.congr_hom (congrArg (fun z ↦ z.app U)
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap T B)).unit.naturality
          ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} B)).map
            f.hom))) x)

private theorem finiteHomRealizationIsoGeneral_hom (T : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (finiteHomRealizationIsoGeneral T B).hom.app M =
      ProEtale.realizationRestrictionUnit T B M := rfl

private theorem finiteHomFixedRestrictionSectionGeneral
    (T : Scheme.{u}) (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (U : T.Etale) (x : M.obj.obj (op U)) :
    ((ProEtale.pbcComparisonRestrict T φ).hom.app M).hom.app (op (T.toProEt.obj U))
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app M).hom.app
          (op U) x) =
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)).hom.app (op U) x := by
  have hm := ProEtale.comparison_restrict_mate T φ
  have ht := unit_mateEquiv
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (TwoSquare.mk _ _ _ _ (ProEtale.pbcComparisonRestrict T φ).inv) M
  have hmc := congrArg (fun z ↦ z.app
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).obj M)) hm
  change _ ≫ _ = _ at ht
  erw [hmc] at ht
  simp only [NatTrans.id_app] at ht
  change (Sheaf.restrictScalars T.smallEtaleTopology φ).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app M) ≫ 𝟙 _ =
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).map
        ((ProEtale.pbcComparisonRestrict T φ).inv.app M) at ht
  rw [Category.comp_id] at ht
  have ht' := congrArg (fun f ↦ f.hom.app (op U) x) ht
  have hi := congrArg (fun f ↦ f.hom.app (op (T.toProEt.obj U))
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)).hom.app (op U) x))
    ((ProEtale.pbcComparisonRestrict T φ).inv_hom_id_app M)
  change ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app M).hom.app
      (op U) x =
    ((ProEtale.pbcComparisonRestrict T φ).inv.app M).hom.app
      (op (T.toProEt.obj U))
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)).hom.app (op U) x) at ht'
  change ((ProEtale.pbcComparisonRestrict T φ).hom.app M).hom.app
      (op (T.toProEt.obj U))
      (((ProEtale.pbcComparisonRestrict T φ).inv.app M).hom.app
        (op (T.toProEt.obj U))
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)).hom.app (op U) x)) =
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)).hom.app (op U) x at hi
  exact (congrArg (fun y ↦
    ((ProEtale.pbcComparisonRestrict T φ).hom.app M).hom.app
      (op (T.toProEt.obj U)) y) ht').trans hi

private def finiteHomNuEncodedGeneral (T : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B] :
    ProEtale.finiteCoefficientIntrinsicComparison T B ⋙
      Scheme.proEtaleModuleRestriction T B ≅
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T :=
  (Functor.isoWhiskerLeft
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T)
    (finiteHomRealizationIsoGeneral T B)).symm

private def finiteHomEncodedSquare
    {A B C D E F : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F]
    (N : A ⥤ B) (R : B ⥤ C) (T : C ⥤ D) (S : B ⥤ E) (U : E ⥤ D)
    (V : A ⥤ E) (P : A ⥤ F) (Q : F ⥤ C) (W : F ⥤ D)
    (β : R ⋙ T ≅ S ⋙ U) (γ : N ⋙ S ≅ V) (δ : Q ⋙ T ≅ W)
    (ε : V ⋙ U ≅ P ⋙ W) :
    (N ⋙ R) ⋙ T ≅ (P ⋙ Q) ⋙ T :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft N β ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ U ≪≫ ε ≪≫
    Functor.isoWhiskerLeft P δ.symm ≪≫ (Functor.associator _ _ _).symm

private theorem finiteHomEncodedSquare_hom_app
    {A B C D E F : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F]
    (N : A ⥤ B) (R : B ⥤ C) (T : C ⥤ D) (S : B ⥤ E) (U : E ⥤ D)
    (V : A ⥤ E) (P : A ⥤ F) (Q : F ⥤ C) (W : F ⥤ D)
    (β : R ⋙ T ≅ S ⋙ U) (γ : N ⋙ S ≅ V) (δ : Q ⋙ T ≅ W)
    (ε : V ⋙ U ≅ P ⋙ W) (M : A) :
    (finiteHomEncodedSquare N R T S U V P Q W β γ δ ε).hom.app M =
      β.hom.app (N.obj M) ≫ U.map (γ.hom.app M) ≫ ε.hom.app M ≫
        δ.inv.app (P.obj M) := by
  simp only [finiteHomEncodedSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private def finiteHomNuSectionGeneral (X : Scheme.{u}) (B : Type u) [CommRing B]
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (U : X.Etale) (x : M.obj.obj (op U)) :
    ((ProEtale.finiteCoefficientIntrinsicComparison X B).obj M).val.obj (op (X.toProEt.obj U)) :=
  (((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap X
        B)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
        (ULift.{u + 1, u} B)).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} B)) X).obj M).obj)).app
      (op (X.toProEt.obj U)))
    ((((ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
      (ULift.{u + 1, u} B)) X).unit.app M).hom.app
        (op U)) x)

private def finiteHomNuAdjointMapGeneral (X : Scheme.{u}) (B : Type u) [CommRing B]
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (N : Scheme.proEtaleRingModules X (proEtaleConstantRing X B))
    (f : (ProEtale.finiteCoefficientIntrinsicComparison X B).obj M ⟶ N) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} B)) X).obj M ⟶
      (Scheme.proEtaleModuleRestriction X
        B).obj N := by
  let a := (PresheafOfModules.sheafificationAdjunction
    (ProEtale.finiteCoefficientIntrinsicScalarMap X
      B)).homEquiv _ N f
  exact ⟨{ app := a.app
           naturality := fun _ _ g ↦ by
             ext x
             exact ConcreteCategory.congr_hom (a.naturality g) x }⟩

private theorem finiteHomNu_hom_extGeneral (X : Scheme.{u}) (B : Type u) [CommRing B]
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (N : Scheme.proEtaleRingModules X (proEtaleConstantRing X B))
    (f g : (ProEtale.finiteCoefficientIntrinsicComparison X B).obj M ⟶ N)
    (h : ∀ (U : X.Etale) (x : M.obj.obj (op U)),
      f.val.app (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X B M U x) =
        g.val.app (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X B M U x)) : f = g := by
  have ha : finiteHomNuAdjointMapGeneral X B M N f =
      finiteHomNuAdjointMapGeneral X B M N g := by
    apply ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
      (ULift.{u + 1, u} B)) X).homEquiv _
        _).injective
    apply Sheaf.hom_ext
    ext U x
    exact h U.unop x
  apply ((PresheafOfModules.sheafificationAdjunction
    (ProEtale.finiteCoefficientIntrinsicScalarMap X
      B)).homEquiv _ N).injective
  ext U x
  exact congrArg (fun z ↦ z.hom.app U x) ha

section GenericOrdinary
variable (X : Scheme.{u}) (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
variable (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
variable (f : (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A) ⟶
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X B))
variable (hη : (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
  ProEtale.finiteCoefficientIntrinsicScalarMap X B =
    ProEtale.finiteCoefficientIntrinsicScalarMap X A ≫ f.hom)
private instance : (Scheme.proEtaleModuleRestriction X A).IsEquivalence :=
  Scheme.proEtaleModuleRestriction_isEquivalence X A
private def finiteHomRestrictionEncodedGeneral :
    (ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f) ⋙
        Scheme.proEtaleModuleRestriction X A ≅
      (Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A) ⋙ Scheme.proEtaleModuleRestriction X A :=
  finiteHomEncodedSquare _ _ _ _ _ _ _ _ _
    (finiteHomEncodingRestrictionGeneral X A B φ f hη)
    (finiteHomNuEncodedGeneral X B) (finiteHomNuEncodedGeneral X A)
    (ProEtale.pbcComparisonRestrict X φ)

private theorem finiteHomRestrictionEncoded_hom_appGeneral
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (finiteHomRestrictionEncodedGeneral X A B φ f hη).hom.app M =
      (finiteHomEncodingRestrictionGeneral X A B φ f hη).hom.app
        ((ProEtale.finiteCoefficientIntrinsicComparison X B).obj M) ≫
        (Sheaf.restrictScalars (ProEt.topology X) φ).map
          ((finiteHomNuEncodedGeneral X B).hom.app M) ≫
        (ProEtale.pbcComparisonRestrict X φ).hom.app M ≫
        (finiteHomNuEncodedGeneral X A).inv.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) :=
  finiteHomEncodedSquare_hom_app _ _ _ _ _ _ _ _ _ _ _ _ _ M

private def finiteHomRestrictionCandidateGeneral :
    ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A :=
  Functor.fullyFaithfulCancelRight (Scheme.proEtaleModuleRestriction X A)
    (finiteHomRestrictionEncodedGeneral X A B φ f hη)

private theorem finiteHomRestrictionCandidate_mapGeneral
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (Scheme.proEtaleModuleRestriction X A).map
      ((finiteHomRestrictionCandidateGeneral X A B φ f hη).hom.app M) =
        (finiteHomRestrictionEncodedGeneral X A B φ f hη).hom.app M := by
  simp only [finiteHomRestrictionCandidateGeneral, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]

/-- Identity-on-generators normalization for comparison and scalar restriction.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
private def FiniteHomNuRestrictionNormalizationGeneral
    (σ : ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A) : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (U : X.Etale) (x : M.obj.obj (op U)),
    ∃ (z : ((ProEtale.finiteCoefficientIntrinsicComparison X B ⋙
          SheafOfModules.restrictScalars f).obj M).val.obj (op (X.toProEt.obj U)))
      (y : ((Sheaf.restrictScalars X.smallEtaleTopology
          φ).obj M).obj.obj (op U)),
      HEq z (finiteHomNuSectionGeneral X B M U x) ∧ HEq y x ∧
      HEq (((σ.hom.app M).val.app (op (X.toProEt.obj U))) z)
        (finiteHomNuSectionGeneral X A
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) U y)

private theorem finiteHomRestrictionCandidate_normalizedGeneral :
    FiniteHomNuRestrictionNormalizationGeneral X A B φ f
      (finiteHomRestrictionCandidateGeneral X A B φ f hη) := by
  intro M U x
  refine ⟨finiteHomNuSectionGeneral X B M U x, x, HEq.rfl, HEq.rfl, ?_⟩
  apply heq_of_eq
  have hp := finiteHomRestrictionCandidate_mapGeneral X A B φ f hη M
  have hp' := congrArg (fun f ↦ f.hom.app (op (X.toProEt.obj U))
    (finiteHomNuSectionGeneral X B M U x)) hp
  change ((finiteHomRestrictionCandidateGeneral X A B φ f hη).hom.app M).val.app
      (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X B M U x) = _ at hp'
  refine hp'.trans ?_
  rw [finiteHomRestrictionEncoded_hom_appGeneral]
  change ((finiteHomRealizationIsoGeneral X A).hom.app
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M))).hom.app
      (op (X.toProEt.obj U))
      (((ProEtale.pbcComparisonRestrict X φ).hom.app M).hom.app
        (op (X.toProEt.obj U))
        (((finiteHomRealizationIsoGeneral X B).inv.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).obj
            M)).hom.app (op (X.toProEt.obj U))
              ((((finiteHomEncodingRestrictionGeneral X A B φ f hη).hom.app
                ((ProEtale.finiteCoefficientIntrinsicComparison X B).obj M)).hom.app
                  (op (X.toProEt.obj U))) (finiteHomNuSectionGeneral X B M U x)))) = _
  rw [finiteHomEncodingRestrictionGeneral_sections]
  have hi := congrArg (fun f ↦ f.hom.app (op (X.toProEt.obj U))
    ((((ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
      (ULift.{u + 1, u} B)) X).unit.app M).hom.app
        (op U)) x))
    ((finiteHomRealizationIsoGeneral X B).hom_inv_id_app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} B)) X).obj M))
  rw [finiteHomRealizationIsoGeneral_hom] at hi
  change ((finiteHomRealizationIsoGeneral X B).inv.app
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} B)) X).obj M)).hom.app
        (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X B M U x) =
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).unit.app
        M).hom.app (op U) x at hi
  rw [hi, finiteHomFixedRestrictionSectionGeneral, finiteHomRealizationIsoGeneral_hom]
  rfl

omit [Finite A] [Finite B] in
private theorem finiteHomRestriction_uniqueGeneral
    (σ τ : ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A)
    (hσ : FiniteHomNuRestrictionNormalizationGeneral X A B φ f σ)
    (hτ : FiniteHomNuRestrictionNormalizationGeneral X A B φ f τ) : σ = τ := by
  suffices hs : σ.symm = τ.symm from congrArg Iso.symm hs
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply finiteHomNu_hom_extGeneral X A
  intro U x
  obtain ⟨zσ, yσ, hzσ, hyσ, heσ⟩ := hσ M U x
  obtain ⟨zτ, yτ, hzτ, hyτ, heτ⟩ := hτ M U x
  have hyσ' : yσ = x := eq_of_heq hyσ
  have hyτ' : yτ = x := eq_of_heq hyτ
  subst yσ
  subst yτ
  have hz : zσ = zτ := eq_of_heq (hzσ.trans hzτ.symm)
  have hiσ := congrArg (fun f ↦ f.val.app (op (X.toProEt.obj U)) zσ)
    (σ.hom_inv_id_app M)
  have hiτ := congrArg (fun f ↦ f.val.app (op (X.toProEt.obj U)) zτ)
    (τ.hom_inv_id_app M)
  change (σ.inv.app M).val.app (op (X.toProEt.obj U))
    ((σ.hom.app M).val.app (op (X.toProEt.obj U)) zσ) = zσ at hiσ
  change (τ.inv.app M).val.app (op (X.toProEt.obj U))
    ((τ.hom.app M).val.app (op (X.toProEt.obj U)) zτ) = zτ at hiτ
  rw [eq_of_heq heσ] at hiσ
  rw [eq_of_heq heτ] at hiτ
  exact hiσ.trans (hz.trans hiτ.symm)

private theorem finiteHomRestrictionCandidate_encodingGeneral
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (Scheme.proEtaleModuleRestriction X A).map
        ((finiteHomRestrictionCandidateGeneral X A B φ f hη).hom.app M) ≫
      (finiteHomNuEncodedGeneral X A).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) =
    (finiteHomEncodingRestrictionGeneral X A B φ f hη).hom.app
        ((ProEtale.finiteCoefficientIntrinsicComparison X B).obj M) ≫
      (Sheaf.restrictScalars (ProEt.topology X) φ).map
        ((finiteHomNuEncodedGeneral X B).hom.app M) ≫
      (ProEtale.pbcComparisonRestrict X φ).hom.app M := by
  rw [finiteHomRestrictionCandidate_mapGeneral,
    finiteHomRestrictionEncoded_hom_appGeneral]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end GenericOrdinary
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finiteHomCommSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

private theorem finiteHomAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

private theorem finiteHomAbWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (finiteHomAbSheafify T).isRightAdjoint

private theorem finiteHomAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

private theorem finiteHomCompose (T : Scheme.{u}) :
    (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by infer_instance

attribute [local instance] finiteHomCommSheafify finiteHomAbSheafify
  finiteHomAbWeakSheafify finiteHomAbLocallyBijective finiteHomCompose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The actual comparison on module sheaves, with finite coefficients supplied.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuOrdinary (n : ℕ) :
    Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) ⥤
      normalizedDVRModules l E X n :=
  @ProEtale.finiteCoefficientIntrinsicComparison X (Padic.coefficientExtensionRing l E (n + 1))
    inferInstance

/-- Additivity of the published intrinsic comparison, at the positive finite stage.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
instance finiteHomNuOrdinary_additive (n : ℕ) : (finiteHomNuOrdinary l E X n).Additive :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  inferInstanceAs (ProEtale.finiteCoefficientIntrinsicComparison X
    (Padic.coefficientExtensionRing l E (n + 1))).Additive

/-- Exact comparison preserves finite limits.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
instance finiteHomNuOrdinary_limits (n : ℕ) :
    PreservesFiniteLimits (finiteHomNuOrdinary l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  inferInstanceAs (PreservesFiniteLimits (ProEtale.finiteCoefficientIntrinsicComparison X
    (Padic.coefficientExtensionRing l E (n + 1))))

/-- Exact comparison preserves finite colimits.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
instance finiteHomNuOrdinary_colimits (n : ℕ) :
    PreservesFiniteColimits (finiteHomNuOrdinary l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  inferInstanceAs (PreservesFiniteColimits (ProEtale.finiteCoefficientIntrinsicComparison X
    (Padic.coefficientExtensionRing l E (n + 1))))

/-- The exact derived inverse image nu_X^* in the intrinsic constant-ring presentation.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNu (n : ℕ) : finiteHomEtale l E X n ⥤ normalizedDVRDerived l E X n :=
  (finiteHomNuOrdinary l E X n).mapDerivedCategory

/-- A section mapped by the comparison unit and the associated-module-sheaf unit.
Source: blueprint site formula; Stacks 00YV
(blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuSection (n : ℕ)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)) :
    ((finiteHomNuOrdinary l E X n).obj M).val.obj (op (X.toProEt.obj U)) :=
  (((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap X
        (Padic.coefficientExtensionRing l E (n + 1)))).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).obj M).obj)).app
      (op (X.toProEt.obj U)))
    ((((ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).unit.app M).hom.app
        (op U)) x)

private theorem finiteHomCoefficientMap {n m : ℕ} (h : m ≤ n) :
    normalizedDVRQuotient l E X h =
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (finiteHomQuotient l E h))) :=
  compactSupportQuotient_eq l E X h

private def finiteHomEncoding (n : ℕ) :=
  Scheme.proEtaleModuleRestriction X (Padic.coefficientExtensionRing l E (n + 1))

private instance finiteHomEncoding_equivalence (T : Scheme.{u}) (B : Type u)
    [CommRing B] : (Scheme.proEtaleModuleRestriction T B).IsEquivalence :=
  Scheme.proEtaleModuleRestriction_isEquivalence T B

private theorem finiteHomScalarUnit_naturality {n m : ℕ} (h : m ≤ n) :
    (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom (finiteHomQuotient l E h)) ≫
        ProEtale.finiteCoefficientIntrinsicScalarMap X
          (Padic.coefficientExtensionRing l E (m + 1)) =
      ProEtale.finiteCoefficientIntrinsicScalarMap X
          (Padic.coefficientExtensionRing l E (n + 1)) ≫
        (normalizedDVRQuotient l E X h).hom := by
  rw [finiteHomCoefficientMap]
  exact congrArg (fun f ↦ Functor.whiskerRight f
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (finiteHomQuotient l E h))))

private def finiteHomEncodingRestriction {n m : ℕ} (h : m ≤ n) :
    normalizedDVRModuleRes l E X h ⋙ finiteHomEncoding l E X n ≅
      finiteHomEncoding l E X m ⋙
        Sheaf.restrictScalars (ProEt.topology X) (finiteHomQuotient l E h) :=
  finiteHomEncodingRestrictionGeneral X _ _ (finiteHomQuotient l E h)
    (normalizedDVRQuotient l E X h) (finiteHomScalarUnit_naturality l E X h)

attribute [local irreducible] finiteHomEncodingRestrictionGeneral finiteHomRealizationIsoGeneral

private def finiteHomNuEncoded (n : ℕ) :
    finiteHomNuOrdinary l E X n ⋙ finiteHomEncoding l E X n ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  finiteHomNuEncodedGeneral X _

private def finiteHomRestrictionCandidate {n m : ℕ} (h : m ≤ n) :
    finiteHomNuOrdinary l E X m ⋙ normalizedDVRModuleRes l E X h ≅
      Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNuOrdinary l E X n :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  finiteHomRestrictionCandidateGeneral X _ _ (finiteHomQuotient l E h)
    (normalizedDVRQuotient l E X h) (finiteHomScalarUnit_naturality l E X h)

/-- Identity-on-generators normalization for comparison and scalar restriction.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def FiniteHomNuRestrictionNormalization {n m : ℕ} (h : m ≤ n)
    (σ : finiteHomNuOrdinary l E X m ⋙ normalizedDVRModuleRes l E X h ≅
      Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNuOrdinary l E X n) : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)),
    ∃ (z : ((finiteHomNuOrdinary l E X m ⋙
          normalizedDVRModuleRes l E X h).obj M).val.obj (op (X.toProEt.obj U)))
      (y : ((Sheaf.restrictScalars X.smallEtaleTopology
          (finiteHomQuotient l E h)).obj M).obj.obj (op U)),
      HEq z (finiteHomNuSection l E X m M U x) ∧ HEq y x ∧
      HEq (((σ.hom.app M).val.app (op (X.toProEt.obj U))) z)
        (finiteHomNuSection l E X n
          ((Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)).obj M) U y)

private theorem finiteHomRestrictionCandidate_normalized {n m : ℕ} (h : m ≤ n) :
    FiniteHomNuRestrictionNormalization l E X h
      (finiteHomRestrictionCandidate l E X h) := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  exact finiteHomRestrictionCandidate_normalizedGeneral X _ _ (finiteHomQuotient l E h)
    (normalizedDVRQuotient l E X h) (finiteHomScalarUnit_naturality l E X h)

private theorem finiteHomRestriction_unique {n m : ℕ} (h : m ≤ n)
    (σ τ : finiteHomNuOrdinary l E X m ⋙ normalizedDVRModuleRes l E X h ≅
      Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNuOrdinary l E X n)
    (hσ : FiniteHomNuRestrictionNormalization l E X h σ)
    (hτ : FiniteHomNuRestrictionNormalization l E X h τ) : σ = τ := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  exact finiteHomRestriction_uniqueGeneral X _ _ (finiteHomQuotient l E h)
    (normalizedDVRQuotient l E X h) σ τ hσ hτ

/-- Restriction commutes canonically with inverse image, fixing every local generator.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: on underlying module presheaves scalar restriction does not change sections.
The two inverse-image constructions are left Kan extension followed by module
sheafification. The identity on the displayed generators respects scalar balancing,
restriction, and gluing. It extends to a natural isomorphism; the identity in the
opposite direction is inverse. These generators locally generate the associated
sheaf, so the normalization determines every component uniquely. -/
theorem finiteHomNuRestriction_existsUnique {n m : ℕ} (h : m ≤ n) :
    ∃! σ, FiniteHomNuRestrictionNormalization l E X h σ := by
  exact ⟨finiteHomRestrictionCandidate l E X h,
    finiteHomRestrictionCandidate_normalized l E X h,
    fun σ hσ ↦ finiteHomRestriction_unique l E X h σ _ hσ
      (finiteHomRestrictionCandidate_normalized l E X h)⟩

/-- The uniquely normalized ordinary scalar-restriction comparison.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuRestriction {n m : ℕ} (h : m ≤ n) :
    finiteHomNuOrdinary l E X m ⋙ normalizedDVRModuleRes l E X h ≅
      Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNuOrdinary l E X n :=
  (finiteHomNuRestriction_existsUnique l E X h).choose

private theorem finiteHomNuRestriction_eq_candidate {n m : ℕ} (h : m ≤ n) :
    finiteHomNuRestriction l E X h = finiteHomRestrictionCandidate l E X h := by
  apply finiteHomRestriction_unique l E X h
  · exact (finiteHomNuRestriction_existsUnique l E X h).choose_spec.1
  · exact finiteHomRestrictionCandidate_normalized l E X h

private theorem finiteHomRestriction_encoding {n m : ℕ} (h : m ≤ n)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))))) :
    (finiteHomEncoding l E X n).map ((finiteHomNuRestriction l E X h).hom.app M) ≫
        (finiteHomNuEncoded l E X n).hom.app
          ((Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)).obj M) =
      (finiteHomEncodingRestriction l E X h).hom.app ((finiteHomNuOrdinary l E X m).obj M) ≫
        (Sheaf.restrictScalars (ProEt.topology X) (finiteHomQuotient l E h)).map
          ((finiteHomNuEncoded l E X m).hom.app M) ≫
        (ProEtale.pbcComparisonRestrict X (finiteHomQuotient l E h)).hom.app M := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  rw [finiteHomNuRestriction_eq_candidate]
  exact finiteHomRestrictionCandidate_encodingGeneral X _ _ (finiteHomQuotient l E h)
    (normalizedDVRQuotient l E X h) (finiteHomScalarUnit_naturality l E X h) M

/-- Exact descent of the canonical scalar-restriction comparison.
Source: blueprint canonical site maps (blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomNuDerivedRestriction {n m : ℕ} (h : m ≤ n) :
    finiteHomNu l E X m ⋙ normalizedDVRRes l E X h ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h) ⋙
        finiteHomNu l E X n :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (finiteHomNuRestriction l E X h) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Beta is the canonical left-adjoint mate of identity-on-sections scalar restriction.
Source: blueprint nu_X^* coefficient formula
(blueprint: def-sf-finite-coefficient-site-scalar-arrow). -/
def finiteHomSiteBeta {n m : ℕ} (h : m ≤ n) :
    finiteHomNu l E X n ⋙ coefficientFiniteQuotientDerived l E X h ⟶
      finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)))
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)).symm
    (TwoSquare.mk _ _ _ _ (finiteHomNuDerivedRestriction l E X h).inv))

private instance finiteHomEncoding_additive (T : Scheme.{u}) (B : Type u) [CommRing B] :
    (Scheme.proEtaleModuleRestriction T B).Additive where
  map_add := by intros; ext U x; rfl

private instance finiteHomConcreteEncoding_additive (n : ℕ) :
    (finiteHomEncoding l E X n).Additive :=
  finiteHomEncoding_additive X _

private instance finiteHomConcreteEncoding_equivalence (n : ℕ) :
    (finiteHomEncoding l E X n).IsEquivalence :=
  Scheme.proEtaleModuleRestriction_isEquivalence X _

private instance finiteHomConcreteEncoding_limits (n : ℕ) :
    PreservesFiniteLimits (finiteHomEncoding l E X n) :=
  inferInstanceAs (PreservesFiniteLimits
    (Scheme.proEtaleModuleRestriction X (Padic.coefficientExtensionRing l E (n + 1))))

private instance finiteHomConcreteEncoding_colimits (n : ℕ) :
    PreservesFiniteColimits (finiteHomEncoding l E X n) :=
  inferInstanceAs (PreservesFiniteColimits
    (Scheme.proEtaleModuleRestriction X (Padic.coefficientExtensionRing l E (n + 1))))

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedLeftWhisker
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (I : B ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : G ⋙ H ≅ I) (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryCompNatIso (F := F ⋙ G) (G := H)
      (Functor.isoWhiskerLeft F e)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F I).inv.app K =
      H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).inv.app K) ≫
        (Functor.mapDerivedCategoryCompNatIso e).hom.app (F.mapDerivedCategory.obj K) := by
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn ha
  have ht := congrArg (fun z ↦
    (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).hom.app K ≫ z ≫
      (Functor.mapDerivedCategoryCompIso G H).hom.app (F.mapDerivedCategory.obj K)) ha
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app] at ht
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  have ht' : (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv.app K =
    H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso G H).hom.app (F.mapDerivedCategory.obj K) := by
    erw [Category.comp_id] at ht
    exact ht
  rw [hn, ← Category.assoc, ht', Category.assoc]

private theorem derivedRightWhisker
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : A ⥤ B) (U : B ⥤ C) (S : C ⥤ D) (V : A ⥤ C)
    (P : A ⥤ E) (Q : E ⥤ D)
    [F.Additive] [U.Additive] [S.Additive] [V.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (γ : F ⋙ U ≅ V) (ε : V ⋙ S ≅ P ⋙ Q) (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryCompNatIso (F := F) (G := U ⋙ S)
      (Functor.isoWhiskerRight γ S ≪≫ ε)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso P Q).inv.app K =
      (Functor.mapDerivedCategoryCompIso U S).inv.app (F.mapDerivedCategory.obj K) ≫
        S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso γ).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso ε).hom.app K := by
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight γ S) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc F U S) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn ha
  have ht := congrArg (fun z ↦
    (Functor.mapDerivedCategoryCompIso F (U ⋙ S)).hom.app K ≫ z ≫
      S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F U).hom.app K)) ha
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id] at ht
  simp only [Functor.mapDerivedCategoryCompNatIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_trans, Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht]
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem derivedCompatibility
    {A B C D E J : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category J]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian J]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory J]
    (F : A ⥤ B) (R : B ⥤ C) (T : C ⥤ D) (U : B ⥤ E) (S : E ⥤ D)
    (V : A ⥤ E) (P : A ⥤ J) (Q : J ⥤ C) (Q' : J ⥤ D)
    [F.Additive] [R.Additive] [T.Additive] [U.Additive] [S.Additive]
    [V.Additive] [P.Additive] [Q.Additive] [Q'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
    (α : F ⋙ R ≅ P ⋙ Q) (β : R ⋙ T ≅ U ⋙ S)
    (γ : F ⋙ U ≅ V) (δ : Q ⋙ T ≅ Q') (ε : V ⋙ S ≅ P ⋙ Q')
    (h : ∀ M, T.map (α.hom.app M) ≫ δ.hom.app (P.obj M) =
      β.hom.app (F.obj M) ≫ S.map (γ.hom.app M) ≫ ε.hom.app M)
    (K : DerivedCategory A) :
    T.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso α).hom.app K) ≫
        (Functor.mapDerivedCategoryCompNatIso δ).hom.app (P.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso β).hom.app (F.mapDerivedCategory.obj K) ≫
        S.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso γ).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso ε).hom.app K := by
  have hd := Functor.mapDerivedCategoryCompNatIso_cocycle α
    (Functor.isoWhiskerLeft P δ) β (Functor.isoWhiskerRight γ S ≪≫ ε) h K
  have hl := derivedLeftWhisker P Q T Q' δ K
  have hr := derivedRightWhisker F U S V P Q' γ ε K
  have hz := congrArg (fun z ↦ z ≫ (Functor.mapDerivedCategoryCompIso P Q').inv.app K) hd
  simp only [Category.assoc] at hz
  rw [hl, hr] at hz
  simpa only [Functor.mapDerivedCategoryCompNatIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using hz

private theorem transferLeftMate
    {A B C D E F : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F]
    {L : A ⥤ B} {R : B ⥤ A} {M : C ⥤ D} {U : D ⥤ C}
    {K : E ⥤ F} {V : F ⥤ E}
    (a : L ⊣ R) (b : M ⊣ U) (c : K ⊣ V)
    (T : C ⥤ E) (S : D ⥤ F) [S.ReflectsIsomorphisms]
    {N : A ⥤ C} {P : B ⥤ D} {N' : A ⥤ E} {P' : B ⥤ F}
    (α : T ⋙ K ⟶ M ⋙ S) [IsIso α]
    (β : S ⋙ V ≅ U ⋙ T) (γ : N' ≅ N ⋙ T) (δ : P' ≅ P ⋙ S)
    (τ : R ⋙ N ⟶ P ⋙ U) (τ' : R ⋙ N' ⟶ P' ⋙ V)
    (hu : ∀ X, c.unit.app (T.obj X) ≫ V.map (α.app X) ≫
      β.hom.app (M.obj X) = T.map (b.unit.app X))
    (ht : ∀ X, γ.hom.app (R.obj X) ≫ T.map (τ.app X) =
      τ'.app X ≫ V.map (δ.hom.app X) ≫ β.hom.app (P.obj X))
    [IsIso (((mateEquiv a c).symm (TwoSquare.mk _ _ _ _ τ')))] :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ))) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  have he := AlgebraicGeometry.ProEtale.left_mate_normalization a b a c
    (𝟭 _) (𝟭 _) T S (𝟙 _) α (Iso.refl _) β γ δ τ τ'
    (fun Y ↦ by simp) hu
    (fun Y ↦ by
      change N'.map (𝟙 _) ≫ γ.hom.app (R.obj Y) ≫ T.map (τ.app Y) =
        τ'.app Y ≫ V.map (δ.hom.app Y) ≫ β.hom.app (P.obj Y)
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact ht Y) X
  have hi : IsIso (K.map (γ.hom.app X) ≫ α.app (N.obj X) ≫
      S.map (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).app X)) := by
    rw [← he]
    infer_instance
  have : IsIso (S.map
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).app X)) :=
    (isIso_comp_left_iff _ _).1 ((isIso_comp_left_iff _ _).1 hi)
  exact isIso_of_reflects_iso _ S

private theorem leftMateUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (T : A ⥤ C) (S : B ⥤ D)
    (e : R ⋙ T ≅ S ⋙ R') (X : A) :
    b.unit.app (T.obj X) ≫ R'.map
        (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).app X) ≫
      e.inv.app (L.obj X) = T.map (a.unit.app X) := by
  have h := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ e.hom) X
  have ht := congrArg (fun z ↦ z ≫ e.inv.app (L.obj X)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at ht
  erw [Category.comp_id] at ht
  exact ht.symm

private theorem reverseEncoding
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {A B : C} {W V Z : D}
    (a : A ≅ B) (b : T.obj B ≅ W) (c : T.obj A ≅ V) (d : V ≅ Z) (e : Z ≅ W)
    (h : T.map a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    b.inv ≫ T.map a.inv = e.inv ≫ d.inv ≫ c.inv := by
  have he : T.mapIso a ≪≫ b = c ≪≫ d ≪≫ e := Iso.ext h
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using
    congrArg Iso.inv he

private def finiteHomNuDerivedEncoded (n : ℕ) :
    finiteHomNu l E X n ⋙ (finiteHomEncoding l E X n).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).mapDerivedCategory := by
  letI := finiteHomConcreteEncoding_additive l E X n
  letI := finiteHomConcreteEncoding_limits l E X n
  letI := finiteHomConcreteEncoding_colimits l E X n
  exact Functor.mapDerivedCategoryCompIso (finiteHomNuOrdinary l E X n)
    (finiteHomEncoding l E X n) ≪≫
      Functor.mapDerivedCategoryNatIso (finiteHomNuEncoded l E X n)

private def finiteHomDerivedEncodingRestriction {n m : ℕ} (h : m ≤ n) :
    normalizedDVRRes l E X h ⋙ (finiteHomEncoding l E X n).mapDerivedCategory ≅
      (finiteHomEncoding l E X m).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h) := by
  letI := finiteHomConcreteEncoding_additive l E X n
  letI := finiteHomConcreteEncoding_limits l E X n
  letI := finiteHomConcreteEncoding_colimits l E X n
  letI := finiteHomConcreteEncoding_additive l E X m
  letI := finiteHomConcreteEncoding_limits l E X m
  letI := finiteHomConcreteEncoding_colimits l E X m
  exact Functor.mapDerivedCategorySquareIso (finiteHomEncodingRestriction l E X h)

private theorem finiteHomDerivedRestriction_encoding {n m : ℕ} (h : m ≤ n)
    (K : finiteHomEtale l E X m) :
    (finiteHomEncoding l E X n).mapDerivedCategory.map
        ((finiteHomNuDerivedRestriction l E X h).hom.app K) ≫
        (finiteHomNuDerivedEncoded l E X n).hom.app
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
            (finiteHomQuotient l E h)).obj K) =
      (finiteHomDerivedEncodingRestriction l E X h).hom.app ((finiteHomNu l E X m).obj K) ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h)).map
          ((finiteHomNuDerivedEncoded l E X m).hom.app K) ≫
        (ProEtale.pbcDerivedComparisonRestrict X (finiteHomQuotient l E h)).hom.app K := by
  let := finiteHomConcreteEncoding_additive l E X n
  let := finiteHomConcreteEncoding_limits l E X n
  let := finiteHomConcreteEncoding_colimits l E X n
  let := finiteHomConcreteEncoding_additive l E X m
  let := finiteHomConcreteEncoding_limits l E X m
  let := finiteHomConcreteEncoding_colimits l E X m
  exact derivedCompatibility _ _ _ _ _ _ _ _ _
    (finiteHomNuRestriction l E X h) (finiteHomEncodingRestriction l E X h)
    (finiteHomNuEncoded l E X m) (finiteHomNuEncoded l E X n)
    (ProEtale.pbcComparisonRestrict X (finiteHomQuotient l E h))
    (finiteHomRestriction_encoding l E X h) K

private theorem finiteHomDerivedRestriction_inverse_encoding {n m : ℕ} (h : m ≤ n)
    (K : finiteHomEtale l E X m) :
    (finiteHomNuDerivedEncoded l E X n).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteHomQuotient l E h)).obj K) ≫
      (finiteHomEncoding l E X n).mapDerivedCategory.map
        ((finiteHomNuDerivedRestriction l E X h).inv.app K) =
    (ProEtale.pbcDerivedComparisonRestrict X (finiteHomQuotient l E h)).inv.app K ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h)).map
        ((finiteHomNuDerivedEncoded l E X m).inv.app K) ≫
      (finiteHomDerivedEncodingRestriction l E X h).inv.app ((finiteHomNu l E X m).obj K) := by
  exact reverseEncoding (finiteHomEncoding l E X n).mapDerivedCategory
    ((finiteHomNuDerivedRestriction l E X h).app K)
    ((finiteHomNuDerivedEncoded l E X n).app
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteHomQuotient l E h)).obj K))
    ((finiteHomDerivedEncodingRestriction l E X h).app ((finiteHomNu l E X m).obj K))
    ((Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h)).mapIso
      ((finiteHomNuDerivedEncoded l E X m).app K))
    ((ProEtale.pbcDerivedComparisonRestrict X (finiteHomQuotient l E h)).app K)
    (finiteHomDerivedRestriction_encoding l E X h K)

private theorem finiteHomEquivalenceLeftMate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} [G.IsEquivalence] [H.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (τ : R ⋙ G ≅ H ⋙ R') :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ.hom))) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ.hom))
  let τop : TwoSquare H.op R.op R'.op G.op :=
    TwoSquare.mk _ _ _ _ (NatTrans.op τ.hom)
  have hi := isIso_mateEquiv_of_isEquivalence a.op b.op τop
  have he : NatTrans.op α = (mateEquiv a.op b.op τop) := by
    ext X
    simp [α, τop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

private def finiteHomScalarEncodingMate {n m : ℕ} (h : m ≤ n) :
    (finiteHomEncoding l E X n).mapDerivedCategory ⋙
        ProEtale.pbcFixedScalarExtension (ProEt.topology X) (finiteHomQuotient l E h) ⟶
      coefficientFiniteQuotientDerived l E X h ⋙
        (finiteHomEncoding l E X m).mapDerivedCategory :=
  ((mateEquiv
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h)))).symm
    (TwoSquare.mk _ _ _ _ (finiteHomDerivedEncodingRestriction l E X h).hom))

private instance finiteHomScalarEncodingMate_isIso {n m : ℕ} (h : m ≤ n) :
    IsIso (finiteHomScalarEncodingMate l E X h) :=
  finiteHomEquivalenceLeftMate_isIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h)))
    (finiteHomDerivedEncodingRestriction l E X h)

/-- The specified beta mate is invertible on every ambient object.
Source: blueprint site-comparison paragraph
(blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: encode intrinsic module sheaves by their constant scalar action. The
canonical sheafification units identify encoded inverse image with the ordinary
fixed-ring comparison. The section normalization identifies the restriction
square with the conjugate fixed-ring square. Exact localization preserves this
identity. The mate of the encoding square is invertible because both encodings
are equivalences. Mate normalization then identifies the encoded beta, up to
invertible factors, with the proved fixed-ring comparison mate. Cancel those
factors and reflect isomorphisms through the derived encoding equivalence. -/
@[instance] theorem finiteHomSiteBeta_isIso {n m : ℕ} (h : m ≤ n) :
    IsIso (finiteHomSiteBeta l E X h) := by
  let a := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h))
  let b := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h
  let c := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology X) (finiteHomQuotient l E h))
  let T := (finiteHomEncoding l E X n).mapDerivedCategory
  let S := (finiteHomEncoding l E X m).mapDerivedCategory
  let α := finiteHomScalarEncodingMate l E X h
  have : IsIso α := finiteHomScalarEncodingMate_isIso l E X h
  let β := (finiteHomDerivedEncodingRestriction l E X h).symm
  let γ := (finiteHomNuDerivedEncoded l E X n).symm
  let δ := (finiteHomNuDerivedEncoded l E X m).symm
  have : IsIso (((mateEquiv a c).symm
      (TwoSquare.mk _ _ _ _
        (ProEtale.pbcDerivedComparisonRestrict X (finiteHomQuotient l E h)).inv))) :=
    ProEtale.pbcComparisonReductionMap_isIso X (finiteHomQuotient l E h)
  exact transferLeftMate a b c T S α β γ δ
    (finiteHomNuDerivedRestriction l E X h).inv
    (ProEtale.pbcDerivedComparisonRestrict X (finiteHomQuotient l E h)).inv
    (leftMateUnit b c T S (finiteHomDerivedEncodingRestriction l E X h))
    (finiteHomDerivedRestriction_inverse_encoding l E X h)

end WeilConjectures
