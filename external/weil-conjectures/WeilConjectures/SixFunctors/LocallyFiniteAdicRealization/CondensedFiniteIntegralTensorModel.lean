/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import all WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiltrationModels
import all WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationCocone
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus

/-! # An integral tensor presentation of a finite condensed model

Source: Bhatt--Scholze, Proposition 6.8.14(2), with Lemma 6.8.2.
(blueprint: lem-sf-condensed-finite-integral-tensor-model).
Only one finite condensed coefficient model is considered here; no object descent
from the algebraic closure or normalized functor is part of this assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

attribute [local irreducible] sections CoefficientPresentation.integralMap

/- Residue normalization identifies the integral coefficient presentations. -/
section IntegralComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsCommMonObj (abRing l X)]
  [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : F →ₐ[ℚ_[l]] PadicAlgCl l) (C : CoefficientPresentation l X F i)

private theorem rational_integral_projection (s : RationalModuleRealization l F X) (n : ℕ) :
    s.integralIso.hom ≫ continuousCoefficientReduction l F X n =
      pbcAdicProjection X (pbcIntegralDatum l F) n ≫ (s.finiteIso n).hom := by
  apply (cancel_epi (RationalModuleRealization.integralIso s).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  letI : TopologicalSpace (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⊥
  letI : DiscreteTopology (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  ext U a
  apply ContinuousMap.ext
  intro x
  apply ULift.down_injective
  exact (s.integral_normalization n U a x).symm

private theorem rational_integral_comparison (s : RationalModuleRealization l F X) :
    s.integralIso.hom ≫ C.integral.hom = (purCoefficientIso l F X).hom := by
  let B : ContinuousRational.Base l :=
    { scheme := X, dimension := Fact.out, prime_unit := Fact.out }
  let A := adicLisseForget X
  have h : A.mapIso (s.integralIso ≪≫ C.integral) =
      integralDetailedCoefficientComparison X l F := by
    apply (integralDetailedCoefficientComparison_exists X l F).unique
      ?_ (integralDetailedCoefficientComparison_exists X l F).exists.choose_spec
    intro n
    have hn : s.integralIso.hom ≫ C.integral.hom ≫
        completedIntegralCommRingProjectionUnrestricted l F X n =
        pbcAdicProjection X (pbcIntegralDatum l F) n ≫
          ((pbcLevelConstantComparison X (pbcIntegralDatum l F) n).symm ≪≫
            (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso
              (integralCoefficientULift l F n).toCommRingCatIso).hom := by
      apply (cancel_mono (C.finite n).hom).mp
      have hred : C.integral.hom ≫
          completedIntegralCommRingProjectionUnrestricted l F X n ≫ (C.finite n).hom =
          continuousCoefficientReduction l F X n := by
        let : TopologicalSpace (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⊥
        let : DiscreteTopology (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) :=
          ⟨rfl⟩
        apply Sheaf.hom_ext
        ext U a
        apply ContinuousMap.ext
        intro x
        apply ULift.ext
        exact C.integral_residues n U a x
      rw [Category.assoc, Category.assoc, hred, rational_integral_projection l X F s n]
      rw [ContinuousRational.finiteIso_eq l F B s n]
      have hfinite : (C.finite n).hom =
          (discreteContinuousCoefficientIso X).hom.app
            (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := by
        let : TopologicalSpace (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⊥
        let : DiscreteTopology (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) :=
          ⟨rfl⟩
        apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
          ((Functor.const X.ProEtᵒᵖ).obj (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n))
          (finiteContinuousCoefficientSheaf l X F n)).injective
        change toSheafify (ProEt.topology X) _ ≫ (C.finite n).hom.hom =
          toSheafify (ProEt.topology X) _ ≫ (continuousCoefficientConstantComparison X
            (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n)).hom
        rw [continuousCoefficientConstantComparison_unit]
        apply NatTrans.ext
        funext U
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        apply ContinuousMap.ext
        intro x
        exact C.finite_constants n U a x
      rw [hfinite]
      rfl
    change A.map (s.integralIso.hom ≫ C.integral.hom) ≫
      A.map (completedIntegralCommRingProjectionUnrestricted l F X n) = _
    rw [← A.map_comp, Category.assoc, hn]
    rfl
  have he : s.integralIso ≪≫ C.integral = purCoefficientIso l F X := by
    apply A.mapIso_injective
    exact h.trans (purCoefficientIso_existsUnique l F X).exists.choose_spec.symm
  exact congrArg Iso.hom he

private theorem rational_integral_square (s : RationalModuleRealization l F X) :
    (purCoefficientIso l F X).hom ≫ C.integralMap l X =
      (s.integralIso.hom ≫ s.inclusion) ≫ C.rationalInclusion := by
  rw [← rational_integral_comparison l X F i C s]
  simp only [CoefficientPresentation.integralMap, Category.assoc, Iso.hom_inv_id_assoc]
  letI := coefficientExtensionNormedField l F
  have heq : C.integralInclusion = s.inclusion := by
    apply Sheaf.hom_ext
    ext U a
    apply ContinuousMap.ext
    intro x
    apply ULift.down_injective
    exact (C.integralInclusion_normalized U.unop a x).trans
      (s.inclusion_normalization U.unop a x).symm
  rw [heq]

private def extendIsoRestrict {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (b : R ≅ S) : pbcDerivedExtend b.hom ≅ pbcDerivedRestrict b.inv := by
  let e := WeilConjectures.restrictionEquivalence ((adicLisseForget X).mapIso b)
  letI : e.functor.Additive := pbcRestrict_additive b.hom
  letI : e.inverse.Additive := pbcRestrict_additive b.inv
  exact (pbcDerivedScalarAdjunction b.hom).leftAdjointUniq
    e.mapDerivedCategory.symm.toAdjunction

private theorem integral_tensor_image
    (M : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X F)))
    (hM : AdicFiniteRealization.finiteFreeTarget X (rationalCoefficientSheaf l X F) M) :
    ∃ L : sfIntegralConstructibleCategory l F X,
      Nonempty ((pbcDerivedExtend (C.integralMap l X)).obj L.obj ≅
        (pbcDerivedExtend C.rationalInclusion).obj M) := by
  classical
  let s := Classical.choice (rationalModuleRealizationFunctor l F X)
  obtain ⟨⟨N⟩, ⟨e⟩⟩ :=
    (AdicFiniteRealization.realization_image l F X s M).mp hM
  have hunit : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using
      (Fact.out : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) x
  let L : sfIntegralConstructibleCategory l F X :=
    ⟨(purCoefficientModel l F X).functor.obj N.obj,
      (purCoefficientModel_bounded_predicate l F X Fact.out hunit N.obj).mp N.property⟩
  let b := purCoefficientIso l F X
  let α := s.integralIso.hom ≫ s.inclusion
  let v := extendIsoRestrict X b
  let eM : (pbcDerivedExtend α).obj N.obj ≅ M :=
    (eqToIso (s.objects N)).symm ≪≫ e
  refine ⟨L, ⟨?_⟩⟩
  exact (pbcDerivedExtend (C.integralMap l X)).mapIso (v.app N.obj).symm ≪≫
    pbcReductionNormalization b.hom (C.integralMap l X)
      (b.hom ≫ C.integralMap l X) rfl N.obj ≪≫
    eqToIso (congrArg (fun φ ↦ (pbcDerivedExtend φ).obj N.obj)
      (rational_integral_square l X F i C s)) ≪≫
    (pbcReductionNormalization α C.rationalInclusion
      (α ≫ C.rationalInclusion) rfl N.obj).symm ≪≫
    (pbcDerivedExtend C.rationalInclusion).mapIso eM

end IntegralComparison

/- Restriction squares give the scalar extension comparisons by taking mates. -/
section SectionComparison
attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
variable (X : Scheme.{u})

private instance sectionAdditive
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj A] [IsCommMonObj A] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

private instance sectionInverseAdditive
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj A] [IsCommMonObj A] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) A).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

private abbrev sectionD
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj A] [IsCommMonObj A] :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) A).functor.mapDerivedCategory

private def section_tensor
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) S))
    (adj : L ⊣ (Mod.comap a).mapDerivedCategory) :
    L ⋙ sectionD X S ≅
      sectionD X R ⋙ pbcDerivedExtend (ProEtale.CondensedRing.sectionRingMap X a) := by
  let ER := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) R
  let ES := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) S
  letI : ER.functor.Additive := sectionAdditive X R
  letI : ER.inverse.Additive := sectionInverseAdditive X R
  letI : ES.functor.Additive := sectionAdditive X S
  letI : ES.inverse.Additive := sectionInverseAdditive X S
  letI : (sectionD X R).IsEquivalence := ER.mapDerivedCategory.isEquivalence_functor
  letI : (sectionD X S).IsEquivalence := ES.mapDerivedCategory.isEquivalence_functor
  let φ := ProEtale.CondensedRing.sectionRingMap X a
  let β : (Mod.comap a).mapDerivedCategory ⋙ sectionD X R ≅
      sectionD X S ⋙ pbcDerivedRestrict φ :=
    Functor.mapDerivedCategoryCompIso (Mod.comap a) ER.functor ≪≫
      Functor.mapDerivedCategoryNatIso (ProEtale.CondensedRing.sectionModuleComapIso X a) ≪≫
      (Functor.mapDerivedCategoryCompIso ES.functor (pbcRestrict φ)).symm
  let α := ((mateEquiv adj (pbcDerivedScalarAdjunction φ)).symm
    (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  letI : IsIso α := isIso_inverseMate_of_equivalences adj
    (pbcDerivedScalarAdjunction φ) β
  exact (asIso α).symm

variable (l : ℕ) [Fact l.Prime] [IsCommMonObj (abRing l X)]

private def nativeSectionIso : AdicFiniteRealization.closureRing l X ≅ ringSheaf l X where
  hom := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.NativeEncoding.coefficientIso l X).hom
  inv := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.NativeEncoding.coefficientIso l X).inv
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext U a
    change (ProEtale.NativeEncoding.coefficientIso l X).inv.hom.app U
      ((ProEtale.NativeEncoding.coefficientIso l X).hom.hom.app U a) = a
    have h := congrArg (fun f :
        ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X ⟶
          ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X ↦ f.hom.app U)
      (ProEtale.NativeEncoding.coefficientIso l X).hom_inv_id
    exact ConcreteCategory.congr_hom h a
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext U a
    change (ProEtale.NativeEncoding.coefficientIso l X).hom.hom.app U
      ((ProEtale.NativeEncoding.coefficientIso l X).inv.hom.app U a) = a
    have h := congrArg (fun f : abRing l X ⟶ abRing l X ↦ f.hom.app U)
      (ProEtale.NativeEncoding.coefficientIso l X).inv_hom_id
    exact ConcreteCategory.congr_hom h a

private def native_inverse_sections [hSA : (sections l X).Additive]
    [hSL : PreservesFiniteLimits (sections l X)]
    [hSC : PreservesFiniteColimits (sections l X)] :
    (ProEtale.NativeEncoding.derivedEncoding l X).inv ⋙
        (sections l X).mapDerivedCategory ≅
      sectionD X (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X) ⋙
        pbcDerivedExtend (nativeSectionIso X l).hom := by
  let A := ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X
  let d := nativeSectionIso X l
  let R₀ := WeilConjectures.restrictionEquivalence ((adicLisseForget X).mapIso d)
  letI : R₀.functor.Additive := pbcRestrict_additive d.hom
  letI : R₀.inverse.Additive := pbcRestrict_additive d.inv
  let R := R₀.mapDerivedCategory
  let N := (ProEtale.NativeEncoding.derivedEncoding l X).asEquivalence
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) A
  let e : ProEtale.NativeEncoding.encoding l X ⋙ E.functor ≅
      sections l X ⋙ R₀.functor := by
    unfold ProEtale.NativeEncoding.encoding sections
    exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ProEtale.AdicSheaf.forgetAb l X)
        (ProEtale.CondensedRing.sectionModuleComapIso X
          (ProEtale.NativeEncoding.coefficientIso l X).hom) ≪≫
      (Functor.associator _ _ _).symm
  have hRA : R₀.functor.Additive := pbcRestrict_additive d.hom
  have hRL : PreservesFiniteLimits R₀.functor := pbcRestrict_limits d.hom
  have hRC : PreservesFiniteColimits R₀.functor := pbcRestrict_colimits d.hom
  letI := hRL
  letI := hRC
  have hGL : PreservesFiniteLimits (sections l X ⋙ R₀.functor) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ (sections l X) R₀.functor hSL hRL
  have hGC : PreservesFiniteColimits (sections l X ⋙ R₀.functor) :=
    @comp_preservesFiniteColimits _ _ _ _ _ _ (sections l X) R₀.functor hSC hRC
  letI := hGL
  have hGA : (sections l X ⋙ R₀.functor).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hFL : PreservesFiniteLimits (ProEtale.NativeEncoding.encoding l X ⋙ E.functor) :=
    inferInstance
  have hFC : PreservesFiniteColimits (ProEtale.NativeEncoding.encoding l X ⋙ E.functor) :=
    inferInstance
  letI := hFL
  have hFA : (ProEtale.NativeEncoding.encoding l X ⋙ E.functor).Additive :=
    Functor.additive_of_preserves_binary_products _
  let z : N.functor ⋙ sectionD X A ≅ (sections l X).mapDerivedCategory ⋙ R.functor :=
    Functor.mapDerivedCategoryCompIso (ProEtale.NativeEncoding.encoding l X)
      E.functor ≪≫
      @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
        hFA hGA hFL hFC hGL hGC e ≪≫
      (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _
        (sections l X) inferInstance inferInstance inferInstance R₀.functor hRA hRL hRC).symm
  let z' : (sections l X).mapDerivedCategory ≅
      N.functor ⋙ (sectionD X A ⋙ R.inverse) :=
    (Iso.compInverseIso (H := R) z).symm ≪≫ Functor.associator _ _ _
  exact Iso.inverseCompIso (G := N) z' ≪≫
    Functor.isoWhiskerLeft (sectionD X A) (extendIsoRestrict X d).symm

set_option backward.isDefEq.respectTransparency false in
private def finiteSectionIso
    [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (A : AdicFiniteRealization.Core l X) (B : AdicFiniteRealization.ScalarData l X A)
    (R : AdicFiniteRealization.ClosureData l X A B)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology X) (ProEtale.padicSubfieldRingObj X l E) ≅
      rationalCoefficientSheaf l X (Coefficient.{u} l (PadicAlgCl l) E) :=
  R.finiteIso E

set_option backward.isDefEq.respectTransparency false in
private theorem finite_native_coefficient
    [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (A : AdicFiniteRealization.Core l X) (B : AdicFiniteRealization.ScalarData l X A)
    (R : AdicFiniteRealization.ClosureData l X A B)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)) :
    (finiteSectionIso X l A B R E).hom ≫ C.rationalInclusion =
      ProEtale.CondensedRing.sectionRingMap X
        (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E) ≫ (nativeSectionIso X l).hom := by
  apply Sheaf.hom_ext
  ext U a
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (C.rationalInclusion.hom.app U ((finiteSectionIso X l A B R E).hom.hom.app U a)).down.1 x =
    (((ProEtale.padicSubfieldRingObjToPadicAlgCl X l E ≫
      (ProEtale.NativeEncoding.coefficientIso l X).hom).hom.app U) a).down.1 x
  erw [C.rationalInclusion_normalized]
  change E.val.val ((Shrink.algEquiv (Padic l) E.val)
    (rationalCoefficientValue l (Coefficient.{u} l (PadicAlgCl l) E) X U
      ((finiteSectionIso X l A B R E).hom.hom.app U a) x)) = _
  dsimp only [finiteSectionIso]
  erw [R.finite_normalization]
  have hc : ProEtale.padicSubfieldRingObjToPadicAlgCl X l E ≫
      (ProEtale.NativeEncoding.coefficientIso l X).hom =
      ProEtale.chartComparison X E ≫
        (ProEtale.padicAlgClSheafCocone X l).ι.app E ≫
          ProEtale.padicAlgClSheafToAdicConstantSheaf X l := by
    change (ProEtale.upperStarFromPoint X).map
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
      ((ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
        ProEtale.padicAlgClSheafToAdicConstantSheaf X l) = _
    rw [← Category.assoc, ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso_fac,
      ProEtale.NativeEncoding.finiteComparison_eq_chart]
    exact Category.assoc _ _ _
  rw [hc]
  exact (ProEtale.NativeEncoding.finiteLeg_native l X E U
    ((ProEtale.chartComparison X E).hom.app U a) x).symm

end SectionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

/-- A constructible complex over a finite condensed coefficient field has an integral
model whose tensor extension is its native section-module presentation.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Lemma 6.8.13 and Lemma 6.8.2.
(blueprint: lem-sf-condensed-finite-integral-tensor-model).

Proof in words: use the canonical size transport on the given finite subextension E of
PadicAlgCl; this is the same index E, with coefficient type Shrink E. Internal-module and
section-module equivalences, together with the continuous-field local-freeness theorem,
identify its bounded constructible category with the continuous rational coefficient
category. Apply finite-field continuous rational derived realization, which is essentially
surjective by the integral-lattice construction and finite Postnikov induction of
Proposition 6.8.14(2). The raw rationalization has unchanged objects, so its preimage is an
actual integral constructible complex L. The integral identity comparison transports L to
sfIntegralConstructibleCategory. Its integral tensor formula and the normalized coefficient
presentation identify its extension with the finite condensed realization. Compose with
flat extension to PadicAlgCl. The balanced tensor associator identifies that composite with
extension along C.integralMap: the associator sends b tensor (a tensor m) to ba tensor m.
Finite residue maps determine the integral coefficient map by the inverse-limit property;
the pointwise normalization determines its rational inclusion. Hence these are the given
maps of C, rather than arbitrarily chosen ring identifications.
The specified coefficient isomorphism in NativeEncoding and
the exact section-module equivalence identify the other side with the displayed inverse
encoding followed by sections. Thus the tensor associator gives the asserted isomorphism.
This uses a finite-field model as input; descent of an arbitrary algebraic-closure object
is separate. Zero complexes and the empty scheme use zero integral representatives.
-/
theorem condensedFinite_integralTensor_model
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [IsCommMonObj (abRing l X)] [(sections l X).Additive]
    [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E))
    (K : ProEtale.PadicSubfieldConstructible X l E) :
    ∃ L : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X,
      Nonempty ((pbcDerivedExtend (C.integralMap l X)).obj L.obj ≅
        (sections l X).mapDerivedCategory.obj
          ((ProEtale.NativeEncoding.derivedEncoding l X).inv.obj
            ((ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj K.obj))) := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  letI : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{u} :=
    { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1,
      cardinality_eq := (pow_one p).symm, k₀ := ULift.{u} (ZMod p),
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ULift.{u} (ZMod p)) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  obtain ⟨A⟩ := AdicFiniteRealization.core_exists D l hl X
  obtain ⟨B, _⟩ := AdicFiniteRealization.adic_finite_scalar_coherence l X A
  obtain ⟨R, _, _, hFS, _⟩ :=
    AdicFiniteRealization.adic_finite_constructibility_comparison l X A B
  let T := sectionD X (ProEtale.padicSubfieldRingObj X l E)
  let ρ := finiteSectionIso X l A B R E
  let M := (pbcDerivedExtend ρ.hom).obj (T.obj K.obj)
  have hM : AdicFiniteRealization.finiteFreeTarget X
      (rationalCoefficientSheaf l X (Coefficient.{u} l (PadicAlgCl l) E)) M := by
    have h := (hFS E K.obj).mp K.property
    unfold AdicFiniteRealization.sectionDerived at h
    exact h
  obtain ⟨L, ⟨eL⟩⟩ := integral_tensor_image l X
    (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E) C M hM
  let a := ProEtale.padicSubfieldRingObjToPadicAlgCl X l E
  let d := nativeSectionIso X l
  let φ := ProEtale.CondensedRing.sectionRingMap X a
  let ψ := φ ≫ d.hom
  obtain ⟨adj⟩ := (ProEtale.condensedAlgClCoefficientCalculus X l E).2.2.2.2.2.2.1
  let e₁ : (pbcDerivedExtend C.rationalInclusion).obj M ≅
      (pbcDerivedExtend ψ).obj (T.obj K.obj) :=
    pbcReductionNormalization ρ.hom C.rationalInclusion ψ
      (finite_native_coefficient X l A B R E C) (T.obj K.obj)
  let e₂ : (sections l X).mapDerivedCategory.obj
        ((ProEtale.NativeEncoding.derivedEncoding l X).inv.obj
          ((ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj K.obj)) ≅
      (pbcDerivedExtend ψ).obj (T.obj K.obj) :=
    (native_inverse_sections X l).app
        ((ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj K.obj) ≪≫
      (pbcDerivedExtend d.hom).mapIso ((section_tensor X a
        (ProEtale.derivedExtendScalarsToPadicAlgCl X l E) adj).app K.obj) ≪≫
      pbcReductionNormalization φ d.hom ψ rfl (T.obj K.obj)
  exact ⟨L, ⟨eL ≪≫ e₁ ≪≫ e₂.symm⟩⟩

end WeilConjectures.LocallyFiniteAdicRealization
