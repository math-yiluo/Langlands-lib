/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
public import WeilConjectures.SixFunctors.AdicFiniteRealization.LocallyFiniteAdicFiniteCondensedRealization

/-! # Section comparisons for integral condensed realizations

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: def-sf-condensed-integral-section-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

/-- The two sides of a tensor square agree, allowing the prescribed target transport.
Source: tensor-comparison naturality, BS 6.8.14(2).
(blueprint: def-sf-condensed-integral-section-comparisons). -/
def integralTensorSquare {C : Type*} [Category C] {X Y M N N' : C}
    (f : X ⟶ Y) (p : X ≅ M) (q : Y ≅ N) (t : M ⟶ N') : Prop :=
  HEq (f ≫ q.hom) (p.hom ≫ t)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- Section reconstruction is an exact equivalence, before imposing constructibility.
Source: the exact section-module equivalence, BS 6.8.2.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
theorem sectionDerived_isEquivalence
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (sectionDerived X R).IsEquivalence := by
  unfold sectionDerived
  infer_instance

/-- The fixed section functor for condensed algebraic-closure coefficients.
Source: exact section reconstruction, BS 6.8.2.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
@[irreducible] def integralSections :=
  sectionDerived X (ProEtale.padicAlgClRingObj X l)

/-- The fixed section functor is an equivalence.
Source: exact section reconstruction, BS 6.8.2.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
theorem integralSections_isEquivalence : (integralSections l X).IsEquivalence := by
  unfold integralSections
  exact sectionDerived_isEquivalence X _

/-- Forgetting native scalars and reconstructing sections commute with restriction
along the actual condensed-to-native coefficient map.
Source: section reconstruction and exact derived transport, BS 6.8.2.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
@[irreducible] def nativeCondensedSectionComparison [IsCommMonObj (abRing l X)]
    [(sections l X).Additive] [PreservesFiniteLimits (sections l X)]
    [PreservesFiniteColimits (sections l X)] :
    nativeCondensedDerived l X ⋙ integralSections l X ≅
      (sections l X).mapDerivedCategory ⋙
        pbcDerivedRestrict (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)) := by
  let S := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (ProEtale.padicAlgClRingObj X l)).functor
  letI : S.Additive := Functor.additive_of_preserves_binary_products S
  let k : nativeCondensedModules l X ⋙ S ≅ sections l X ⋙
      pbcRestrict (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)) :=
    Functor.isoWhiskerLeft (ProEtale.AdicSheaf.forgetAb l X)
      (ProEtale.CondensedRing.sectionModuleComapIso X (condensedNativeMap l X))
  unfold nativeCondensedDerived integralSections sectionDerived
  exact Functor.mapDerivedCategoryCompIso (nativeCondensedModules l X) S ≪≫
    Functor.mapDerivedCategoryNatIso k ≪≫
    (Functor.mapDerivedCategoryCompIso (sections l X) _).symm

/-- The section ring map of an invertible internal coefficient map is invertible.
Source: functoriality on the literal section rings.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
theorem sectionRingMap_isIso
    {R S : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] [IsIso f] :
    IsIso (ProEtale.CondensedRing.sectionRingMap X f) := by
  let g := ProEtale.CondensedRing.sectionRingMap X (inv f)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change (inv f).hom.app U (f.hom.app U r) = r
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun z : R ⟶ R ↦ z.hom)
      (IsIso.hom_inv_id f)) U) r
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change f.hom.app U ((inv f).hom.app U r) = r
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun z : S ⟶ S ↦ z.hom)
      (IsIso.inv_hom_id f)) U) r

/-- The section comparison for extension from a finite field to the condensed closure
is the mate of the identity-on-sections scalar restriction comparison.
Source: the scalar adjunction under coefficient equivalences, BS 6.8.2.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
@[irreducible] def closureSectionScalarComparison
    (E : Index l (PadicAlgCl l)) :
    ProEtale.derivedExtendScalarsToPadicAlgCl X l E ⋙
        integralSections l X ≅
      sectionDerived X (ProEtale.padicSubfieldRingObj X l E) ⋙
        pbcDerivedExtend (ProEtale.CondensedRing.sectionRingMap X
          (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)) := by
  unfold integralSections sectionDerived
  letI hcommE : IsCommMonObj (ProEtale.padicSubfieldRingObj X l E) :=
    ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) X
  letI hcommC : IsCommMonObj (ProEtale.padicAlgClRingObj X l) := inferInstance
  let φ := ProEtale.padicSubfieldRingObjToPadicAlgCl X l E
  let eE := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (ProEtale.padicSubfieldRingObj X l E)
  let eC := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (ProEtale.padicAlgClRingObj X l)
  letI := Functor.additive_of_preserves_binary_products eE.functor
  letI := Functor.additive_of_preserves_binary_products eC.functor
  let k := Functor.mapDerivedCategoryCompIso (Mod.comap φ) eE.functor ≪≫
    Functor.mapDerivedCategoryNatIso (ProEtale.CondensedRing.sectionModuleComapIso X φ) ≪≫
    (Functor.mapDerivedCategoryCompIso eC.functor
      (pbcRestrict (ProEtale.CondensedRing.sectionRingMap X φ))).symm
  let a : ProEtale.derivedExtendScalarsToPadicAlgCl X l E ⊣
      (Mod.comap φ).mapDerivedCategory := by
    exact @Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (ProEtale.padicSubfieldRingObj X l E) (ProEtale.padicAlgClRingObj X l)
      _ _ hcommE hcommC φ _
  exact (scalarAdjunctionCoefficientEquivalence a
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap X φ))
    eE.functor.mapDerivedCategory eC.functor.mapDerivedCategory k).choose

/-- Restriction through two coefficient isomorphisms transports a scalar tensor square.
All comparisons are the mates of the fixed restriction square.
Source: adjunction uniqueness for extension and restriction of scalars.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
@[irreducible] def tensorThroughCoefficientSquare
    {R P V T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (d : R ≅ P) (q : V ≅ T) (s : R ⟶ V) (c : P ⟶ T)
    (h : d.hom ≫ c = s ≫ q.hom) :
    pbcDerivedExtend c ⋙ pbcDerivedRestrict q.hom ≅
      pbcDerivedRestrict d.hom ⋙ pbcDerivedExtend s := by
  letI := derivedRestrictIso_isEquivalence d
  letI := derivedRestrictIso_isEquivalence q
  letI := (pbcDerivedScalarAdjunction d.hom).isEquivalence_left_of_isEquivalence_right
  letI := (pbcDerivedScalarAdjunction q.hom).isEquivalence_left_of_isEquivalence_right
  let ed := (pbcDerivedScalarAdjunction d.hom).toEquivalence
  let eq := (pbcDerivedScalarAdjunction q.hom).toEquivalence
  let a : pbcDerivedExtend c ≅
      (pbcDerivedRestrict d.hom ⋙ pbcDerivedExtend s) ⋙ pbcDerivedExtend q.hom :=
    (ed.invFunIdAssoc (pbcDerivedExtend c)).symm ≪≫
      Functor.isoWhiskerLeft (pbcDerivedRestrict d.hom)
        (coefficientExtensionSquare X d.hom c s q.hom h)
  exact Iso.compInverseIso (H := eq) a

/-- The raw completed coefficient transport is restriction by its CommRing lift.
Source: the specified integral coefficient transport, BS 6.8.2.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
theorem integralDetailedTransport_eq
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    integralDetailedTransport X l E = pbcDerivedRestrict (purCoefficientIso l E X).hom := by
  have h := congrArg Iso.hom (purCoefficientIso_existsUnique l E X).exists.choose_spec
  unfold integralDetailedTransport pbcDerivedRestrict
  simp only [← h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual stage transition has the specified underlying integral object.
Source: the raw localization and the published stage-transition object equation.
(blueprint: def-sf-condensed-integral-section-comparisons). -/
theorem finiteCondensedStageIntegralObject
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj =
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        E L h).obj K := by
  rw [(GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l
    (PadicAlgCl l) X).exists.choose_spec.1 E L h]
  exact congrArg ScalarLocalization.obj
    (sfRationalScalarExtension_obj l (Coefficient.{u} l (PadicAlgCl l) E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l (PadicAlgCl l) L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h)
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The finite condensed closure realization, reconstructed as ordinary section modules,
is the original continuous realization followed by its specified closure leg.
Source: the section encoding counit and scalar adjunction, BS 6.8.14(2).
(blueprint: def-sf-condensed-integral-section-comparisons). -/
@[irreducible] def finiteCondensedClosureSectionComparison (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    finiteCondensedClosureFunctor l X A E ⋙
        integralSections l X ≅
      finiteFunctor l X A.toCore E ⋙ pbcDerivedExtend (A.closure.leg E) := by
  let S := sectionDerived X (ProEtale.padicSubfieldRingObj X l E)
  let F := finiteCondensedFunctor l X A E ⋙
    (ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj X l E)).ι
  let t := ProEtale.CondensedRing.sectionRingMap X
    (ProEtale.padicSubfieldRingObjToPadicAlgCl X l E)
  let m : pbcDerivedExtend t ≅
      pbcDerivedExtend (A.closure.finiteIso E).hom ⋙ pbcDerivedExtend (A.closure.leg E) :=
    (Adjunction.leftAdjointCompIso
      (pbcDerivedScalarAdjunction (A.closure.finiteIso E).hom)
      (pbcDerivedScalarAdjunction (A.closure.leg E)) (pbcDerivedScalarAdjunction t)
      (pbcDerivedRestrictComp _ _ t (A.closure.leg_normalization E))).symm
  exact Functor.isoWhiskerLeft F (closureSectionScalarComparison l X E) ≪≫
    Functor.isoWhiskerLeft (F ⋙ S) m ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F (eqToIso (finiteCondensedEncoding_functor l X A E)).symm)
      (pbcDerivedExtend (A.closure.leg E)) ≪≫
    Functor.isoWhiskerRight (finiteCondensedComparison l X A E)
      (pbcDerivedExtend (A.closure.leg E))

/-- On integral arrows the continuous realization is its literal tensor formula.
The components are the specified object equalities, rather than new choices of isomorphisms.
Source: the integral numerator formula for continuous realization, BS 6.8.14(2).
(blueprint: def-sf-condensed-integral-section-comparisons). -/
@[irreducible] def continuousIntegralComparison (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    pbcStageLocalization l (PadicAlgCl l) X E ⋙ (A.realization E).J ≅
      pbcStageInclusion l (PadicAlgCl l) X E ⋙
        pbcDerivedExtend ((A.realization E).integralIso.hom ≫ (A.realization E).inclusion) := by
  refine NatIso.ofComponents (fun K ↦ eqToIso ((A.realization E).objects K)) ?_
  intro K L f
  have h := (A.realization E).fractions K L f 0
  simp only [pow_zero, inv_one, map_one, one_smul] at h
  change (A.realization E).J.map ((pbcStageLocalization l (PadicAlgCl l) X E).map f) ≫
    eqToHom ((A.realization E).objects L) =
      eqToHom ((A.realization E).objects K) ≫ _
  rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Functor.comp_map]
  rfl

end WeilConjectures.LocallyFiniteAdicRealization
