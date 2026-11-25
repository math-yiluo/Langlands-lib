/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateData

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRestrictionCube
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarMateComposition
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Tactic.DefEqTransformations

/-! # Presentation of the native proper scalar mate

Source: Bhatt--Scholze, Lemma 6.8.2; the formal-properties paragraph of the
current blueprint scalar direct-image proof.
(blueprint: lem-sf-native-proper-scalar-mate-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.PurCompactSupport.properComparison
  AlgebraicGeometry.Scheme.reductionDerivedChange
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Mod.extendScalars CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  WeilConjectures.LocallyFiniteAdicCompactSupport.nativeScalarCondensedComposite

attribute [local implicit_reducible] WeilConjectures.SemilinearSections.moduleAbelian

namespace CategoryTheory
open TwoSquare

private theorem inverseMateIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {E : A ⥤ C} {H : B ⥤ D} [E.IsEquivalence] [H.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (k : R ⋙ E ≅ H ⋙ R') :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ k.hom))) := by
  let s := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ k.hom))
  let ko : TwoSquare H.op R.op R'.op E.op := TwoSquare.mk _ _ _ _ (NatTrans.op k.hom)
  have hi := isIso_mateEquiv_of_isEquivalence a.op b.op ko
  have he : NatTrans.op s = (mateEquiv a.op b.op ko) := by
    ext X
    simp [s, ko, mateEquiv]
  have : IsIso (NatTrans.op s) := by rw [he]; exact hi
  have (X : A) : IsIso (s.app X) := by
    have : IsIso ((s.app X).op) := NatIso.isIso_app_of_isIso (NatTrans.op s) _
    exact isIso_of_op (s.app X)
  exact NatIso.isIso_of_isIso_app s

/-- Inverse mates carry a commuting cube of restriction comparisons to a commuting
cube of scalar-extension arrows. No scalar mate is assumed invertible. -/
private theorem scalarMateArrowTransport
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L : A ⥤ B} {R : B ⥤ A} {K : C ⥤ D} {S : D ⥤ C}
    {L' : A' ⥤ B'} {R' : B' ⥤ A'} {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (a : L ⊣ R) (b : K ⊣ S) (a' : L' ⊣ R') (b' : K' ⊣ S')
    (E : A ≌ A') (F : C ≌ C') (H : B ≌ B') (J : D ≌ D')
    (k : R ⋙ E.functor ≅ H.functor ⋙ R')
    (n : S ⋙ F.functor ≅ J.functor ⋙ S')
    {G : A ⥤ C} {Q : B ⥤ D} {G' : A' ⥤ C'} {Q' : B' ⥤ D'}
    (x : G ⋙ F.functor ≅ E.functor ⋙ G')
    (y : Q ⋙ J.functor ≅ H.functor ⋙ Q')
    (v : TwoSquare R Q G S) (v' : TwoSquare R' Q' G' S')
    (hc : ((v ≫ᵥ TwoSquare.mk _ _ _ _ n.hom).whiskerLeft y.hom) =
      ((TwoSquare.mk _ _ _ _ k.hom ≫ᵥ v').whiskerRight x.hom))
    (M : A) :
    Nonempty (Arrow.mk (((mateEquiv a b).symm v).app M) ≅
      Arrow.mk (J.inverse.map (((mateEquiv a' b').symm v').app (E.functor.obj M)))) := by
  let s := (mateEquiv a a').symm (TwoSquare.mk _ _ _ _ k.hom)
  let t := (mateEquiv b b').symm (TwoSquare.mk _ _ _ _ n.hom)
  let w := (mateEquiv a b).symm v
  let w' := (mateEquiv a' b').symm v'
  have : IsIso s := inverseMateIso a a' k
  have : IsIso t := inverseMateIso b b' n
  let si := asIso s
  let ti := asIso t
  have he : ((w ≫ₕ t).whiskerBottom y.hom) =
      ((s ≫ₕ w').whiskerTop x.hom) := by
    apply (mateEquiv a b').injective
    have ht : (mateEquiv a b') ((s ≫ₕ w').whiskerTop x.hom) =
        ((mateEquiv a b') (s ≫ₕ w')).whiskerRight x.hom := by
      simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
        (mateEquiv_whiskerTop_whiskerBottom a b' (s ≫ₕ w') x.hom (𝟙 _))
    rw [mateEquiv_whiskerBottom, ht]
    dsimp only [s, t, w, w']
    rw [mateEquiv_vcomp a b b', mateEquiv_vcomp a a' b']
    simpa only [Equiv.apply_symm_apply] using hc
  have hM := congrArg (fun z ↦ z.app M) he
  have hM' : ti.hom.app (G.obj M) ≫ J.functor.map (w.app M) ≫
        y.hom.app (L.obj M) =
      K'.map (x.hom.app M) ≫ w'.app (E.functor.obj M) ≫ Q'.map (si.hom.app M) := by
    simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      si, ti, asIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.comp_obj, Category.assoc] using hM
  have hcancel : Q'.map (si.hom.app M) ≫ Q'.map (si.inv.app M) = 𝟙 _ :=
    (Q'.mapIso (si.app M)).hom_inv_id
  let i : Arrow.mk (J.functor.map (w.app M)) ≅
      Arrow.mk (w'.app (E.functor.obj M)) :=
    Arrow.isoMk
      ((ti.app (G.obj M)).symm ≪≫ K'.mapIso (x.app M))
      (y.app (L.obj M) ≪≫ Q'.mapIso ((si.app M).symm)) (by
        apply (cancel_epi (ti.hom.app (G.obj M))).mp
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
          Arrow.mk_hom, Category.assoc]
        rw [Iso.hom_inv_id_app_assoc, reassoc_of% hM']
        rw [hcancel]
        simpa only [Functor.comp_obj, Category.assoc] using
          (Category.comp_id
            (K'.map (x.hom.app M) ≫ w'.app (E.functor.obj M))).symm)
  exact ⟨(Functor.mapArrowEquivalence J).unitIso.app (Arrow.mk (w.app M)) ≪≫
    J.inverse.mapArrow.mapIso i⟩

end CategoryTheory

namespace CategoryTheory.Equivalence

private theorem derivedFunctorProjection
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive] :
    E.mapDerivedCategory.functor = E.functor.mapDerivedCategory := rfl

private theorem derivedInverseProjection
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive] :
    E.mapDerivedCategory.inverse = E.inverse.mapDerivedCategory := rfl

end CategoryTheory.Equivalence

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale

attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight
  nativeScalarIntegralExact

attribute [local irreducible] NativeScalarRingModel.integralEquivalence
  NativeScalarRingModel.closureEquivalence

attribute [local implicit_reducible] sheafBraidedCategory sheafSymmetricCategory
attribute [local irreducible] nativeScalarDerivedCompositeAdjunction
attribute [local irreducible] CondensedRing.lowerStar CondensedRing.derivedPushHom
  CondensedRing.derivedComapLowerStarIso nativeScalarCompositeRestrictionSquare
attribute [local implicit_reducible] CondensedRing.moduleObjectDerivedPushforward
  nativeScalarIntegralDerived nativeScalarClosureDerived
  nativeScalarCompositeRestriction

private def scalarCompositeAdjunction (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :=
  @nativeScalarDerivedCompositeAdjunction.{u}
    (Profinite.padicIntegersRingObj l E.1) (Profinite.continuousMapRingObj E.1)
    (Profinite.padicAlgClRingObj l)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (padicIntegersRingObjToContinuousMapRingObj l E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) inferInstance inferInstance T

attribute [local irreducible] scalarCompositeAdjunction

attribute [local irreducible] mateEquiv TwoSquare.hComp Adjunction.comp

private theorem scalarCompositeMate (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {U V : Scheme.{u}} (g : U ⟶ V)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) U))) :
    (((mateEquiv (scalarCompositeAdjunction l E U) (scalarCompositeAdjunction l E V)).symm
      (nativeScalarCompositeRestrictionSquare l E g)).app M) =
        nativeScalarCondensedComposite l E g M := by
  have h := @nativeScalarDerivedCompositeMate.{u}
    (Profinite.padicIntegersRingObj l E.1) (Profinite.continuousMapRingObj E.1)
    (Profinite.padicAlgClRingObj l)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (padicIntegersRingObjToContinuousMapRingObj l E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
    inferInstance inferInstance inferInstance inferInstance U V g M
  -- Expose the inferred equation before delta-reducing the named wrappers.
  whnf at h ⊢
  delta scalarCompositeAdjunction nativeScalarCompositeRestrictionSquare
    nativeScalarDerivedRestrictionSquare nativeScalarCondensedComposite
    CondensedRing.localizedDirectImageComparison nativeScalarIntegralDerived
    nativeScalarClosureDerived CondensedRing.moduleObjectDerivedPushforward
    padicIntegersToPadicSubfield coefficientMap inferInstance at h ⊢
  exact h

attribute [local implicit_reducible] pbcDerivedRestrict Equivalence.mapDerivedCategory

attribute [local irreducible] nativeRingRestrictionSquare

private theorem nativeMateProjection
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (M : DerivedCategory (pbcModules U (R.ring U))) :
    (((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
        (pbcDerivedScalarAdjunction (a.map V))).symm
      (nativeRingRestrictionSquare a g)).app M) =
        (PurCompactSupport.properComparison a g).app M := by
  delta nativeRingRestrictionSquare PurCompactSupport.properComparison
    pbcDerivedRestrict pbcRestrict
  rfl

private theorem scalarPresentationOfModel
    (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    (P : NativeScalarRingModel l E a) {U V : Scheme.{u}} (g : U ⟶ V)
    (M : DerivedCategory (pbcModules U (R.ring U))) :
    Nonempty (Arrow.mk ((PurCompactSupport.properComparison a g).app M) ≅
      Arrow.mk ((P.closureEquivalence V).inverse.mapDerivedCategory.map
        (nativeScalarCondensedComposite l E g
          ((P.integralEquivalence U).functor.mapDerivedCategory.obj M)))) := by
  have hCube := @nativeScalarRestrictionCube.{u} l inferInstance E R S a P
  obtain ⟨k, hk⟩ := hCube
  obtain ⟨x, y, hxy⟩ := hk g
  have h := CategoryTheory.scalarMateArrowTransport
    (pbcDerivedScalarAdjunction (a.map U)) (pbcDerivedScalarAdjunction (a.map V))
    (scalarCompositeAdjunction l E U) (scalarCompositeAdjunction l E V)
    (P.integralEquivalence U).mapDerivedCategory (P.integralEquivalence V).mapDerivedCategory
    (P.closureEquivalence U).mapDerivedCategory (P.closureEquivalence V).mapDerivedCategory
    (k U) (k V) x y (nativeRingRestrictionSquare a g)
    (nativeScalarCompositeRestrictionSquare l E g) hxy M
  simp only [Equivalence.derivedFunctorProjection,
    Equivalence.derivedInverseProjection] at h
  simp only [scalarCompositeMate, nativeMateProjection] at h ⊢
  whnf at h ⊢
  delta pbcModules proEtaleRingModules adicLisseForget
    WeilConjectures.SemilinearSections.moduleAbelian at h ⊢
  exact h

/-- Completion, internal/section transport, and scalar transitivity identify the
native scalar mate with the successive integral-to-field and field-to-closure mates.
This is a comparison of arrows for arbitrary morphisms and arbitrary complexes.
Neither properness nor boundedness, nor invertibility of either mate, is assumed.

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; the formal-properties
paragraph of the current blueprint scalar direct-image proof; the presentation/pasting step of
lem-sf-native-proper-scalar-mate-bounded-below-restricted.
(blueprint: lem-sf-native-proper-scalar-mate-presentation).

Proof in words:
1. Use the normalized continuous integral coefficient realization and the inverse
limit of finite quotient projections to identify the completed ring for the size
model Coefficient E with the section ring of the pulled condensed integers of E.
The algebra equivalence Shrink.algEquiv is bicontinuous by finite dimensionality
over the complete base field. Uniqueness of the extending absolute value identifies
the integer rings and their finite quotients, compatibly with the fixed embedding.
Transporting modules along this ring isomorphism and applying the
internal/section equivalence gives e. These additive equivalences are exact.
2. The normalized locally finite coefficient-ring realization identifies the pulled
condensed algebraic-closure ring with the native ring. The internal/section module
equivalence followed by this ring isomorphism gives d, again additive and exact.
3. The completion identification, integral localization inclusion, and finite-field
inclusion compose to a.map: the finite quotient projections give the integral
normalization, the localization fixes the integral inclusion, and the finite-field
normalization fixes the rational inclusion. Thus ha applies to this presentation.
The normalized inverse-image maps agree as well: after taking adjoints they are
precomposition of functions. The direct-image comparisons therefore commute with
the coefficient identifications.
4. Construct these equivalences at every scheme. The restriction cube transports
inverse mates by mateEquiv_vcomp and its whiskering formulas. The two transverse
inverse mates are invertible because their horizontal functors are equivalences;
this follows from isIso_mateEquiv_of_isEquivalence applied to opposite adjunctions.
Their components give an isomorphism between the corresponding arrows after the
closure equivalence. Its inverse carries this arrow isomorphism back to native modules.
5. Use nativeScalarDerivedCompositeMate, proved from mateEquiv_hcomp: the inverse
mate of the pasted condensed restriction square is closure extension applied to
the integral mate, followed by the closure mate at the integrally extended object.
The integral mate is localizedDirectImageComparison by definition. The native
inverse mate is properComparison by definition. Substitution into the preceding
arrow isomorphism gives the asserted conclusion. All constructions use ordinary
ambient derived categories. Neither geometric scalar mate is inverted. The argument
applies to empty schemes, identity morphisms and zero complexes. -/
theorem native_proper_scalar_mate_presentation
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ∃ (e : pbcModules U ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).ring U) ≌
        Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj l E.1) U))
      (d : Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj l) V) ≌
        pbcModules V ((nativeCoefficients l).ring V))
      (he : e.functor.Additive) (hd : d.functor.Additive),
      letI := he
      letI := hd
      ∀ M : DerivedCategory (pbcModules U ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).ring U)),
        Nonempty (Arrow.mk ((PurCompactSupport.properComparison a g).app M) ≅
          Arrow.mk (d.functor.mapDerivedCategory.map
            (nativeScalarCondensedComposite l E g
              (e.functor.mapDerivedCategory.obj M)))) := by
  obtain ⟨P⟩ := exists_nativeScalarRingModel l E a ha
  have he := NativeScalarRingModel.integralEquivalence_additive P U
  have hd : (P.closureEquivalence V).inverse.Additive := by
    let := NativeScalarRingModel.closureEquivalence_additive P V
    exact Equivalence.inverse_additive _
  refine ⟨P.integralEquivalence U, (P.closureEquivalence V).symm, he, hd, ?_⟩
  intro M
  exact scalarPresentationOfModel l E a P g M

end WeilConjectures.LocallyFiniteAdicCompactSupport
