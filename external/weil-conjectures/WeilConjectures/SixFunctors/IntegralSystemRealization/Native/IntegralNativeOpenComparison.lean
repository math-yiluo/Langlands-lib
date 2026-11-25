/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeDirectComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativePullEvaluation
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # Normalized comparison with the native system operation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  coefficientSequenceEvaluation_additiveInstance coefficientSequenceEvaluation_limits
  coefficientSequenceEvaluation_colimits sfIntrinsicPullback_additive
  sfIntrinsicPullback_preservesFiniteLimits sfIntrinsicPullback_preservesFiniteColimits
attribute [local irreducible] constantSheaf presheafToSheaf Functor.ofSequence
  Functor.ofOpSequence MorphismProperty.Over.pullback
attribute [local implicit_reducible] ProEtale.StrictTower.modulePullback
  ProEtale.StrictTower.moduleDirectImage

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

private theorem compareOpenMates
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R R' : B ⥤ A} {l l' : C ⥤ D} {r r' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (c : l ⊣ r) (d : l' ⊣ r')
    {E : A ⥤ C} {H : B ⥤ D}
    (e : R ≅ R') (q : r' ≅ r) (k : l' ≅ l)
    (δ : R ⋙ E ⟶ H ⋙ r) (δ' : R' ⋙ E ⟶ H ⋙ r')
    (v : L' ⋙ H ≅ E ⋙ l') (w : L ⋙ H ≅ E ⋙ l)
    (hv : (mateEquiv b d).symm δ' = v.inv)
    (hw : (mateEquiv a c).symm δ = w.inv)
    (hq : ∀ N, d.unit.app N ≫ q.hom.app (l'.obj N) ≫ r.map (k.hom.app N) =
      c.unit.app N)
    (hs : ∀ N, E.map (e.hom.app N) ≫ δ'.app N ≫ q.hom.app (H.obj N) = δ.app N)
    (M : A) :
    H.map (((a.ofNatIsoRight e).leftAdjointUniq b).hom.app M) ≫
      v.hom.app M ≫ k.hom.app (E.obj M) = w.hom.app M := by
  let α := (a.ofNatIsoRight e).leftAdjointUniq b
  have hα : a.unit.app M ≫ e.hom.app (L.obj M) =
      b.unit.app M ≫ R'.map (α.inv.app M) := by
    exact (b.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight e) M).symm
  have hq' : c.unit.app (E.obj M) ≫ r.map (k.inv.app (E.obj M)) =
      d.unit.app (E.obj M) ≫ q.hom.app (l'.obj (E.obj M)) := by
    rw [← hq (E.obj M)]
    simp only [Category.assoc, ← r.map_comp, Iso.hom_inv_id_app,
      r.map_id, Category.comp_id]
  have hv' := unit_mateEquiv_symm b d δ' M
  rw [hv] at hv'
  have hw' := unit_mateEquiv_symm a c δ M
  rw [hw] at hw'
  have hi : k.inv.app (E.obj M) ≫ v.inv.app M ≫ H.map (α.inv.app M) =
      w.inv.app M := by
    apply (c.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [hq']
    simp only [Category.assoc]
    have hn := q.hom.naturality (v.inv.app M)
    rw [← reassoc_of% hn, ← reassoc_of% hv']
    have hn' := δ'.naturality (α.inv.app M)
    dsimp only [Functor.comp_map] at hn'
    rw [← (q.hom.naturality (H.map (α.inv.app M))),
      ← reassoc_of% hn', ← E.map_comp_assoc, ← hα, E.map_comp_assoc,
      hs (L.obj M)]
    exact hw'
  have he : H.mapIso (α.app M) ≪≫ v.app M ≪≫ k.app (E.obj M) = w.app M :=
    Iso.ext_inv (by
      simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi)
  exact congrArg Iso.hom he

private theorem finiteOpen_unit (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (N : proEtaleRingModules U (proEtaleConstantRing U A)) :
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1} A) j).unit.app N ≫
      (openSquarePullbackModel A j).hom.app
        ((ProEtale.StrictTower.moduleJ (ULift.{u + 1} A) j).obj N) ≫
      (sfIntrinsicPullback A j).map ((compactSupportOpenModel j A).hom.app N) =
      (sfIntrinsicOpenAdjunction A j).unit.app N := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1} A) j)
      ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm) N
  have hn := (openSquarePullbackModel A j).hom.naturality
    ((compactSupportOpenModel j A).hom.app N)
  rw [← hn]
  rw [← Category.assoc]
  change (_ ≫ _ ) ≫ _ = _
  change (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1} A) j).unit.app N ≫
      (proEtaleConstantRingPullback A j).map ((compactSupportOpenModel j A).hom.app N) =
    (sfIntrinsicOpenAdjunction A j).unit.app N ≫
      (openSquarePullbackModel A j).inv.app ((sfIntrinsicExtensionByZero j A).obj N) at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

-- The actual localized unit, with the standard exact-functor factorizations.
private theorem localized_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {J : A ⥤ B} {P : B ⥤ A} [J.Additive] [P.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : J ⊣ P)
    (K : CochainComplex A ℤ) :
    (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        P.mapDerivedCategoryFactors.inv.app _ ≫
        P.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app K) := by
  unfold exactLocalizationDerivedAdjunction
  rw [Adjunction.localization_unit_app]
  rfl

-- Transport an ordinary unit equation to every derived object.
private theorem localized_unit_transport
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {J J' : A ⥤ B} {P P' : B ⥤ A}
    [J.Additive] [J'.Additive] [P.Additive] [P'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (a : J ⊣ P) (b : J' ⊣ P') (e : J ≅ J') (q : P ≅ P')
    (h : ∀ K, a.unit.app K ≫ q.hom.app (J.obj K) ≫ P'.map (e.hom.app K) =
      b.unit.app K) (K : DerivedCategory A) :
    (exactLocalizationDerivedAdjunction a).unit.app K ≫
      (Functor.mapDerivedCategoryNatIso q).hom.app (J.mapDerivedCategory.obj K) ≫
      P'.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso e).hom.app K) =
      (exactLocalizationDerivedAdjunction b).unit.app K := by
  suffices he : (exactLocalizationDerivedAdjunction a).unit ≫
      Functor.whiskerLeft J.mapDerivedCategory (Functor.mapDerivedCategoryNatIso q).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom P'.mapDerivedCategory =
      (exactLocalizationDerivedAdjunction b).unit from congr_app he K
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro L
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_mono (P'.mapDerivedCategory.map (J'.mapDerivedCategoryFactors.hom.app L) ≫
    P'.mapDerivedCategoryFactors.hom.app ((J'.mapHomologicalComplex (.up ℤ)).obj L))).1
  have hn := (Functor.mapDerivedCategoryNatIso q).hom.naturality
    (J.mapDerivedCategoryFactors.inv.app L)
  have he := Functor.mapDerivedCategoryNatIso_fac e L
  have hq := Functor.mapDerivedCategoryNatIso_fac q
    ((J.mapHomologicalComplex (.up ℤ)).obj L)
  have hp := P'.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app L)
  dsimp only [Functor.comp_map] at hn hp
  rw [localized_unit, localized_unit]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← P'.mapDerivedCategory.map_comp_assoc,
    ← P'.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← P'.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P'.mapDerivedCategory.map_id, Category.id_comp]
  rw [hp, reassoc_of% hq, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app L ≫
      (NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app
        ((J.mapHomologicalComplex (.up ℤ)).obj L) ≫
      (P'.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app L) =
      (b.mapHomologicalComplex (.up ℤ)).unit.app L := by
    ext i
    exact h (L.X i)
  rw [hc]
  rw [← P'.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P'.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]

private theorem derivedFiniteOpen_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ)
    (N : DerivedCategory (normalizedDVRModules l E U n)) :
    let := sfIntrinsicExtensionByZero_additive j
      (Padic.coefficientExtensionRing l E (n + 1))
    let := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.1
    let := (sfIntrinsicExtensionByZero_exact j
      (Padic.coefficientExtensionRing l E (n + 1))).2.2
    (ProEtale.VaryingRing.levelJAdj (compactSupportSystemLevel l E) j n).unit.app N ≫
      (Functor.mapDerivedCategoryNatIso
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) j)).hom.app
          ((ProEtale.StrictTower.moduleJ
            (compactSupportSystemLevel l E n) j).mapDerivedCategory.obj N) ≫
      (finiteDerivedPullback l E n j).map
        ((Functor.mapDerivedCategoryNatIso
          (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))).hom.app
            N) = (finiteOpenAdj l E j n).unit.app N := by
  let := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have h := localized_unit_transport
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1} A) j)
    (sfIntrinsicOpenAdjunction A j) (compactSupportOpenModel j A)
    (openSquarePullbackModel A j) (finiteOpen_unit A j) N
  have he := ProEtale.SemilinearProperOpen.Normalization.exact_adjunction_eq
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1} A) j)
  rw [← he] at h
  exact h

/-- The native open comparison is fixed by uniqueness of the left adjoint to pull.
Source: Stacks 03DI, 0941
(blueprint: lem-sf-integral-native-open-comparison). -/
def integralNativeOpenIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (a : Open l E j) :
    a.derived ≅ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j :=
  (a.adj.ofNatIsoRight (integralNativePullIso l E j)).leftAdjointUniq
    (ProEtale.VaryingRing.jAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)

/-- Compare exact open extension on whole systems, with its prescribed finite evaluations.
Source: Stacks 03DI, 0941; blueprint fix-prop-coherence, coefficient comparisons
of adjunction units and counits
(blueprint: lem-sf-integral-native-open-comparison).

Proof: the ordinary sequence direct image and VaryingRing.push have identical sections
and scalar maps, by the constant-section normalization of their ring maps. The identity
on sections is therefore a natural isomorphism. Ordinary left-adjoint uniqueness gives
the corresponding inverse-image comparison. Localize this exact comparison to obtain
pull isomorphic to VaryingRing.G. Transport a.adj by this isomorphism and compare its
left adjoint with VaryingRing.J using VaryingRing.jAdj. This constructs the whole-system
isomorphism alpha. The ordinary evaluation/direct-image square is identity on sections;
transposing under the ordinary adjunctions identifies the inverse-image evaluation
square with pullbackTensorSequenceInverseEvaluation and the native moduleEvalG.
Exact localization, with the cochain normalization of pullbackTensorDerivedEvaluation,
retains this square. Transpose it under the open adjunctions. The transpose equation of
ea fixes ea.evaluation.inv, and native evalJ.inv is the inverse mate of evalG.hom.
The finite change of coordinates is compactSupportOpenModel, itself defined by the
same open-adjunction uniqueness. Thus mate naturality identifies the inverse of the
displayed equality; invert to obtain the equality. This construction is on entire
systems, so it retains horizontal maps and uses no faithfulness of derived evaluation.
For the empty open both extensions are zero; identity opens and zero inputs use the
same unit identities. The argument applies to arbitrary derived systems. -/
theorem integralNativeOpenComparison {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (a : Open l E j) (ea : OpenEvaluation l E a) :
    ∀ (M : System l E U) (n : ℕ),
      letI := sfIntrinsicExtensionByZero_additive j
        (Padic.coefficientExtensionRing l E (n + 1))
      letI := (sfIntrinsicExtensionByZero_exact j
        (Padic.coefficientExtensionRing l E (n + 1))).2.1
      letI := (sfIntrinsicExtensionByZero_exact j
        (Padic.coefficientExtensionRing l E (n + 1))).2.2
      (coefficientSequenceDerivedEvaluation l E X n).map
          ((integralNativeOpenIso l E j a).hom.app M) ≫
          (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j n ≪≫
            Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
              (compactSupportOpenModel j
                (Padic.coefficientExtensionRing l E (n + 1))))).hom.app M =
        (ea.evaluation n).hom.app M := by
  intro M n
  let := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  let := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) j
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) j
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) j
  have h := compareOpenMates
    (E := coefficientSequenceDerivedEvaluation l E U n)
    (H := coefficientSequenceDerivedEvaluation l E X n) a.adj
    (ProEtale.VaryingRing.jAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j) (finiteOpenAdj l E j n)
    (ProEtale.VaryingRing.levelJAdj (compactSupportSystemLevel l E) j n)
    (integralNativePullIso l E j)
    (Functor.mapDerivedCategoryNatIso
      (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) j))
    (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1))))
    (pullbackTensorDerivedEvaluation l E j n).hom
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n).hom
    (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n) (ea.evaluation n)
    rfl (ea.transpose n) (derivedFiniteOpen_unit l E j n)
    (integralNativePullEvaluation l E j n) M
  exact h

end WeilConjectures.IntegralSystemRealization
