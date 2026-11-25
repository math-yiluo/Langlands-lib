/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemDirectEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralSystemOpenEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralSystemOpenComparisons
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Section-normalized models for strict-system operations

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941, 03DI, 07A7;
blueprint fix-prop-coherence, strict-system realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] pullbackTensorSequenceDerived
attribute [local irreducible] ProEtale.SemilinearProperOpen.pushComp

private theorem sequenceRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f =
      ProEtale.SemilinearProperOpen.coefficientMap (scalarRings l E)
        (scalarTransitions l E) f := by
  apply (pullbackTensorSequenceRing_existsUnique l E f).unique
  · intro n U
    unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
    rfl
  · intro n U
    exact (ProEtale.SemilinearProperOpen.coefficientMap_existsUnique
      (scalarRings l E) (scalarTransitions l E) f).choose_spec.1 n U

private def ordinaryBridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f ≅
      ProEtale.SemilinearProperOpen.push (scalarRings l E) (scalarTransitions l E) f :=
  SheafOfModules.pushforwardCongr (by
    rw [sequenceRing_eq l E f]
    rfl)

private theorem direct_exists {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (Direct l E f) := by
  have : Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X) :=
    ProEtale.SemilinearProperOpen.systems_kInjective
    (scalarRings l E) (scalarTransitions l E) X
  obtain ⟨d⟩ := SheafOfModules.derivedImage_exists
    (pullbackTensorSequenceInverse l E f) (pullbackTensorSequenceDirect l E f)
    (pullbackTensorSequenceAdjunction l E f)
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q) d.inverse := ⟨d.inverseFactors⟩
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q) (pull l E f) :=
    ⟨(pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors⟩
  let e : d.inverse ≅ pull l E f := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    d.inverse (pull l E f) (Iso.refl _)
  refine ⟨⟨d, e, ?_⟩⟩
  intro P
  dsimp only [e, Localization.liftNatIso]
  simp only [Localization.liftNatTrans_app, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.assoc]
  change d.inverseFactors.hom.app P ≫
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.inv.app P ≫
        (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P = _
  rw [Iso.inv_hom_id_app, Category.comp_id]

private def ordinaryOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Open l E j :=
  { ordinary := ProEtale.SemilinearProperOpen.extension
      (scalarRings l E) (scalarTransitions l E) j
    additive := (ProEtale.SemilinearProperOpen.extension_exact
      (scalarRings l E) (scalarTransitions l E) j).1
    limits := (ProEtale.SemilinearProperOpen.extension_exact
      (scalarRings l E) (scalarTransitions l E) j).2.1
    colimits := (ProEtale.SemilinearProperOpen.extension_exact
      (scalarRings l E) (scalarTransitions l E) j).2.2
    adjunction :=
      (ProEtale.SemilinearProperOpen.ordinaryOpenAdj
        (scalarRings l E) (scalarTransitions l E) j).ofNatIsoRight
        (((pullbackTensorSequenceAdjunction l E j).ofNatIsoRight
          (ordinaryBridge l E j)).leftAdjointUniq
            (ProEtale.SemilinearProperOpen.ordinaryAdj
              (scalarRings l E) (scalarTransitions l E) j)).symm }

private def ordinaryDirectComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackTensorSequenceDirect l E f ⋙ pullbackTensorSequenceDirect l E g ≅
      pullbackTensorSequenceDirect l E (f ≫ g) :=
  Functor.isoWhiskerRight (ordinaryBridge l E f) _ ≪≫
    Functor.isoWhiskerLeft _ (ordinaryBridge l E g) ≪≫
    ProEtale.SemilinearProperOpen.pushComp (scalarRings l E) (scalarTransitions l E) f g ≪≫
    (ordinaryBridge l E (f ≫ g)).symm

private theorem ordinaryDirectComp_sections {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : Z.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f ⋙
      pullbackTensorSequenceDirect l E g).obj M).val.obj (op (n, U))) :
    ((ordinaryDirectComp l E f g).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  simp only [ordinaryDirectComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change ((ProEtale.SemilinearProperOpen.pushComp
    (scalarRings l E) (scalarTransitions l E) f g).hom.app
      M).val.app (op (n, U)) x = _
  exact ProEtale.SemilinearProperOpen.pushComp_apply
    (scalarRings l E) (scalarTransitions l E) f g M n U x

private def ordinaryPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackTensorSequenceInverse l E (f ≫ g) ≅
      pullbackTensorSequenceInverse l E g ⋙ pullbackTensorSequenceInverse l E f :=
  (Adjunction.leftAdjointCompIso (pullbackTensorSequenceAdjunction l E g)
    (pullbackTensorSequenceAdjunction l E f)
    (pullbackTensorSequenceAdjunction l E (f ≫ g)) (ordinaryDirectComp l E f g)).symm

private theorem derivedComp_model
    {C D F : Type*} [Category C] [Category D] [Category F]
    [Abelian C] [Abelian D] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory F]
    (A : C ⥤ D) (B : D ⥤ F) (H : C ⥤ F)
    [A.Additive] [B.Additive] [H.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ A ⋙ B) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso A B).symm).hom.app
          (DerivedCategory.Q.obj P) ≫
        B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.hom.app P) ≫
        B.mapDerivedCategoryFactors.hom.app ((A.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  calc
    _ = (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
        (A ⋙ B).mapDerivedCategoryFactors.hom.app P := by
      simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
        congrArg (fun k ↦ (Functor.mapDerivedCategoryNatIso e).hom.app
          (DerivedCategory.Q.obj P) ≫ k)
            (Functor.mapDerivedCategoryCompIso_hom_app_factors A B P)
    _ = _ := Functor.mapDerivedCategoryNatIso_fac e P

private def compositors (o : Operations l E) : Compositors l E o where
  ordinaryDirect := ordinaryDirectComp l E
  sections := ordinaryDirectComp_sections l E
  ordinaryPull := ordinaryPullComp l E
  conjugate f g := by
    apply Iso.ext
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (pullbackTensorSequenceAdjunction l E g) (pullbackTensorSequenceAdjunction l E f)
      (pullbackTensorSequenceAdjunction l E (f ≫ g)) (ordinaryDirectComp l E f g)
  pullComp f g := Functor.mapDerivedCategoryNatIso (ordinaryPullComp l E f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (pullbackTensorSequenceInverse l E g)
      (pullbackTensorSequenceInverse l E f)).symm
  pullComp_model f g P := derivedComp_model
    (pullbackTensorSequenceInverse l E g) (pullbackTensorSequenceInverse l E f)
    (pullbackTensorSequenceInverse l E (f ≫ g)) (ordinaryPullComp l E f g) P

/-- Existence of the ordinary/derived operation models, without proper/open
pasting or a tensor composition assertion.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI, 03D8, 0941;
strict-system realization steps 1 and 2 of fix-prop-coherence
(blueprint: lem-sf-integral-system-operation-models).

Proof: on the ringed sequence site, derive the ordinary direct image by K-injective
resolutions. Its exact left adjoint descends with the standard complex factorization;
localization uniqueness identifies it with pull. Finite left extension to a level is
left adjoint to evaluation. Derive this extension using flat-term K-flat
resolutions on the sequence site; evaluation is exact and hence is its derived
right adjoint. Exact pullback commutes with the derived extension by the quotient
pure-tensor formula (zero above that level). This requires no flatness of quotient
rings: use derived scalar extension in the finite left extension. Transposing
this isomorphism of derived left adjoints gives direct evaluation,
its unit and counit equations. Naturality for adjacent quotient maps gives the
restricted direct comparison and the transition equation in DirectEvaluation.
For an open immersion construct ordinary extension by zero on the sequence site;
it is additive and exact, with adjunction to the specified inverse image. Localize
this adjunction. The inverse-image evaluation comparison has an invertible open
mate by the slice extension formula, giving OpenEvaluation and Operations.
Ordinary direct-image composition is restriction of sections along pullbackComp.
Its inverse is restriction along the inverse scheme isomorphism. Take its ordinary
adjoint conjugate, then localize complexes, obtaining Compositors including its
representative equation. The identity on sections identifies the ordinary direct
image with the intrinsic semilinear presentation and gives CanonicalBridge.
The open unit is invertible by restriction of extension by zero. For a cartesian
open square the slice extension comparison is invertible; take its inverse to be
the displayed open-unit transpose. The slice tensor formula likewise gives the
projection isomorphism with the displayed inverse transpose. For a clopen immersion,
extension by zero is direct image, with map the direct-image transpose of the
inverse open unit. These are exactly the fields of OpenComparisons. All formulas
include the empty open and zero complexes. No proper/open pasting or tensor
composition coherence is assumed in this construction. -/
theorem integralSystemOperationModels :
    ∃ (o : Operations l E) (c : Compositors l E o),
      Nonempty (OpenComparisons l E o c) ∧ Nonempty (CanonicalBridge l E o) := by
  classical
  let d : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Direct l E f :=
    fun f ↦ Classical.choice (direct_exists l E f)
  have he {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
      OpenEvaluation l E (ordinaryOpen l E j) := by
    let a := ordinaryOpen l E j
    exact {
      evaluation := fun n ↦ (@asIso _ _ _ _
        ((mateEquiv a.adj (finiteOpenAdj l E j n)).symm
          (pullbackTensorDerivedEvaluation l E j n).hom)
        (integralSystemOpenEvaluation_isIso l E j a n)).symm
      transpose := fun n ↦ rfl }
  let o : Operations l E := {
    direct := d
    evaluation := fun f ↦ Classical.choice (integralSystemDirectEvaluation l E f (d f))
    extension := ordinaryOpen l E
    openEvaluation := he }
  refine ⟨o, compositors l E o, integralSystemOpenComparisons l E o (compositors l E o), ?_⟩
  exact ⟨{
    ordinary := ordinaryBridge l E
    sections := fun _ _ _ _ _ ↦ rfl }⟩

end WeilConjectures.IntegralSystemRealization
