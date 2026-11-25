/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.NativeComparison.IntegralNativeOrdinaryComparison
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Exact localization of the native inverse-image comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v u₁ u₂ u₃ u₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization.NativeComparison
private theorem derived_conjugate
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.Additive] [L₂.Additive] [R₁.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (p : L₂ ≅ L₁) (r : R₁ ≅ R₂)
    (hr : r.hom = conjugateEquiv a b p.hom) :
    (Functor.rightDerivedFunctorNatIso r).hom =
      conjugateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        b.mapDerivedCategoryRightDerivedAdjunction (Functor.mapDerivedCategoryNatIso p).hom := by
  apply R₁.rightDerivedFunctor.rightDerived_ext R₁.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso D (.up ℤ))
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedNatTrans_app, Functor.whiskerRight_app,
    conjugateEquiv_apply_app]
  erw [b.mapDerivedCategoryRightDerivedAdjunction.unit.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  let Z := (R₁.mapHomotopyCategory (.up ℤ)).obj X
  let m : (L₂.mapHomotopyCategory (.up ℤ)).obj Z ⟶ X :=
    (NatTrans.mapHomotopyCategory p.hom (.up ℤ)).app Z ≫
      (a.mapHomotopyCategory (.up ℤ)).counit.app X
  have hε := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ))
    L₁.mapDerivedCategoryFactorsh.hom R₁.rightDerivedFunctorUnit X
  have hB : L₂.mapDerivedCategory.map (R₁.rightDerivedFunctorUnit.app X) ≫
      (Functor.mapDerivedCategoryNatIso p).hom.app (R₁.rightDerivedFunctor.obj
        (DerivedCategory.Qh.obj X)) ≫
      a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj X) =
    L₂.mapDerivedCategoryFactorsh.hom.app Z ≫ DerivedCategory.Qh.map m := by
    erw [(Functor.mapDerivedCategoryNatIso p).hom.naturality_assoc]
    erw [hε]
    rw [← Category.assoc]
    erw [Functor.mapDerivedCategoryNatIso_fach p Z]
    rw [Category.assoc, ← Functor.map_comp]
  rw [hB, Functor.map_comp]
  have hη := (b.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    L₂.mapDerivedCategoryFactorsh.hom R₂.rightDerivedFunctorUnit Z
  erw [← Category.assoc, hη, Category.assoc,
    ← R₂.rightDerivedFunctorUnit.naturality m]
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [m, Z, Functor.map_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app]
  rw [← Functor.map_comp]
  congr 1
  ext i
  (simp [hr, conjugateEquiv_apply_app]; rfl)

private theorem exact_transport
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L L' : A ⥤ B} {K K' : C ⥤ D} {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [L'.Additive] [K.Additive] [K'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (p : L ≅ L') (q : K ≅ K')
    (e : L ⋙ H ≅ G ⋙ K) (e' : L' ⋙ H ≅ G ⋙ K')
    (he : ∀ M, H.map (p.hom.app M) ≫ e'.hom.app M =
      e.hom.app M ≫ q.hom.app (G.obj M)) :
    ∀ M, H.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso p).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso e').hom.app M =
      (Functor.mapDerivedCategorySquareIso e).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso q).hom.app (G.mapDerivedCategory.obj M) := by
  have hh : Functor.whiskerRight (Functor.mapDerivedCategoryNatIso p).hom
        H.mapDerivedCategory ≫ (Functor.mapDerivedCategorySquareIso e').hom =
      (Functor.mapDerivedCategorySquareIso e).hom ≫
        Functor.whiskerLeft G.mapDerivedCategory (Functor.mapDerivedCategoryNatIso q).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    apply (cancel_mono (K'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      K'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P))).mp
    simp only [Category.assoc]
    rw [Functor.exactSquare_fac e']
    rw [← H.mapDerivedCategory.map_comp_assoc,
      Functor.mapDerivedCategoryNatIso_fac p P]
    rw [H.mapDerivedCategory.map_comp, Category.assoc]
    erw [H.mapDerivedCategoryFactors.hom.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp]
    have hn := (Functor.mapDerivedCategoryNatIso q).hom.naturality
      (G.mapDerivedCategoryFactors.hom.app P)
    rw [← reassoc_of% hn]
    rw [Functor.mapDerivedCategoryNatIso_fac q]
    rw [reassoc_of% Functor.exactSquare_fac e P, ← Functor.map_comp]
    congr 2
    congr 1
    ext i
    exact he (P.X i)
  intro M
  exact congr_app hh M

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] coefficientSequenceEvaluation_additiveInstance

attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence
  constantSheaf presheafToSheaf MorphismProperty.Over.pullback
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition coefficientSequenceEvaluation
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

attribute [local irreducible] ordinaryPullIso ordinaryEvaluation
  pullbackTensorLevelIntrinsic

private theorem derivedEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    Functor.mapDerivedCategorySquareIso (ordinaryEvaluation l E f n) =
      pullbackTensorDerivedEvaluation l E f n := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  apply (pullbackTensorDerivedEvaluation_existsUnique l E f n).unique
  · unfold pullbackTensorDerivedEvaluationNormalization
    intro P
    have h := Functor.exactSquare_fac (ordinaryEvaluation l E f n) P
    have hc : (((ordinaryEvaluation l E f n).hom.mapHomologicalComplex (.up ℤ)).app P) =
        (pullbackTensorInverseEvaluationComplex l E f n).inv.app P ≫
          (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
            (.up ℤ)).hom.app
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P) := by
      apply HomologicalComplex.hom_ext
      intro i
      simp only [ordinaryEvaluation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        NatTrans.mapHomologicalComplex_app_f, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, pullbackTensorInverseEvaluationComplex, Iso.trans_inv,
        Iso.symm_inv]
      let α := (pullbackTensorSequenceInverseEvaluation l E f n).inv.app (P.X i)
      let β := (pullbackTensorLevelIntrinsic l E f n).hom.app
        ((coefficientSequenceEvaluation l E Y n).obj (P.X i))
      change α ≫ β = 𝟙 _ ≫ α ≫ 𝟙 _ ≫ β
      simp only [Category.id_comp]
    rw [hc, Functor.map_comp] at h
    exact h
  · exact (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec

/-- Exact localization of ordinary whole-system left-adjoint uniqueness.
The specified ordinary direct isomorphism determines this comparison.
Source: exact localization of adjoint uniqueness.
(blueprint: lem-sf-integral-native-exact-comparison). -/
def derivedPullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : pullbackTensorSequenceDirect l E f ≅
      ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f) :
    pull l E f ≅ ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f :=
  letI := ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  letI := ProEtale.VaryingRing.pullLimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  letI := ProEtale.VaryingRing.pullColimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  Functor.mapDerivedCategoryNatIso
    (ordinaryPullIso l E f r)

/-- Exact localization of the ordinary native comparison preserves finite evaluation.
Source: the whole-cochain normalization and exact-square factorization.
Proof: localize the ordinary square, use natural-transformation extensionality and
its cochain factor equations, then use the normalized derived evaluation uniqueness.
(blueprint: lem-sf-integral-native-exact-comparison). -/
theorem derived_pull_square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r : pullbackTensorSequenceDirect l E f ≅
      ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f)
    (hr : ∀ N, (coefficientSequenceEvaluation l E Y n).map (r.hom.app N) ≫
      (compactSupportOrdinaryDirectEvaluation l E f n).hom.app N =
        (pullbackTensorSequenceDirectEvaluation l E f n).hom.app N)
    (M : System l E Y) :
    letI := ProEtale.StrictTower.modulePullback_additive (compactSupportSystemLevel l E n) f
    letI := ProEtale.StrictTower.modulePullback_finiteLimits (compactSupportSystemLevel l E n) f
    letI := ProEtale.StrictTower.modulePullback_finiteColimits (compactSupportSystemLevel l E n) f
    letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((derivedPullIso l E f r).hom.app M) ≫
      (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M =
    (pullbackTensorDerivedEvaluation l E f n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (nativeFinitePullIso l E f n)).inv.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M) := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let := ProEtale.VaryingRing.pullAdditive R q f
  let := ProEtale.VaryingRing.pullLimits R q f
  let := ProEtale.VaryingRing.pullColimits R q f
  let := ProEtale.StrictTower.modulePullback_additive (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteLimits (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteColimits (R n) f
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let : (coefficientSequenceEvaluation l E Y n).Additive :=
    coefficientSequenceEvaluation_additive l E Y n
  let : (coefficientSequenceEvaluation l E X n).Additive :=
    coefficientSequenceEvaluation_additive l E X n
  let : PreservesFiniteLimits (coefficientSequenceEvaluation l E Y n) :=
    coefficientSequenceEvaluation_limits l E Y n
  let : PreservesFiniteColimits (coefficientSequenceEvaluation l E Y n) :=
    coefficientSequenceEvaluation_colimits l E Y n
  let : PreservesFiniteLimits (coefficientSequenceEvaluation l E X n) :=
    coefficientSequenceEvaluation_limits l E X n
  let : PreservesFiniteColimits (coefficientSequenceEvaluation l E X n) :=
    coefficientSequenceEvaluation_colimits l E X n
  have h := exact_transport
    (L := pullbackTensorSequenceInverse l E f)
    (L' := ProEtale.VaryingRing.pull R q f)
    (K := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (K' := ProEtale.StrictTower.modulePullback (R n) f)
    (G := coefficientSequenceEvaluation l E Y n)
    (H := coefficientSequenceEvaluation l E X n)
    (ordinaryPullIso l E f r) (nativeFinitePullIso l E f n).symm
    (ordinaryEvaluation l E f n) (ProEtale.VaryingRing.moduleEvalG R q f n)
    (ordinary_pull_square l E f n r hr) M
  rw [derivedEvaluation_eq l E f n, Functor.mapDerivedCategoryNatIso_symm] at h
  simpa only [R, q, derivedPullIso, ProEtale.VaryingRing.evalG,
    Functor.mapDerivedCategorySquareIso, coefficientSequenceDerivedEvaluation,
    pull, pullbackTensorSequenceDerived, ProEtale.VaryingRing.ev,
    ProEtale.VaryingRing.eval, SemilinearSections.evaluation,
    coefficientSequenceEvaluation] using h

/-- Finite adjoint conjugation is the fixed right-derived direct coordinate change.
Source: derived unit/counit factor equations and ordinary left-adjoint uniqueness.
Proof: test right-derived transformations on homotopy inputs. The factor equations
reduce conjugation to its ordinary formula, checked in each complex degree. Apply
this to the ordinary finite comparison and invert the resulting isomorphism.
(blueprint: lem-sf-integral-native-finite-derived-conjugate). -/
theorem finite_derived_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := ProEtale.StrictTower.modulePullback_additive (compactSupportSystemLevel l E n) f
    letI := ProEtale.StrictTower.modulePullback_finiteLimits (compactSupportSystemLevel l E n) f
    letI := ProEtale.StrictTower.modulePullback_finiteColimits (compactSupportSystemLevel l E n) f
    letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    letI := proEtaleConstantModuleDirectImage_additive f
      (finiteCoefficientRing l E (n + 1))
    conjugateEquiv (finiteAdj l E f n)
      (ProEtale.VaryingRing.levelAdj (compactSupportSystemLevel l E) f n)
      (Functor.mapDerivedCategoryNatIso (nativeFinitePullIso l E f n)).hom =
    (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel f (finiteCoefficientRing l E (n + 1)))).inv := by
  let := proEtaleConstantModuleDirectImage_additive f
    (finiteCoefficientRing l E (n + 1))
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let := ProEtale.StrictTower.modulePullback_additive (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteLimits (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteColimits (R n) f
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let a := proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients R Y n) (ProEtale.VaryingRing.coefficients R X n)
    (ProEtale.StrictTower.constantRingIso (R n) f)
  let b := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))
  let s := compactSupportDirectModel f (finiteCoefficientRing l E (n + 1))
  have h := derived_conjugate a b (nativeFinitePullIso l E f n).symm s
    (nativeFinitePullIso_conjugate l E f n).symm
  rw [Functor.mapDerivedCategoryNatIso_symm] at h
  have hi : conjugateIsoEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategoryNatIso (nativeFinitePullIso l E f n)).symm =
        Functor.rightDerivedFunctorNatIso s := Iso.ext h.symm
  exact congrArg Iso.inv hi

end WeilConjectures.IntegralSystemRealization.NativeComparison
