/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOpenComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.NativeComparison.IntegralNativeDerivedComparison
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOpenComparison
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativePullEvaluation
import all WeilConjectures.SixFunctors.FrobeniusExchange.IntegralSystemEvaluationNormalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization

/-! # Native normalization of strict-system finite evaluations

The finite evaluations of the strict-system direct image and open extension are
specified by adjunction mates of the section-normalized pullback evaluation. This
file identifies them with the native varying-ring evaluations `evalP` and `evalJ`,
followed by the fixed finite coordinate changes.

Source: Zheng 4.1 and 4.10; Stacks 03DI, 03D2
(blueprint: def-weil-system-operation-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  coefficientSequenceEvaluation_additiveInstance coefficientSequenceEvaluation_limits
  coefficientSequenceEvaluation_colimits sfIntrinsicPullback_additive
  sfIntrinsicPullback_preservesFiniteLimits sfIntrinsicPullback_preservesFiniteColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Cancel an isomorphism after composing with its inverse. -/
private theorem eq_comp_inv_hom {C : Type*} [Category C] {A B B' : C} (x : A ⟶ B')
    (i : B ≅ B') : x = (x ≫ i.inv) ≫ i.hom := by
  simp

/-- Invert a square presented as a whiskered coordinate change followed by an inverse. -/
private theorem square_inv_of_hom {B C D D' : Type*} [Category B] [Category C] [Category D]
    [Category D'] {G : C ⥤ D} {F : C ⥤ B} {H : B ⥤ D'} {K K' : D ⥤ D'}
    (θ : G ⋙ K ≅ F ⋙ H) (e : K' ≅ K) (g : F ⋙ H ≅ G ⋙ K')
    (hθ : θ.hom = Functor.whiskerLeft G e.inv ≫ g.inv) (N : C) :
    H.map ((Iso.refl F).hom.app N) ≫ g.hom.app N ≫ e.hom.app (G.obj N) =
      θ.symm.hom.app N := by
  rw [Iso.symm_hom, ← cancel_epi (θ.hom.app N), Iso.hom_inv_id_app, hθ]
  simp

section SquareIso
variable {A B B' C : Type*} [Category A] [Category B] [Category B'] [Category C] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The localized square of an inverse square is the inverse localized square. -/
theorem mapDerivedCategorySquareIso_symm_hom (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm]

end SquareIso

/-- The native finite pullback coordinate change is the open-square pullback model.
Both are characterized by preserving the units of the same direct-image adjunction. -/
theorem nativeFinitePullIso_eq_openSquarePullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) :
    IntegralSystemRealization.NativeComparison.nativeFinitePullIso l E f n =
      openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  refine (openSquarePullbackModel_existsUnique A f).unique ?_
    (openSquarePullbackModel_existsUnique A f).exists.choose_spec
  intro M V s
  unfold IntegralSystemRealization.NativeComparison.nativeFinitePullIso
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((proEtaleRingModuleAdjunction f
      (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) Y n)
      (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) X n)
      (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) f)).ofNatIsoRight
        (compactSupportDirectModel f A))
    (sfIntrinsicConstantModuleAdjunction f A) M
  exact congrArg (fun z ↦ z.val.app (op V) s) h

/-- The inverse mate of the native ordinary direct-image evaluation, in finite intrinsic
coordinates, is the native ordinary pullback evaluation followed by the open-square
pullback coordinate change.
Source: Zheng 4.1; Stacks 03D2. Proof: transport the mate through the finite
adjoint coordinate change, using that `moduleEvalG` is the mate of `moduleEvalP`. -/
theorem pullEvaluationMate_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((mateEquiv (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f)
      (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l E (n + 1)))).symm
      (TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalP (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n ≪≫
          Functor.isoWhiskerLeft (ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) X n)
          (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1)))).hom)
        ) =
    Functor.whiskerLeft (ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Y n)
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f).inv ≫
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).inv := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let a := ProEtale.VaryingRing.moduleAdj R q f
  let b := sfIntrinsicConstantModuleAdjunction f A
  let b' := proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients R Y n) (ProEtale.VaryingRing.coefficients R X n)
    (ProEtale.StrictTower.constantRingIso (R n) f)
  let s := compactSupportDirectModel f A
  let e := openSquarePullbackModel A f
  let G := ProEtale.VaryingRing.eval R q Y n
  let H := ProEtale.VaryingRing.eval R q X n
  let t : TwoSquare G (ProEtale.VaryingRing.pull R q f) (sfIntrinsicPullback A f) H :=
    TwoSquare.mk _ _ _ _ (Functor.whiskerLeft G e.inv ≫
      (ProEtale.VaryingRing.moduleEvalG R q f n).inv)
  have hs : conjugateIsoEquiv b' b
      (IntegralSystemRealization.NativeComparison.nativeFinitePullIso l E f n).symm = s :=
    Iso.ext (IntegralSystemRealization.NativeComparison.nativeFinitePullIso_conjugate l E f n)
  rw [nativeFinitePullIso_eq_openSquarePullbackModel] at hs
  have hs' : conjugateEquiv b b' e.hom = s.inv := congrArg Iso.inv hs
  have hm : (mateEquiv a b'
      (TwoSquare.mk G _ _ H (ProEtale.VaryingRing.moduleEvalG R q f n).inv)) =
        (ProEtale.VaryingRing.moduleEvalP R q f n).hom :=
    varyingModuleEvalMate R q f n
  have key : mateEquiv a b t = TwoSquare.mk _ _ _ _
      (ProEtale.VaryingRing.moduleEvalP R q f n ≪≫ Functor.isoWhiskerLeft H s).hom := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    have ht := IntegralSystemRealization.NativeComparison.transport_mates a a b b'
      (Iso.refl _) e.symm t
      (TwoSquare.mk G _ _ H (ProEtale.VaryingRing.moduleEvalG R q f n).inv)
      (fun N ↦ by
        simp only [t, Iso.symm_inv, Iso.refl_inv, NatTrans.id_app,
          CategoryTheory.Functor.map_id]
        exact Iso.hom_inv_id_app_assoc e (G.obj N) _) M
    rw [Iso.symm_inv, hs', Iso.refl_inv, conjugateEquiv_id, hm, NatTrans.id_app,
      CategoryTheory.Functor.map_id G ((ProEtale.VaryingRing.push R q f).obj M),
      Category.id_comp] at ht
    rw [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ← ht]
    exact eq_comp_inv_hom _ (s.app (H.obj M))
  exact (((mateEquiv a b).symm_apply_apply t).symm.trans
    (congrArg (mateEquiv a b).symm key)).symm

/-- Exact localization of `pullEvaluationMate_eq`: any ordinary pullback evaluation
isomorphism with the native normalization localizes to the native derived evaluation
`evalG`, followed by the open-square pullback coordinate change.
Source: Zheng 4.1; Stacks 03D2. -/
theorem pullEvaluation_derived {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (θ : ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Y n ⋙
          sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ≅
      ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
          ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) X n)
    (hθ : θ.hom = Functor.whiskerLeft (ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Y n)
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f).inv ≫
      (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).inv)
    (M : ProEtale.VaryingRing.Derived (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) Y) :
    letI := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f)).hom.app
          ((ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) Y n).obj M) =
      (Functor.mapDerivedCategorySquareIso θ).inv.app M := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let := ProEtale.StrictTower.modulePullback_additive (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteLimits (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteColimits (R n) f
  have hinv (N : ProEtale.VaryingRing.Modules R q Y) :
      (ProEtale.VaryingRing.eval R q X n).map
        ((Iso.refl (ProEtale.VaryingRing.pull R q f)).hom.app N) ≫
      (ProEtale.VaryingRing.moduleEvalG R q f n).hom.app N ≫
        (openSquarePullbackModel A f).hom.app ((ProEtale.VaryingRing.eval R q Y n).obj N) =
      θ.symm.hom.app N :=
    square_inv_of_hom θ (openSquarePullbackModel A f)
      (ProEtale.VaryingRing.moduleEvalG R q f n) hθ N
  have h := IntegralSystemRealization.localizePullSquare
    (Iso.refl (ProEtale.VaryingRing.pull R q f))
    (openSquarePullbackModel A f) θ.symm (ProEtale.VaryingRing.moduleEvalG R q f n) hinv M
  rw [Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, mapDerivedCategorySquareIso_symm_hom] at h
  exact h

/-- Cancel a normalized evaluation square: if `g ≫ k = σ⁻¹` then `k ≫ σ = g⁻¹`. -/
private theorem iso_square_cancel {C : Type*} [Category C] {P Q S : C}
    (g : P ≅ Q) (k : Q ≅ S) (σ : S ≅ P) (h : g.hom ≫ k.hom = σ.inv) :
    k.hom ≫ σ.hom = g.inv ≫ 𝟙 P := by
  apply (cancel_epi g.hom).1
  rw [← Category.assoc, h]
  simp

/-- Solve `x ≫ i⁻¹ = 𝟙 ≫ y` for `x`. -/
private theorem eq_of_comp_inv {C : Type*} [Category C] {P Q S : C} (x : P ⟶ S)
    (y : P ⟶ Q) (i : Q ≅ S) (h : x ≫ i.inv = 𝟙 P ≫ y) : x = y ≫ i.hom := by
  rw [Category.id_comp] at h
  rw [← h]
  simp

/-- The finite evaluation of the strict-system direct image, defined as the derived
adjunction mate of a pullback evaluation with the native normalization, is the native
evaluation `evalP` followed by the right-derived finite coordinate change.
Source: Zheng 4.10; Stacks 07A6. -/
theorem directEvaluationMate_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (σ : ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) Y n ⋙
          sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ≅
      ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
          ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) X n)
    (hσ : ∀ M, (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f)).hom.app
          ((ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) Y n).obj M) = σ.inv.app M)
    (M : ProEtale.VaryingRing.Derived (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) X) :
    letI := proEtaleConstantModuleDirectImage_additive f
      (Padic.coefficientExtensionRing l E (n + 1))
    (mateEquiv (ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f)
      (sfIntrinsicConstantModuleAdjunction f
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ σ.hom)).app M =
    (ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n ≪≫
      Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
        (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1))))).hom.app M := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let := ProEtale.StrictTower.modulePullback_additive (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteLimits (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteColimits (R n) f
  let a := ProEtale.VaryingRing.adj R q f
  let b := (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
  let b' := ProEtale.VaryingRing.levelAdj R f n
  let k := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A f)
  have hc : conjugateEquiv b b' k.hom =
      (Functor.rightDerivedFunctorNatIso (compactSupportDirectModel f A)).inv := by
    have h := IntegralSystemRealization.NativeComparison.finite_derived_conjugate l E f n
    rw [nativeFinitePullIso_eq_openSquarePullbackModel] at h
    exact h
  have ht := IntegralSystemRealization.NativeComparison.transport_mates a a b b'
    (Iso.refl _) k.symm (TwoSquare.mk _ _ _ _ σ.hom)
    (TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.evalG R q f n).inv)
    (fun N ↦ by
      rw [Iso.symm_inv, Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id]
      exact iso_square_cancel ((ProEtale.VaryingRing.evalG R q f n).app N)
        (k.app _) (σ.app N) (hσ N)) M
  rw [Iso.symm_inv, hc, Iso.refl_inv, conjugateEquiv_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id] at ht
  exact eq_of_comp_inv _ _ ((Functor.rightDerivedFunctorNatIso
    (compactSupportDirectModel f A)).app _) ht

/-- Transporting an adjunction along the identity of its right adjoint does nothing. -/
private theorem ofNatIsoRight_refl {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) : a.ofNatIsoRight (Iso.refl G) = a := by
  apply Adjunction.ext
  ext X
  simp

/-- Remove an identity factor in front of a composite. -/
private theorem id_comp_eq {C : Type*} [Category C] {P Q : C} {x y : P ⟶ Q} (h : x = y) :
    𝟙 P ≫ x = y := by
  rw [Category.id_comp, h]

/-- The finite evaluation of strict-system open extension, defined as the inverse derived
open-adjunction mate of a pullback evaluation with the native normalization, is inverse to
the native evaluation `evalJ` followed by the finite open coordinate change.
Source: Stacks 03DI; Zheng 4.1. -/
theorem openEvaluationMate_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (σ : ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) X n ⋙
          sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) j ≅
      ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙
          ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) U n)
    (hσ : ∀ M, (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) j)).hom.app
          ((ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) X n).obj M) = σ.inv.app M)
    (w : ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙
          ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) X n ≅
      ProEtale.VaryingRing.ev (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) U n ⋙
          sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E (n + 1)) j)
    (hw : (mateEquiv (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
        (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j))
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
        (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j))).symm
          σ.inv = w.inv)
    (M : ProEtale.VaryingRing.Derived (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) U) :
    letI := sfIntrinsicExtensionByZero_additive j (Padic.coefficientExtensionRing l E (n + 1))
    letI := (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (n + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (n + 1))).2.2
    w.hom.app M =
      (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
          (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1))))).hom.app M := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let := sfIntrinsicExtensionByZero_additive j A
  let := (sfIntrinsicExtensionByZero_exact j A).2.1
  let := (sfIntrinsicExtensionByZero_exact j A).2.2
  let := ProEtale.StrictTower.modulePullback_additive (R n) j
  let := ProEtale.StrictTower.modulePullback_finiteLimits (R n) j
  let := ProEtale.StrictTower.modulePullback_finiteColimits (R n) j
  let := sfIntrinsicPullback_additive A j
  let := sfIntrinsicPullback_preservesFiniteLimits A j
  let := sfIntrinsicPullback_preservesFiniteColimits A j
  let a := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (ProEtale.VaryingRing.moduleJAdj R q j)
  have hab : ProEtale.VaryingRing.jAdj R q j = a :=
    ProEtale.SemilinearProperOpen.Normalization.exact_adjunction_eq
      (ProEtale.VaryingRing.moduleJAdj R q j)
  have h := IntegralSystemRealization.compareOpenMates a (ProEtale.VaryingRing.jAdj R q j)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction A j))
    (ProEtale.VaryingRing.levelJAdj R j n) (Iso.refl _)
    (Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A j))
    (Functor.mapDerivedCategoryNatIso (compactSupportOpenModel j A))
    σ.inv (ProEtale.VaryingRing.evalG R q j n).hom
    (ProEtale.VaryingRing.evalJ R q j n) w rfl hw
    (IntegralSystemRealization.derivedFiniteOpen_unit l E j n)
    (fun N ↦ by
      rw [Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id]
      exact id_comp_eq (hσ N)) M
  rw [ofNatIsoRight_refl, hab, Adjunction.leftAdjointUniq_refl, NatTrans.id_app,
    CategoryTheory.Functor.map_id] at h
  exact (id_comp_eq rfl).symm.trans h |>.symm

section Sections

attribute [local irreducible] constantSheaf presheafToSheaf Functor.ofSequence
  Functor.ofOpSequence MorphismProperty.Over.pullback
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

/-- An `eqToIso` between two sectionwise descriptions of ordinary direct-image evaluation
is the identity on sections. -/
private theorem eqToIso_sections {X Y : Scheme.{u}} (n : ℕ)
    {F G : coefficientSequenceModules l E X ⥤ normalizedDVRModules l E Y n}
    (h : F = G) (M : coefficientSequenceModules l E X) (V : Y.ProEtᵒᵖ)
    (x : (F.obj M).val.obj V) :
    HEq (((eqToIso h).hom.app M).val.app V x) x := by
  subst G
  rfl

/-- Every equality between ordinary direct-image evaluation and finite direct image induces
the native ordinary direct-image evaluation, since both are the identity on sections.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
theorem eqToIso_directEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙ coefficientSequenceEvaluation l E Y n =
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1))) :
    (eqToIso h).hom = (compactSupportOrdinaryDirectEvaluation l E f n).hom := by
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  have h3 := (eqToIso_sections l E n h M V x).trans
    (compactSupportOrdinaryDirectEvaluation_sections l E f n M V x).symm
  exact eq_of_heq h3

end Sections

/-- Transpose a map into a total limit, given by its projections, under a finite
reduction adjunction. The evaluated counit is assumed to be the adjunct of the projection.
Source: Stacks 07A6 (blueprint: def-weil-system-operation-exchange-realization). -/
theorem map_comp_counit_eq_of_projection {C D T : Type*} [Category C] [Category D]
    [Category T] {F : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R) {S : C ⥤ T} {L : T ⥤ C}
    (b : S ⊣ L) {ev : T ⥤ D} (π : L ⟶ ev ⋙ R) (e : S ⋙ ev ≅ F)
    (hc : ∀ N, a.homEquiv _ _ (e.inv.app (L.obj N) ≫ ev.map (b.counit.app N)) = π.app N)
    {Q : C} {N : T} {V : D} (τ : Q ⟶ L.obj N) (ε : ev.obj N ⟶ V) (d : F.obj Q ⟶ V)
    (h : τ ≫ π.app N ≫ R.map ε = a.unit.app Q ≫ R.map d) :
    F.map τ ≫ e.inv.app (L.obj N) ≫ ev.map (b.counit.app N) ≫ ε = d := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, ← Category.assoc,
    Adjunction.homEquiv_naturality_right, hc, Adjunction.homEquiv_unit, h]

end WeilConjectures.FrobeniusExchange
