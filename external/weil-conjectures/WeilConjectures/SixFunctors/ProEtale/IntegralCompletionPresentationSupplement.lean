/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Encoding.IntegralPresentationEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralReductionTransitionComparison
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentation

/-! # Canonical completeness in the completed integral presentation

Source: blueprint main-20261015, integral-criterion-reductions, final sentence;
Stacks Project, Tags 06YY, 0941, 08TC and 0145
(blueprint: lem-pe-integral-completion-presentation).

The coefficient identification is normalized by every finite restriction square.
Finite comparisons retain their finite coefficient action.
Their restriction squares are normalized on underlying abelian sheaves, and their
units fix the derived comparisons uniquely. The index n denotes exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u d

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (A : Encoding l E X)

/-- The restriction square for the specified integral and finite coefficient encodings.
Source: blueprint integral-criterion comparison; Stacks 06YY
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev RestrictionSquare (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
    e.ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n

/-- Localize the actual restriction square; both composition comparisons are Mathlib's
canonical localization comparisons.
Source: Stacks 05RU and 06YY
(blueprint: lem-pe-integral-completion-presentation). -/
def derivedSquare (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    AdicCompletion.restrict l E X n ⋙ A.derived.functor ≅
      e.ordinaryDerived.functor ⋙ scalarReductionDerivedRestriction.{u, u} l E X n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI := scalarReductionRestrictionLimits.{u, u} l E X n
  letI := scalarReductionRestrictionColimits.{u, u} l E X n
  (Functor.mapDerivedCategoryCompIso
    (Mod.comap (AdicCompletion.quotient l E X n)) (A.modules.functor)) ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫
      (Functor.mapDerivedCategoryCompIso e.ordinary.functor
        (scalarReductionRestriction.{u, u} l E X n)).symm

/-- A comparison in D(R_n), retaining the finite coefficient action.
Source: Stacks 06YY, derived tensor under an isomorphism of coefficients
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev FiniteComparison (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  A.derived.functor ⋙
      scalarReductionDerivedExtension.{u, u} l E X n ≅
    AdicCompletion.derivedReduction l E X n ⋙ e.ordinaryDerived.functor

/-- Restrict a finite comparison to the one completed integral derived category.
Source: Stacks 06YY; blueprint integral-criterion comparison
(blueprint: lem-pe-integral-completion-presentation). -/
def restrictedComparison (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) (b : FiniteComparison l E X A n e)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (sfDerivedReductionRestricted l E X n).obj
        (A.derived.functor.obj K) ≅
      A.derived.functor.obj
        (AdicCompletion.integralLevel l E X K n) :=
  (scalarReductionDerivedRestriction.{u, u} l E X n).mapIso (b.app K) ≪≫
    ((derivedSquare l E X A n e a).app ((AdicCompletion.derivedReduction l E X n).obj K)).symm

private theorem internal_roos_complete
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : AlgebraicGeometry.ProEtale.IsDerivedComplete l E X K)
    [HasProduct (AdicCompletion.integralLevel l E X K)] :
    ∃ δ : (∏ᶜ (AdicCompletion.integralLevel l E X K)) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (AdicCompletion.integralStep l E X K) K
        (Pi.lift (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit.app K)) δ := by
  obtain ⟨P, hP, ⟨e⟩, hη⟩ := hK
  obtain ⟨p, δ, hT, hp⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP e
  let : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) := hη
  let v : K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P) :=
    e.symm ≪≫ asIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map v.inv, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine Pretriangulated.Triangle.isoMk _ _ v (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change Pi.lift _ ≫ 𝟙 _ = v.hom ≫ p
    exact (Category.comp_id _).trans hp.symm
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

private theorem map_roos_complete
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [PreservesLimit (Discrete.functor V) F]
    [HasProduct (fun n ↦ F.obj (V n))]
    (t : ∀ n, V (n + 1) ⟶ V n) (s : ∀ n, W (n + 1) ⟶ W n)
    (a : ∀ n, F.obj (V n) ≅ W n)
    (K : C) (p : ∀ n, K ⟶ V n) (q : ∀ n, F.obj K ⟶ W n)
    (ht : ∀ n, F.map (t n) ≫ (a n).hom = (a (n + 1)).hom ≫ s n)
    (hp : ∀ n, F.map (p n) ≫ (a n).hom = q n)
    (δ : (∏ᶜ V) ⟶ K⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle t K (Pi.lift p) δ) :
    ∃ δ' : (∏ᶜ W) ⟶ (F.obj K)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle s (F.obj K) (Pi.lift q) δ' := by
  let B : F.obj (∏ᶜ V) ≅ ∏ᶜ W := PreservesProduct.iso F V ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hB (n : ℕ) : B.hom ≫ Pi.π W n = F.map (Pi.π V n) ≫ (a n).hom := by
    simp [B]
  have hfirst : F.map (Pi.lift p) ≫ B.hom = Pi.lift q := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, Pi.lift_comp_π]
    rw [← Category.assoc, ← F.map_comp, Pi.lift_comp_π, hp]
  have hmiddle : F.map (towerTransitionEndomorphism t) ≫ B.hom =
      B.hom ≫ towerTransitionEndomorphism s := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_comp_π, Functor.map_sub]
    simp only [reassoc_of% hB]
    erw [F.map_id, Category.id_comp]
    congr 1
    rw [← F.map_comp_assoc, Pi.lift_comp_π, Functor.map_comp, Category.assoc, ht]
  refine ⟨B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ hT) _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B.symm B.symm ?_ ?_ ?_
  · change Pi.lift q ≫ B.inv = 𝟙 _ ≫ F.map (Pi.lift p)
    rw [← hfirst]
    simp
  · change towerTransitionEndomorphism s ≫ B.inv =
      B.inv ≫ F.map (towerTransitionEndomorphism t)
    apply (cancel_mono B.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun f ↦ B.inv ≫ f) hmiddle.symm
  · change (B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
        (shiftFunctor D (1 : ℤ)).map (𝟙 (F.obj K)) =
      B.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
    erw [(shiftFunctor D (1 : ℤ)).map_id]
    simpa only [Category.assoc, Functor.comp_obj] using
      Category.comp_id (B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)

end AlgebraicGeometry.ProEtale.IntegralPresentation
