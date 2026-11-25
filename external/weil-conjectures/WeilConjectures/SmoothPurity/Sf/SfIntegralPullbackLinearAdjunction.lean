/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # The integral constructible adjunction before scalar localization

Source: Stacks Project Tag 099N(2), Bhatt--Scholze Lemma 6.7.2.
(blueprint: lem-sf-integral-pullback-linear-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory AlgebraicGeometry CategoryTheory.Functor

namespace CategoryTheory
private noncomputable def faithfulIntegralReduction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {Q : Type u₃} [Category.{v₃} Q]
    (i : C ⥤ D) (hi : i.FullyFaithful)
    {S : D ⥤ Q} {T : Q ⥤ D} (a : S ⊣ T)
    (h : ∀ Y, IsIso (a.unit.app (i.obj Y))) : (i ⋙ S).FullyFaithful where
  preimage {X Y} f := hi.preimage (a.homEquiv _ _ f ≫ inv (a.unit.app (i.obj Y)))
  map_preimage {X Y} f := by
    let := h Y
    change S.map (i.map _) = _
    rw [hi.map_preimage]
    apply (a.homEquiv _ _).injective
    have hh : ∀ g : i.obj X ⟶ i.obj Y,
        a.homEquiv _ _ (S.map g) = g ≫ a.unit.app (i.obj Y) := fun g ↦ by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality g).symm
    rw [hh]
    simp
  preimage_map {X Y} f := by
    let := h Y
    change hi.preimage (a.homEquiv _ _ (S.map (i.map f)) ≫ _) = _
    rw [a.homEquiv_unit]
    have hh := (a.unit.naturality (i.map f)).symm
    change a.unit.app (i.obj X) ≫ T.map (S.map (i.map f)) = _ at hh
    rw [hh]
    simp
end CategoryTheory

universe u
namespace WeilConjectures
open FrobeniusExchange

/-- Integral pullback has a coefficient-linear right adjoint on constructible objects.
Source: Stacks Project Tag 099N(2); Bhatt--Scholze 6.5.9, 6.7.2
(blueprint: lem-sf-integral-pullback-linear-adjunction).
Proof: use the actual whole-system reduction/limit adjunction and system pullback
adjunction. Its reconstruction unit is invertible on complete constructible objects,
so reduction composed with the full inclusion is fully faithful. The normalized
pullback realization gives the natural comparison needed by restrictFullyFaithful.
The existing system direct image preserves constructibility, so it restricts to the
recorded full subcategories. Its additive and O_E-linear structures are supplied by
the sectionwise direct-image action and its derived limit. The resulting right
functor is the actual directImageFunctor, not data chosen from existence. No
rationalization, coefficient-change mate, common-stage or Weil result is used. -/
theorem sfIntegralPullbackLinearAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ R : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y,
      Nonempty (constructibleIntegralPullback l E f ⊣ R) ∧ R.Additive ∧
        R.Linear (Padic.coefficientExtensionIntegers l E) := by
  let DX := (models l E).system X
  let DY := (models l E).system Y
  let iX := (sfIntegralConstructible l E X).ι
  let iY := (sfIntegralConstructible l E Y).ι
  let t := whiskerLeft iY (integralComparisonPullbackCounit l E f DY DX
    ((models l E).roos X) ((models l E).pullback f))
  let : ∀ K : sfIntegralConstructibleCategory l E Y, IsIso (t.app K) :=
    fun K ↦ (models l E).effective f K
  let := NatIso.isIso_of_isIso_app t
  let e : iY ⋙ (DY.reduction ⋙ integralComparisonDerivedSequencePullback l E f) ≅
      constructibleIntegralPullback l E f ⋙ (iX ⋙ DX.reduction) := (asIso t).symm
  let a := DY.adjunction.comp (systemAdjunction l E f)
  refine ⟨directImageFunctor l E K₀ hl f, ⟨?_⟩, directImage_linear l E K₀ hl f⟩
  exact a.restrictFullyFaithful (sfIntegralConstructible l E Y).fullyFaithfulι
    (CategoryTheory.faithfulIntegralReduction iX
      (sfIntegralConstructible l E X).fullyFaithfulι
      DX.adjunction ((models l E).complete X)) e (Iso.refl _)

end WeilConjectures
