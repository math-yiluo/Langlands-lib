/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted

/-!
# Independence of the augmented integral reduction tower

Source: Stacks Project, sites-cohomology.tex, Tags 06YS/06YT/06YY; derived.tex,
Tags 05RT/06XN; Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

The index n denotes exponent n+1. Pure tensors characterize the chain maps before
localization; the finite comparison is the composite of the recorded canonical
K-flat computation isomorphisms. No arbitrary comparison or transition is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

-- Avoid unfolding the inverse limit and the constructed maps when identifying interfaces.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence integralReductionExistence
  integralReductionDerivedExistence
  unrestrictedTowerUnit unrestrictedTowerTransition unrestrictedTowerResolutionIso
  unrestrictedTowerFiniteComparison unrestrictedTowerComparison

attribute [local instance] integralReductionChangeOfRingsAdditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Restriction changes the scalar action and keeps the underlying additive map.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable instance integralTowerRestrictionAdditive (n : ℕ) :
    (completedIntegralRestrictScalars l E Y D hl n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars
    (completedIntegralCoefficientProjection l E Y D hl n)).Additive

/-- Exactness supplies the limits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
theorem integralTowerRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E Y D hl n) :=
  (completedIntegralRestrictScalars_exact l E Y D hl n).1

attribute [local instance] integralTowerRestrictionLimits

/-- Exactness supplies the colimits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
theorem integralTowerRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E Y D hl n) :=
  (completedIntegralRestrictScalars_exact l E Y D hl n).2

attribute [local instance] integralTowerRestrictionColimits

/-- The same reduction regarded as a complex over the completed coefficient sheaf.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable abbrev integralTowerComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  unrestrictedTowerComplex l E Y n P

/-- A pure tensor, followed by sheafification, in the recorded finite reduction.
Transport uses the object equality in the defining change-of-rings witness.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerTensorSection (n : ℕ)
    (M : completedIntegralModuleSheaves l E Y D hl)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((integralReductionChangeOfRings l E Y D hl n).obj M).val.obj U :=
  (eqToHom ((integralReductionExistence l E Y D hl n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjection l E Y D hl n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheaf l E Y D hl).obj.obj U,
            ((completedIntegralCommRingProjection l E Y D hl n).hom.app U).hom] x))

/-- The unit maps are specified on local sections by x ↦ 1 ⊗ x and sheafification.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
def integralTowerUnitCondition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (γ : ∀ n : ℕ, P ⟶ integralTowerComplex l E Y D hl n P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : (P.X i).val.obj U),
    ((γ n).f i).val.app U x = integralTowerTensorSection l E Y D hl n (P.X i) U 1 x

/-- The transition maps are specified on sheafified pure tensors by s ⊗ x ↦ ρ(s) ⊗ x.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
def integralTowerTransitionCondition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (τ : ∀ n : ℕ, integralTowerComplex l E Y D hl (n + 1) P ⟶
      integralTowerComplex l E Y D hl n P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj U)
    (x : (P.X i).val.obj U),
    ((τ n).f i).val.app U (integralTowerTensorSection l E Y D hl (n + 1) (P.X i) U s x) =
      integralTowerTensorSection l E Y D hl n (P.X i) U
        ((integralCoefficientSheafTransition l E Y n).hom.app U s) x

private theorem integralTowerTensorSection_ext (n : ℕ)
    (M N : completedIntegralModuleSheaves l E Y D hl)
    (f g : (completedIntegralRestrictScalars l E Y D hl n).obj
      ((integralReductionChangeOfRings l E Y D hl n).obj M) ⟶ N)
    (h : ∀ U s x,
      f.val.app U (integralTowerTensorSection l E Y D hl n M U s x) =
        g.val.app U (integralTowerTensorSection l E Y D hl n M U s x)) : f = g := by
  let e := (integralReductionExistence l E Y D hl n).choose_spec.choose M
  let a := (completedIntegralRestrictScalars l E Y D hl n).map (eqToHom e.symm)
  apply (cancel_epi a).1
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul s x => exact h U s x
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

private theorem integralTowerUnrestricted_condition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    integralTowerUnitCondition l E Y D hl P (unrestrictedTowerUnit l E Y P) ∧
      integralTowerTransitionCondition l E Y D hl P
        (unrestrictedTowerTransition l E Y P) := by
  constructor
  · change unrestrictedTowerUnitCondition l E Y P (unrestrictedTowerUnit l E Y P)
    exact unrestrictedTowerUnit_condition l E Y P
  · intro n i U s x
    have h :=
      (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec P i U s x
    unfold unrestrictedIntegralTensorSection at h
    unfold unrestrictedTowerTransition unrestrictedIntegralTransition integralTowerTensorSection
    exact h

/-- There is a unique pair of chain-level unit and reduction maps with the stated
pure-tensor formulas. These formulas specify maps on the sheafifications, not just on
constant sections.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined).
Proof: in each degree and site object send x to the sheafification of 1⊗x. Tensor
balancing, naturality of the coefficient projection and of the sheafification unit
make this a map of presheaves of modules, hence of sheaves. For the transition send
s⊗x to ρ(s)⊗x before sheafification. The identity π_n = ρ_n π_(n+1) makes this
balanced and linear over the completed ring. Both maps commute with restrictions
and with the differential by their sectionwise formulas, so define chain maps.
Uniqueness of the unit follows on every section from its formula. For the transition,
pure tensors generate the presheaf tensor product, and the universal property of
sheafification extends equality to the sheaves. Degreewise equality is equality of
chain maps; function extensionality gives uniqueness of the pair at every level. -/
theorem integralTowerMaps_existUnique
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    ∃! a : (∀ n : ℕ, P ⟶ integralTowerComplex l E Y D hl n P) ×
      (∀ n : ℕ, integralTowerComplex l E Y D hl (n + 1) P ⟶
        integralTowerComplex l E Y D hl n P),
      integralTowerUnitCondition l E Y D hl P a.1 ∧
        integralTowerTransitionCondition l E Y D hl P a.2 := by
  classical
  let γ : ∀ n : ℕ, P ⟶ integralTowerComplex l E Y D hl n P :=
    unrestrictedTowerUnit l E Y P
  let τ : ∀ n : ℕ, integralTowerComplex l E Y D hl (n + 1) P ⟶
      integralTowerComplex l E Y D hl n P := unrestrictedTowerTransition l E Y P
  have hγ : integralTowerUnitCondition l E Y D hl P γ :=
    (integralTowerUnrestricted_condition l E Y D hl P).1
  have hτ : integralTowerTransitionCondition l E Y D hl P τ :=
    (integralTowerUnrestricted_condition l E Y D hl P).2
  refine ⟨(γ, τ), ⟨hγ, hτ⟩, ?_⟩
  intro a ha
  apply Prod.ext
  · funext n
    ext i U x
    exact (ha.1 n i U x).trans (hγ n i U x).symm
  · funext n
    ext i : 1
    apply integralTowerTensorSection_ext l E Y D hl (n + 1) (P.X i)
    intro U s x
    exact (ha.2 n i U s x).trans (hτ n i U s x).symm

/-- The chain-level unit x ↦ x⊗1, determined uniquely by its sectionwise formula.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerUnit
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    P ⟶ integralTowerComplex l E Y D hl n P :=
  (integralTowerMaps_existUnique l E Y D hl P).exists.choose.1 n

/-- The chain-level reduction id⊗ρ, determined uniquely on sheafified pure tensors.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerTransition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    integralTowerComplex l E Y D hl (n + 1) P ⟶ integralTowerComplex l E Y D hl n P :=
  (integralTowerMaps_existUnique l E Y D hl P).exists.choose.2 n

private theorem integralTowerMaps_eq
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    (integralTowerMaps_existUnique l E Y D hl P).exists.choose =
      (unrestrictedTowerUnit l E Y P, unrestrictedTowerTransition l E Y P) := by
  exact (integralTowerMaps_existUnique l E Y D hl P).unique
    (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec
    (integralTowerUnrestricted_condition l E Y D hl P)

private theorem integralTowerUnit_eq
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    integralTowerUnit l E Y D hl P n = unrestrictedTowerUnit l E Y P n :=
  congrArg (fun a ↦ a.1 n) (integralTowerMaps_eq l E Y D hl P)

private theorem integralTowerTransition_eq
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    integralTowerTransition l E Y D hl P n = unrestrictedTowerTransition l E Y P n :=
  congrArg (fun a ↦ a.2 n) (integralTowerMaps_eq l E Y D hl P)

/-- The image of the resolution augmentation is invertible in the derived category.
Source: Stacks Tag 06YS (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerAugmentationIso
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
  letI : QuasiIso q := hq.1
  asIso (DerivedCategory.Q.map q)

end WeilConjectures
