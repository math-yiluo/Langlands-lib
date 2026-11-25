/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones

/-! # The integral reduction tower

Source: Bhatt--Scholze, p. 24, Proposition 3.5.1(1) and Definition 3.5.2;
Stacks Project, Tag 06YL (blueprint: def-weil-integral-reduction-tower).

The natural-number index n denotes exponent n+1. We use the chosen complex
representative K and its chosen K-flat resolution q:P→K. The already recorded
chain-level maps are characterized by the sheafified pure-tensor formulas.

This overlay keeps the canonical tower interface while rebuilding its unavailable
well-definedness import in the delivery dependency packet.
The bounded integral constructibility interface imports this same definition through
a paired source overlay. This keeps its canonical coefficient and K-flat interfaces
consistent when published compiled artifacts lag behind their recorded sources.
The integral triangulation statement compiles this same canonical interface in a
paired source packet to retain its recorded independent coefficient universes.
-/

@[expose] public section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The inverse system of the restricted termwise reductions of P, with transitions
[id⊗ρ_n]. For a K-flat resolution of K this represents Res_n(K⊗ᴸA_{E,n+1}).
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def integralReductionTower
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    ℕᵒᵖ ⥤ completedIntegralDerivedCategory l E Y D hl :=
  Functor.ofOpSequence
    (X := fun n => DerivedCategory.Q.obj (integralTowerComplex l E Y D hl n P))
    (fun n =>
    DerivedCategory.Q.map (integralTowerTransition l E Y D hl P n))

/-- The map c_n=[q]⁻¹≫[γ_n] to the reduction at exponent n+1, where γ_n(x)=x⊗1.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def integralReductionTowerMap
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) (n : ℕ) :
    DerivedCategory.Q.obj K ⟶ (integralReductionTower l E Y D hl P).obj (op n) :=
  (integralTowerAugmentationIso l E Y D hl q hq).inv ≫
    DerivedCategory.Q.map (integralTowerUnit l E Y D hl P n)

/-- The maps from K are compatible with every arrow in the reduction tower.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower).
Proof: the defining pure-tensor formulas give τ_n γ_(n+1)=γ_n on sections,
since the coefficient reduction sends 1 to 1. The universal property of
sheafification and equality degree by degree give equality of chain maps.
Localization preserves composition. Precompose with [q]⁻¹ to obtain
c_(n+1)≫t_n=c_n. Every arrow m→n of the opposite natural-number category is
a finite composite of consecutive arrows (the identity when m=n), so induction
on m-n gives the stated compatibility for all arrows. -/
theorem integralReductionTowerMap_naturality
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K)).map f ≫
        integralReductionTowerMap l E Y D hl q hq j.unop =
      integralReductionTowerMap l E Y D hl q hq i.unop ≫
        (integralReductionTower l E Y D hl P).map f := by
  have hcomp (n : ℕ) :
      integralTowerUnit l E Y D hl P (n + 1) ≫ integralTowerTransition l E Y D hl P n =
        integralTowerUnit l E Y D hl P n := by
    have hunit : integralTowerUnitCondition l E Y D hl P (integralTowerUnit l E Y D hl P) :=
      (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec.1
    have hstep : integralTowerTransitionCondition l E Y D hl P
        (integralTowerTransition l E Y D hl P) :=
      (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec.2
    ext a U x
    change (((integralTowerTransition l E Y D hl P n).f a).val.app U)
      ((((integralTowerUnit l E Y D hl P (n + 1)).f a).val.app U) x) =
      (((integralTowerUnit l E Y D hl P n).f a).val.app U) x
    erw [hunit (n + 1) a U x, hunit n a U x]
    simpa only [map_one] using hstep n a U 1 x
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let α : (Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K) ⟶
      integralReductionTower l E Y D hl P :=
    NatTrans.ofOpSequence (fun n ↦ integralReductionTowerMap l E Y D hl q hq n)
      (by
        intro n
        simp only [Functor.const_obj_map, integralReductionTower,
          Functor.ofOpSequence_map_homOfLE_succ, integralReductionTowerMap,
          Category.assoc, ← Functor.map_comp, hcomp]
        exact Category.id_comp _)
  exact α.naturality f

/-- The reduction tower together with its compatible maps from K, as a cone.
The comparison isomorphisms and both independence identities for another resolution
are integralTowerComparison and integralReductionTowerWellDefined, respectively.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def integralReductionTowerCone
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    Cone (integralReductionTower l E Y D hl P) where
  pt := DerivedCategory.Q.obj K
  π :=
    { app := fun n => integralReductionTowerMap l E Y D hl q hq n.unop
      naturality := integralReductionTowerMap_naturality l E Y D hl q hq }

end WeilConjectures
