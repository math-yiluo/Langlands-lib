/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor
/-! # Detecting maps into a complete object with finite shifted reduction Hom

Source: Stacks, Lemma map-into-Rlim, and the finite-group Mittag-Leffler argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
local instance instEssentiallySmallProEt_derivedCompleteFiniteReductionDetection
    (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
local instance instHasSheafifyProEt_derivedCompleteFiniteReductionDetection (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, 0} W
local instance instWEqualsLocallyBijective_derivedCompleteFiniteReductionDetection
    (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, 0} W
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted

private theorem reduction_cone_isHomotopyLimit
    {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {F : ℕᵒᵖ ⥤ A} (c : Cone F) [HasProduct (fun n ↦ F.obj (Opposite.op n))]
    (δ : (∏ᶜ fun n ↦ F.obj (Opposite.op n)) ⟶ c.pt⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op)
      c.pt (Pi.lift (fun n ↦ c.π.app (Opposite.op n))) δ) : IsHomotopyLimit c := by
  refine ⟨_, productIsProduct _, δ, ?_⟩
  have h₁ : Fan.IsLimit.lift (productIsProduct (fun n ↦ F.obj (Opposite.op n)))
      (fun n ↦ c.π.app (Opposite.op n)) =
        Pi.lift (fun n ↦ c.π.app (Opposite.op n)) := by
    apply Pi.hom_ext
    intro n
    exact (Fan.IsLimit.fac _ _ n).trans
      (Pi.lift_comp_π (fun n ↦ c.π.app (Opposite.op n)) n).symm
  have h₂ : towerShift (F := F) (productIsProduct (fun n ↦ F.obj (Opposite.op n))) =
      towerProductShift (fun n ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    simp only [towerShift, towerProductShift, Pi.lift_comp_π]
    exact Fan.IsLimit.fac _ _ n
  rw [h₁, h₂]
  exact h

/-- Scalar reductions detect maps into a derived-complete object when the shifted
Hom sets into its restricted reductions are finite.

Source: Stacks, Lemma map-into-Rlim; the finite-group Mittag-Leffler argument.
(blueprint: lem-sf-derived-complete-finite-reduction-detection).

Proof: the defining completeness triangle makes the canonical reduction cone a
homotopy limit. The given finite shifted Hom sets kill the Milnor kernel.
Naturality of the scalar-adjunction units turns equality after scalar extension
into equality of all composites with the cone legs. Milnor injectivity then gives
equality of the original maps. No constructibility or hypothesis on the scheme
is needed beyond the displayed finiteness and completeness assumptions. -/
theorem derivedComplete_finiteReduction_ext
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) {P Q : DerivedCategory (scalarReductionSource.{u, u} l E W)}
    (hQ : IsSfDerivedComplete l E W Q)
    (hfin : ∀ n : ℕ, Finite
      (P⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E W n).obj Q))
    (a b : P ⟶ Q)
    (h : ∀ n : ℕ, (scalarReductionDerivedExtension.{u, u} l E W n).map a =
      (scalarReductionDerivedExtension.{u, u} l E W n).map b) : a = b := by
  obtain ⟨hp, δ, hδ⟩ := hQ
  let := hp
  let T := sfIntegralReductionTower l E W Q
  let c := sfIntegralReductionCone l E W Q
  let : HasProduct (fun n ↦ T.obj (Opposite.op n)) := hp
  have hc : IsHomotopyLimit c := by
    apply reduction_cone_isHomotopyLimit (δ := δ)
    change IsDerivedLimitTriangle
      (K := fun n ↦ (sfDerivedReductionRestricted l E W n).obj Q)
      (fun n ↦ T.map (homOfLE n.le_succ).op)
      Q (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app Q)) δ
    simpa only [T, sfIntegralReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using hδ
  let (n : ℕ) : Finite (P⟦(1 : ℤ)⟧ ⟶ T.obj (Opposite.op n)) := hfin n
  apply (hc.bijective_milnorMap P).injective
  apply Subtype.ext
  funext n
  change a ≫ (sfDerivedReductionUnit l E W n).app Q =
    b ≫ (sfDerivedReductionUnit l E W n).app Q
  have ha := (sfDerivedReductionUnit l E W n).naturality a
  have hb := (sfDerivedReductionUnit l E W n).naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at ha hb
  rw [ha, hb, h n]

end WeilConjectures
