/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The normalized sheet-sum formula for an internal finite etale trace

Source: the stratified lattice proof, "Pushing down by the trace".
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

/-- A finite splitting chart, allowing the empty splitting.
Source: Stacks Project, Tag 04HN.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
structure FiniteEtaleModuleChart {X U : Scheme.{u}} (p : U ⟶ X) where
  base : Scheme.{u}
  map : base ⟶ X
  weaklyEtale : WeaklyEtale map
  degree : ℕ
  sheet : Fin degree → (base ⟶ U)
  over : ∀ j, sheet j ≫ p = map
  splits : Nonempty (IsColimit (Cofan.mk (pullback p map)
    (fun j ↦ pullback.lift (sheet j) (𝟙 base) (by simpa using over j))))

attribute [instance] FiniteEtaleModuleChart.weaklyEtale

/-- The canonical sheet comparison has a uniquely specified value.
Source: the inverse-image composition comparison.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
theorem finiteEtaleTraceSheetComparison_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    ∃ a : upperStar Λ g ≅ upperStar Λ p ⋙ upperStar Λ t,
      a = (eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p := by
  exact ⟨_, rfl⟩

/-- The canonical sheet comparison, frozen using its proved singleton specification.
Its exact equation below fixes all its components. This avoids kernel reduction
through the large composite adjunction when components are compared.
Source: the inverse-image composition comparison.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
@[irreducible]
def finiteEtaleTraceSheetComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    upperStar Λ g ≅ upperStar Λ p ⋙ upperStar Λ t :=
  Classical.choose (finiteEtaleTraceSheetComparison_exists Λ p g t w)

/-- The frozen comparison is exactly the original canonical composition comparison.
Source: the proved specification above.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
theorem finiteEtaleTraceSheetComparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    finiteEtaleTraceSheetComparison Λ p g t w =
      (eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p := by
  unfold finiteEtaleTraceSheetComparison
  exact Classical.choose_spec (finiteEtaleTraceSheetComparison_exists Λ p g t w)

/-- The actual sum of the normalized counit projections on a finite list of sheets.
Source: blueprint, stratified lattice proof, local computation.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
@[irreducible]
def finiteEtaleTraceSheetSum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Y ⟶ X) (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g) :
    (upperStar Λ g).obj ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ⟶
      (upperStar Λ g).obj P :=
  ∑ j : Fin n,
    (finiteEtaleTraceSheetComparison Λ p g (t j) (w j)).hom.app
        ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ≫
      (upperStar Λ (t j)).map
        ((upperStarLowerStarAdjunction Λ p).counit.app ((upperStar Λ p).obj P)) ≫
      (finiteEtaleTraceSheetComparison Λ p g (t j) (w j)).inv.app P

/-- The trace becomes the sum of canonical sheet projections on every split chart.
Each projection is formed from the pullback composition comparison and the actual
pullback/direct-image counit; thus this condition fixes the normalization of trace.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
def FiniteEtaleTraceFormula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (τ : (lowerStar Λ p).obj ((upperStar Λ p).obj P) ⟶ P) : Prop :=
  ∀ c : FiniteEtaleModuleChart p,
    (upperStar Λ c.map).map τ =
      finiteEtaleTraceSheetSum Λ p P c.map c.degree c.sheet c.over

end AlgebraicGeometry.ProEtale.CondensedRing
