/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ExtensionTowerStalkLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratumTopology

/-!
# The limit of the stalks of a tower of reductions is a finite `𝒪_E`-module

Let `Λ = Shrink 𝒪_E` and `M : ℕᵒᵖ ⥤ Sh(T_ét, Λ)` a tower of reductions (`ℓⁿ⁺¹ Mₙ = 0`, short exact
sequences `0 ⟶ Mₙ --ιₙ--> Mₙ₊₁ ⟶ M₀ ⟶ 0` with `ιₙ ∘ tₙ = ℓ` and `tₙ ∘ ιₙ = ℓ`), for instance the
reductions of an `𝒪_E`-lattice in a lisse `ℓ`-adic sheaf. On a stratum `j : S ⟶ Y` over which
the `j^* Hᵏ(Rg_* Mₙ)` are `IsSetFLC`, the compatible families `lim_n Gₙ` of their stalks at a
geometric point, with the limit topology, form a finite `𝒪_E`-module
(`AlgebraicGeometry.ProEtale.towerLimit_finite_moduleTowerStratum`) carrying its module
(`ℓ`-adic) topology (`AlgebraicGeometry.ProEtale.towerLimit_isModuleTopology_moduleTowerStratum`).

This is the coefficient module of the integral identification
`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_moduleTowerStratum`, and generalises
`AlgebraicGeometry.ProEtale.towerLimit_isModuleTopology_integersStratum` from the constant tower.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)
  (M : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (integersShrink.{u} l E)))
  (ι : ∀ n : ℕ, M.obj (op n) ⟶ M.obj (op (n + 1)))
  (hιt : ∀ n : ℕ, M.map (homOfLE (Nat.le_add_right n 1)).op ≫ ι n =
    (l : integersShrink.{u} l E) • 𝟙 _)
  (htι : ∀ n : ℕ, ι n ≫ M.map (homOfLE (Nat.le_add_right n 1)).op =
    (l : integersShrink.{u} l E) • 𝟙 _)
  (w : ∀ n : ℕ, ι n ≫ M.map (homOfLE (Nat.zero_le (n + 1))).op = 0)
  (hS : ∀ n : ℕ, (ShortComplex.mk _ _ (w n)).ShortExact)
  (hkill : ∀ n : ℕ, (l : integersShrink.{u} l E) ^ (n + 1) • 𝟙 (M.obj (op n)) = 0) (k : ℤ)
  (hH : ∀ n : ℕ, IsSetFLC ((Etale.upperStarHomologyRightDerived g j k).obj (M.obj (op n))))

include hιt htι hS hkill hH in
/-- **The limit of the stalks over a stratum is a finite `𝒪_E`-module**, for a tower of
reductions whose restricted higher direct images are `IsSetFLC`. -/
theorem towerLimit_finite_moduleTowerStratum :
    let G := M ⋙ Etale.upperStarHomologyRightDerived g j k ⋙ (pointSmallEtale s).sheafFiber
    have (n : ℕ) : Small.{0} (G.obj (op n)) :=
      have : Finite (G.obj (op n)) := (hH n).finite_sheafFiber s
      inferInstance
    letI := ModuleCat.towerLimitModuleOf G (shrinkRingEquiv.{0, u} l E)
    Module.Finite (integers l E) (ModuleCat.towerLimit G) := by
  intro G _
  have := Etale.finite_limit_sheafFiber_upperStar_homology_rightDerived_of_tower g j s M ι hιt
    htι w hS hkill k fun n ↦ (hH n).finite_sheafFiber s
  exact ModuleCat.towerLimit_finite_of_ringEquiv G (shrinkRingEquiv.{0, u} l E)

include hιt htι hS hkill hH in
/-- **The limit of the stalks over a stratum carries the `ℓ`-adic topology**, for a tower of
reductions whose restricted higher direct images are `IsSetFLC`: the compatible families of the
stalks at a geometric point of `S`, with the limit topology, form a finite `𝒪_E`-module with
its module topology. -/
theorem towerLimit_isModuleTopology_moduleTowerStratum :
    let G := M ⋙ Etale.upperStarHomologyRightDerived g j k ⋙ (pointSmallEtale s).sheafFiber
    have (n : ℕ) : Small.{0} (G.obj (op n)) :=
      have : Finite (G.obj (op n)) := (hH n).finite_sheafFiber s
      inferInstance
    letI := normedFieldOfAlgebra l E
    letI := ModuleCat.towerLimitModuleOf G (shrinkRingEquiv.{0, u} l E)
    IsModuleTopology (integers l E) (ModuleCat.towerLimit G) := by
  intro G _
  let := normedFieldOfAlgebra l E
  have := isTopologicalRing_integers l E
  have := compactSpace_integers l E
  have := Etale.finite_limit_sheafFiber_upperStar_homology_rightDerived_of_tower g j s M ι hιt
    htι w hS hkill k fun n ↦ (hH n).finite_sheafFiber s
  refine ModuleCat.towerLimit_isModuleTopology G (shrinkRingEquiv.{0, u} l E) fun n m ↦
    isLocallyConstant_shrinkRingEquiv_smul l E (n + 1) m ?_
  rw [← Etale.sheafFiber_upperStarHomologyRightDerived_map_smul_apply g j s k, hkill,
    Functor.map_zero, Functor.map_zero]
  rfl

end AlgebraicGeometry.ProEtale
