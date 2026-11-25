/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowHigherDirectImageLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratum
public import WeilConjectures.SixFunctors.ProEtale.Adic.TowerLimitModule

/-!
# The limit of the stalks over a stratum is a finite `𝒪_E`-module with its `ℓ`-adic topology

Let `j : S ⟶ Y` be a stratum over which the higher direct image `Rᵏg_* (Λ ⧸ ℓ)` is finite locally
constant, `Λ = Shrink 𝒪_E`, and `Gₙ` the stalks at a geometric point of `S` of the restricted
tower `n ↦ j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))` (whose limit is the coefficient group of the integral
identification `AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum`).
Then the group `lim_n Gₙ` of compatible families, with its limit topology, is a finite
`𝒪_E`-module carrying the module (`ℓ`-adic) topology
(`AlgebraicGeometry.ProEtale.towerLimit_isModuleTopology_integersStratum`): it is finite by the
Bockstein argument
(`AlgebraicGeometry.Etale.finite_limit_sheafFiber_upperStar_higherDirectImageQuotPowTower`)
and `𝒪_E` acts on `Gₙ`, killed by `ℓⁿ`, through the discrete quotient `𝒪_E ⧸ ℓⁿ`
(`PadicAlgCl.isLocallyConstant_shrinkRingEquiv_smul`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y)

/-- **The limit of the stalks over a stratum carries the `ℓ`-adic topology.** If over the stratum
`j : S ⟶ Y` the higher direct image `Rᵏg_* (Λ ⧸ ℓ)_T` of sheaves of `Λ ⧸ ℓ`-modules is finite
locally constant and the restricted levels `j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))` are `IsSetFLC`, then the
compatible families of their stalks at a geometric point of `S`, with the limit topology, form a
finite `𝒪_E`-module with its module topology. -/
theorem towerLimit_isModuleTopology_integersStratum {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (k : ℕ)
    (h : Etale.flcProperty S ((Etale.upperStar (ModuleCat.{u + 1}
      (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E)) j).obj
        (((Etale.lowerStar (ModuleCat.{u + 1}
          (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E)) g).rightDerived k).obj
            (Etale.constantQuotSheaf (integersShrink.{u} l E) (integersShrinkIdeal.{u} l E) T))))
    (hH' : ∀ n : ℕ, IsSetFLC ((Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E))
      j).obj ((Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g
        k).obj (op n)))) :
    let G := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
      Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) j ⋙
        (pointSmallEtale s).sheafFiber
    have (n : ℕ) : Small.{0} (G.obj (op n)) :=
      have : Finite (G.obj (op n)) := (hH' n).finite_sheafFiber s
      inferInstance
    letI := normedFieldOfAlgebra l E
    letI := ModuleCat.towerLimitModuleOf G (shrinkRingEquiv.{0, u} l E)
    IsModuleTopology (integers l E) (ModuleCat.towerLimit G) := by
  intro G _
  let := normedFieldOfAlgebra l E
  have := isTopologicalRing_integers l E
  have := compactSpace_integers l E
  have := Etale.finite_limit_sheafFiber_upperStar_higherDirectImageQuotPowTower
    (integersShrinkIdeal.{u} l E) g (natCast_mem_nonZeroDivisors_shrink l E) rfl j s k h
  exact ModuleCat.towerLimit_isModuleTopology G (shrinkRingEquiv.{0, u} l E) fun n m ↦
    isLocallyConstant_shrinkRingEquiv_smul l E n m
      (Etale.smul_eq_zero_sheafFiber_upperStar_higherDirectImageQuotPowTower_obj _ g j s k n
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) m)

end AlgebraicGeometry.ProEtale
