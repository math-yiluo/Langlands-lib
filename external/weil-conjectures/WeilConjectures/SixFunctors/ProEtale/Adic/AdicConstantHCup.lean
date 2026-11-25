/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralAdicCup

/-!
# The cup product on `Hⁿ(S_proét, ℚ̄_ℓ)`

Let `S` be a quasi-compact quasi-separated scheme whose cohomology groups `Hᵏ(S, ℤ/ℓᵐ)` are finite.
Since `Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗_{ℤ_ℓ} Hⁿ(S, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.isBaseChange_integralToAdicConstantH`), the cup product of integral
cohomology (`AlgebraicGeometry.ProEtale.integralAdicHCup`) extends uniquely to a `ℚ̄_ℓ`-bilinear
cup product `⌣ : Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ Hⁱ⁺ʲ(S, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.adicConstantHCup`), compatible with `ι : Hⁿ(S, ℤ_ℓ) ⟶ Hⁿ(S, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.adicConstantHCup_integralToAdicConstantH`). It is graded commutative
and compatible with the pullback along an automorphism of a connected `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]

/-- The cup product with a fixed integral class, extended `ℚ̄_ℓ`-linearly in the second
variable. -/
noncomputable def integralAdicHCupBaseChange (hfin : ∀ m k, Finite (FiniteAdicH S l m k))
    {i j k : ℕ} (h : i + j = k) :
    IntegralAdicH S l i →ₗ[ℤ_[l]] AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k where
  toFun x := (isBaseChange_integralToAdicConstantH l S j).lift
    ((integralToAdicConstantH l S k).comp (integralAdicHCup l S hfin h x))
  map_add' x x' := (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun y ↦ by
    rw [LinearMap.add_apply, IsBaseChange.lift_eq, IsBaseChange.lift_eq, IsBaseChange.lift_eq,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_add,
      LinearMap.add_apply, map_add]
  map_smul' c x := (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun y ↦ by
    rw [LinearMap.smul_apply, IsBaseChange.lift_eq, IsBaseChange.lift_eq, LinearMap.comp_apply,
      LinearMap.comp_apply, map_smul, LinearMap.smul_apply, map_smul, RingHom.id_apply]

/-- The **cup product** `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ Hᵏ(S, ℚ̄_ℓ)`, `i + j = k`: the `ℚ̄_ℓ`-bilinear
extension of the cup product of integral cohomology along `Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗ Hⁿ(S, ℤ_ℓ)`. -/
noncomputable def adicConstantHCup (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) {i j k : ℕ}
    (h : i + j = k) :
    AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
      AdicConstantH l S k :=
  (isBaseChange_integralToAdicConstantH l S i).lift (integralAdicHCupBaseChange l S hfin h)

variable (hfin : ∀ m k, Finite (FiniteAdicH S l m k))

/-- The cup product extends the cup product of integral cohomology. -/
theorem adicConstantHCup_integralToAdicConstantH {i j k : ℕ} (h : i + j = k)
    (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) :
    adicConstantHCup l S hfin h (integralToAdicConstantH l S i x)
        (integralToAdicConstantH l S j y) =
      integralToAdicConstantH l S k (integralAdicHCup l S hfin h x y) := by
  rw [adicConstantHCup, IsBaseChange.lift_eq]
  exact IsBaseChange.lift_eq _ _ y

/-- Two `ℚ̄_ℓ`-bilinear maps on `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ)` agreeing on integral classes agree. -/
lemma adicConstantH_bilinear_ext {i j : ℕ} {Q : Type*}
    [AddCommGroup Q] [Module (PadicAlgCl l) Q]
    {f g : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l] Q}
    (hfg : ∀ x y, f (integralToAdicConstantH l S i x) (integralToAdicConstantH l S j y) =
      g (integralToAdicConstantH l S i x) (integralToAdicConstantH l S j y))
    (x : AdicConstantH l S i) (y : AdicConstantH l S j) : f x y = g x y :=
  LinearMap.congr_fun₂ ((isBaseChange_integralToAdicConstantH l S i).algHom_ext _ _ fun x ↦
    (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun y ↦ hfg x y) x y

/-- **Graded commutativity**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem adicConstantHCup_comm {i j k : ℕ} (h : i + j = k) (x : AdicConstantH l S i)
    (y : AdicConstantH l S j) :
    adicConstantHCup l S hfin ((add_comm j i).trans h) y x =
      ((i : ℤ) * j).negOnePow • adicConstantHCup l S hfin h x y := by
  rw [Units.smul_def]
  refine adicConstantH_bilinear_ext l S
    (f := (adicConstantHCup l S hfin ((add_comm j i).trans h)).flip)
    (g := (((i : ℤ) * j).negOnePow : ℤ) • adicConstantHCup l S hfin h) (fun x y ↦ ?_) x y
  rw [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    adicConstantHCup_integralToAdicConstantH, adicConstantHCup_integralToAdicConstantH,
    integralAdicHCup_comm, Units.smul_def, map_zsmul]

/-- The pullback along an automorphism of a connected `S` is multiplicative. -/
theorem adicConstantHPullback_adicConstantHCup [ConnectedSpace S] (e : S ≅ S) {i j k : ℕ}
    (h : i + j = k) (x : AdicConstantH l S i) (y : AdicConstantH l S j) :
    adicConstantHPullback l e k (adicConstantHCup l S hfin h x y) =
      adicConstantHCup l S hfin h (adicConstantHPullback l e i x) (adicConstantHPullback l e j y) :=
  adicConstantH_bilinear_ext l S
    (f := (adicConstantHCup l S hfin h).compr₂ (adicConstantHPullback l e k))
    (g := ((adicConstantHCup l S hfin h).comp (adicConstantHPullback l e i)).compl₂
      (adicConstantHPullback l e j)) (fun x y ↦ by
      rw [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        adicConstantHCup_integralToAdicConstantH, adicConstantHPullback_integralToAdicConstantH,
        adicConstantHPullback_integralToAdicConstantH,
        adicConstantHPullback_integralToAdicConstantH, adicConstantHCup_integralToAdicConstantH,
        integralAdicHPullback_integralAdicHCup]) x y

end AlgebraicGeometry.ProEtale
