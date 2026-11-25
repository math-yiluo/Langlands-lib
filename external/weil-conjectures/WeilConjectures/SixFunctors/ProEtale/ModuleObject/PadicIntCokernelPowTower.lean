/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.CokernelPowTower
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeLocal
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowCokernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison

/-!
# `ℤ_ℓ,Y` is `ℓ`-adically complete

Let `Y` be a scheme and `ℓ` a prime. The pro-étale sheaf `ℤ_ℓ,Y = p_Y^* ℤ_ℓ` is `ℓ`-adically
complete and separated: it is the limit of its reductions `ℤ_ℓ,Y/ℓⁿ`
(`AlgebraicGeometry.ProEtale.isLimitCokernelPowTowerCone`).

By `AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`, `ℤ_ℓ,Y` is the sheaf of
continuous functions `U ↦ C(U, ℤ_ℓ)`. Sectionwise, the sequence
`0 → C(U, ℤ_ℓ) --ℓⁿ--> C(U, ℤ_ℓ) → C(U, ℤ/ℓⁿ) → 0` is exact: a locally constant map to `ℤ/ℓⁿ`
lifts through a set-theoretic section `ℤ/ℓⁿ → ℤ_ℓ`, and a continuous map with values in
`ℓⁿ ℤ_ℓ` may be divided by `ℓⁿ` (`PadicInt.exists_continuousMap_pow_mul_eq`). Hence the
reductions `C(-, ℤ_ℓ) → C(-, ℤ/ℓⁿ)` are cokernels of `ℓⁿ`, and their limit is `C(-, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.isLimitPadicIntAbSheafCone`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]

/-- A continuous map `f : X → ℤ_p` vanishing modulo `pⁿ` is `pⁿ` times a continuous map. -/
lemma exists_continuousMap_pow_mul_eq (n : ℕ) (f : C(X, ℤ_[p]))
    (hf : ∀ x, toZModPow n (f x) = 0) : ∃ g : C(X, ℤ_[p]), ∀ x, (p : ℤ_[p]) ^ n * g x = f x := by
  have h (x : X) : ∃ z : ℤ_[p], f x = (p : ℤ_[p]) ^ n * z := by
    have hx : f x ∈ RingHom.ker (toZModPow n) := hf x
    rwa [ker_toZModPow, Ideal.mem_span_singleton] at hx
  have hp : ((p : ℚ_[p]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hdiv (x : X) : ‖(f x : ℚ_[p]) / (p : ℚ_[p]) ^ n‖ ≤ 1 := by
    obtain ⟨z, hz⟩ := h x
    rw [hz, coe_mul, coe_pow, coe_natCast, mul_div_cancel_left₀ _ hp]
    exact z.2
  refine ⟨⟨fun x ↦ ⟨(f x : ℚ_[p]) / (p : ℚ_[p]) ^ n, hdiv x⟩,
    ((continuous_subtype_val.comp f.continuous).div_const _).subtype_mk _⟩, fun x ↦ ?_⟩
  refine Subtype.ext ?_
  rw [coe_mul, coe_pow, coe_natCast]
  exact mul_div_cancel₀ _ hp

end PadicInt

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Multiplication by `ℓⁿ` followed by the reduction `ℤ_ℓ,Y → (ℤ/ℓⁿ)_Y` vanishes. -/
lemma pow_smul_comp_padicIntAbSheafCone_π (Y : Scheme.{u}) (n : ℕ) :
    (((ℓ ^ n : ℕ) : ℤ) • 𝟙 _) ≫
      ((sheafCompose (ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapCone
        (padicIntSheafCone Y ℓ)).π.app (op n) = 0 := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ ?_))
  ext x
  refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
  refine (map_zsmul (PadicInt.toZModPow n) _ (x.down t)).trans ?_
  rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  rfl

/-- The reduction `ℤ_ℓ,Y → (ℤ/ℓⁿ)_Y` of sheaves of continuous functions is a cokernel of `ℓⁿ`. -/
noncomputable def isColimitCokernelCoforkPadicIntAbSheafCone (Y : Scheme.{u}) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ _ (pow_smul_comp_padicIntAbSheafCone_π ℓ Y n)) := by
  refine Sheaf.isColimitCokernelCoforkOfSurjective _ _ _ (fun U x ↦ ?_) (fun U x hx ↦ ?_)
  · refine ⟨ULift.up ((⟨fun z : ZMod (ℓ ^ n) ↦ (z.val : ℤ_[ℓ]), continuous_of_discreteTopology⟩ :
      C(ZMod (ℓ ^ n), ℤ_[ℓ])).comp x.down), ULift.ext (ContinuousMap.ext fun t ↦ ?_)⟩
    exact (map_natCast (PadicInt.toZModPow n) (x.down t).val).trans (ZMod.natCast_zmod_val _)
  · obtain ⟨g, hg⟩ := PadicInt.exists_continuousMap_pow_mul_eq n x.down (fun t ↦
      congrArg (fun y : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) ↦ y.down t) hx)
    refine ⟨ULift.up g, ULift.ext (ContinuousMap.ext fun t ↦ ?_)⟩
    refine (zsmul_eq_mul (g t) _).trans ?_
    rw [Int.cast_natCast, Nat.cast_pow, hg]

/-- **`ℤ_ℓ,Y` is `ℓ`-adically complete and separated**: the condensed ring `ℤ_ℓ` pulled back to
`Y_proét` is the limit of its reductions modulo `ℓⁿ`. -/
noncomputable def isLimitCokernelPowTowerCone (Y : Scheme.{u}) :
    IsLimit (cokernelPowTowerCone
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) Y) ℓ) :=
  haveI := isIso_continuousMapComparison Y ℤ_[ℓ]
  isLimitCokernelPowTowerConeOfIso (asIso (continuousMapComparison Y ℤ_[ℓ])).symm
    (isLimitCokernelPowTowerConeOfIsColimit _ _
      (isColimitCokernelCoforkPadicIntAbSheafCone ℓ Y) (isLimitPadicIntAbSheafCone Y ℓ))

end AlgebraicGeometry.ProEtale
