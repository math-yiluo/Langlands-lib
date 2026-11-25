/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear

/-!
# Multiplication by nonzero integers on `ℚ̲̄_ℓ`-module objects is cancellable

The constant global sections `ℚ̄_ℓ →+* Γ ℚ̲̄_ℓ` (`Profinite.PadicAlgCl.constRingHom`) make the
category of `ℚ̲̄_ℓ`-module objects on a scheme `X` linear over the characteristic zero field
`ℚ̄_ℓ` (`ProEtale.CondensedRing.modLinear`), hence so is its derived category. Since `n ≠ 0` is
invertible in `ℚ̄_ℓ`, multiplication by `n` on morphisms of the derived category is cancellable
(`ProEtale.CondensedRing.nsmul_cancel_padicAlgClRingObj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- In the derived category of `ℚ̲̄_ℓ`-module objects on `X`, multiplication by a nonzero natural
number on morphisms is cancellable. -/
theorem nsmul_cancel_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) {n : ℕ}
    (hn : n ≠ 0)
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))} {f g : K ⟶ L}
    (h : n • f = n • g) : f = g := by
  let _ := modLinear _ (Profinite.PadicAlgCl.constRingHom.{u} ℓ) X
  have hn' : (n : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← one_smul (PadicAlgCl ℓ) f, ← one_smul (PadicAlgCl ℓ) g, ← inv_mul_cancel₀ hn', mul_smul,
    mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h]

end AlgebraicGeometry.ProEtale.CondensedRing
