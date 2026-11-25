/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction

/-!
# Reduction modulo `ℓⁿ` commutes with internal homs

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E`, and `X` a scheme. The derived
reduction modulo `ℓⁿ`,
```
(𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{(𝒪_E ⧸ ℓⁿ)_X}),
```
the derived extension of scalars along `ProEtale.integersModPowReduction`, monoidal through
`Functor.leftDerivedFunctorMonoidal`, commutes with internal homs: for all `A`, `B` the
comparison
```
RHom(A, B) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶ RHom(A ⊗ᴸ 𝒪_E ⧸ ℓⁿ, B ⊗ᴸ 𝒪_E ⧸ ℓⁿ)
```
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedIntegersModPowReduction`; blueprint
`proposition-six-operations-change-coefficients--7`,
`proposition-six-operations-change-coefficients` (2) for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`).

Since `0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` is short exact
(`ProEtale.shortExact_integersModPowReduction`), this is an instance of
`CategoryTheory.Mod.isIso_ihomComparison_leftDerivedExtendScalars`: by the projection formula,
`RHom(A, B) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ≅ RHom(A, B) ⊗ᴸ_{𝒪_E} (𝒪_E ⧸ ℓⁿ)[0]`, and `(𝒪_E ⧸ ℓⁿ)[0]` is a dualizable
`𝒪_E`-complex, having the finite free resolution `𝒪_E --ℓⁿ--> 𝒪_E`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)
  (X : Scheme.{u})

/-- **Reduction modulo `ℓⁿ` commutes with internal homs** (blueprint
`proposition-six-operations-change-coefficients--7`): for `A, B ∈ D(Mod_{𝒪_{E,X}})`, the comparison
`RHom(A, B) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶ RHom(A ⊗ᴸ 𝒪_E ⧸ ℓⁿ, B ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` of the derived reduction, monoidal
through `Functor.leftDerivedFunctorMonoidal`, is an isomorphism. -/
theorem isIso_ihomComparison_leftDerivedIntegersModPowReduction
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
    letI := (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctorMonoidal
    IsIso ((Functor.LaxMonoidal.ihomComparison
      L(Mod.extendScalars (integersModPowReduction X ℓ E n)) A).app B) :=
  Mod.isIso_ihomComparison_leftDerivedExtendScalars _ _
    (zsmul_id_comp_integersModPowReduction X ℓ E n) (shortExact_integersModPowReduction X ℓ E n)
    A B


/-- `ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedIntegersModPowReduction` for any
monoidal structure on the derived reduction which is equal to that of
`Functor.leftDerivedFunctorMonoidal`, for instance a named local instance unfolding to it. Applied
with `h := rfl`, this avoids a slow unification of such a named instance with the unfolded one in
the statement. -/
theorem isIso_ihomComparison_leftDerivedIntegersModPowReduction_of_eq
    (inst : L(Mod.extendScalars (integersModPowReduction X ℓ E n)).Monoidal)
    (h : inst = (letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctorMonoidal))
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    letI := inst
    IsIso ((Functor.LaxMonoidal.ihomComparison
      L(Mod.extendScalars (integersModPowReduction X ℓ E n)) A).app B) := by
  subst h
  exact isIso_ihomComparison_leftDerivedIntegersModPowReduction ℓ E n X A B

end AlgebraicGeometry.ProEtale.CondensedRing
