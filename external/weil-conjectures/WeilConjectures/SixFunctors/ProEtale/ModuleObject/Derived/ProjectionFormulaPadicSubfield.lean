/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaExtendScalars

/-!
# The projection formula and the coefficient change `𝒪_E ⟶ E`

If the projection map with coefficients `𝒪_E` is invertible at `(K₀, M₀)`, with `K₀` and
`K₀ ⊗ᴸ Lf^* M₀` bounded below, then so is the projection map with coefficients `E` at
`(E ⊗ᴸ K₀, E ⊗ᴸ M₀)`
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicSubfield_of_padicIntegers`).

The concrete coefficient rings carry instance arguments elaborated in different contexts, which
differ by proofs only; the tactic `exact_mod_proofs` bridges them.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section ExtendScalars

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f]

/-- **The projection formula and the coefficient change `𝒪_E ⟶ E`**: for a quasi-compact
quasi-separated `f`, if the projection map with coefficients `𝒪_E` is invertible at `(K₀, M₀)`,
with `K₀` and `K₀ ⊗ᴸ Lf^* M₀` bounded below, then the projection map with coefficients `E` is
invertible at `(E ⊗ᴸ K₀, E ⊗ᴸ M₀)`. -/
theorem isIso_projectionMap_app_app_padicSubfield_of_padicIntegers
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersRingObj ℓ E) X)))
    (M₀ : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.integersRingObj ℓ E) Y)))
    (n m : ℤ) (hn : K₀.IsGE n)
    (hm : (((curriedTensor _).obj K₀).obj
      (((f)^*⟦Profinite.integersRingObj ℓ E⟧).leftDerivedFunctor.obj M₀)).IsGE m)
    (h : IsIso (((projectionMap (Profinite.integersRingObj ℓ E) f).app K₀).app M₀)) :
    IsIso (((projectionMap (Profinite.subfieldRingObj ℓ E) f).app
      ((Mod.extendScalars (coefficientMap (Profinite.integersRingObjToSubfieldRingObj ℓ E)
        X)).leftDerivedFunctor.obj K₀)).app
      ((Mod.extendScalars (coefficientMap (Profinite.integersRingObjToSubfieldRingObj ℓ E)
        Y)).leftDerivedFunctor.obj M₀)) := by
  have e := isIso_projectionMap_app_app_extendScalars_of_isIso
    (Profinite.integersRingObjToSubfieldRingObj ℓ E) f K₀ M₀
    (by exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f K₀ n)
    (by exact_mod_proofs (@isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ _ E _ _ f _ _ _ m hm))
    (by exact_mod_proofs h)
  exact_mod_proofs e

end ExtendScalars

end AlgebraicGeometry.ProEtale.CondensedRing
