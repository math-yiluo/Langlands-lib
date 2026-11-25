/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaExtendScalars

/-!
# The projection formula and the coefficient change `E ⟶ ℚ̄_ℓ`

If the projection map with coefficients `E` is invertible at `(K, M)`, with `K` and
`K ⊗ᴸ Lf^* M` bounded below, then so is the projection map with coefficients `ℚ̄_ℓ` at
`(ℚ̄_ℓ ⊗ᴸ K, ℚ̄_ℓ ⊗ᴸ M)`
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield`).

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

/-- **The projection formula and the coefficient change `E ⟶ ℚ̄_ℓ`**: for a quasi-compact
quasi-separated `f`, if the projection map with coefficients `E` is invertible at `(K, M)`, with
`K` and `K ⊗ᴸ Lf^* M` bounded below, then the projection map with coefficients `ℚ̄_ℓ` is
invertible at `(ℚ̄_ℓ ⊗ᴸ K, ℚ̄_ℓ ⊗ᴸ M)`. -/
theorem isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.subfieldRingObj ℓ E) X)))
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.subfieldRingObj ℓ E) Y)))
    (n m : ℤ) (hn : K.IsGE n)
    (hm : (((curriedTensor _).obj K).obj
      (((f)^*⟦Profinite.subfieldRingObj ℓ E⟧).leftDerivedFunctor.obj M)).IsGE m)
    (h : IsIso (((projectionMap (Profinite.subfieldRingObj ℓ E) f).app K).app M)) :
    IsIso (((projectionMap (Profinite.padicAlgClRingObj ℓ) f).app
      ((Mod.extendScalars (coefficientMap (Profinite.subfieldRingObjToPadicAlgClRingObj ℓ E)
        X)).leftDerivedFunctor.obj K)).app
      ((Mod.extendScalars (coefficientMap (Profinite.subfieldRingObjToPadicAlgClRingObj ℓ E)
        Y)).leftDerivedFunctor.obj M)) := by
  have e := isIso_projectionMap_app_app_extendScalars_of_isIso
    (Profinite.subfieldRingObjToPadicAlgClRingObj ℓ E) f K M
    (by exact_mod_proofs
      isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E f K n)
    (by exact_mod_proofs
      (@isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ _ E _ _ f _ _ _ m hm))
    (by exact_mod_proofs h)
  exact_mod_proofs e

end ExtendScalars


end AlgebraicGeometry.ProEtale.CondensedRing
