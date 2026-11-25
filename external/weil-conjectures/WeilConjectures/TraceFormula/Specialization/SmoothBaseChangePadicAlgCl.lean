/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchange

/-!

# Smooth base change with `ℚ̄_ℓ`-coefficients for quasi-compact quasi-separated pushforward

For a cartesian square `e ≫ g = h ≫ p` with `p` smooth and `g` quasi-compact quasi-separated
from a noetherian scheme, the base change morphism `Lp^* Rg_* ⟶ Rh_* Le^*` with
`ℚ̄_ℓ`-coefficients is invertible at pullbacks of bounded constructible complexes
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_smooth`), by
integral models and integral smooth base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Smooth base change with `ℚ̄_ℓ`-coefficients for quasi-compact quasi-separated pushforward**:
for a cartesian square `e ≫ g = h ≫ p` of quasi-compact quasi-separated schemes with `p` smooth,
`g` quasi-compact and quasi-separated, `W` noetherian and `ℓ` invertible on `S`, the base change
morphism `Lp^* Rg_* ⟶ Rh_* Le^*` is invertible at `Lε^* K` for every bounded constructible
`ℚ̄_ℓ`-complex `K` on a noetherian scheme `T` and every `ε : W ⟶ T`. By integral models, this is
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`. -/
theorem isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_smooth {S W X Y T : Scheme.{u}}
    (p : X ⟶ S) {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X} [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] [IsNoetherian W]
    [QuasiCompact h] [QuasiSeparated h] [TopologicalSpace.NoetherianSpace T]
    (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(S, ⊤))) (ε : W ⟶ T)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hK : boundedConstructible _ K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq.toCommSq).app
      ((L((ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) :=
  isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_integral ℓ sq.toCommSq ε hK
    fun E _ hK₀ ↦ isIso_baseChangeMap_app_padicIntegers_of_smooth ℓ E p sq hℓ _
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hK₀)

end AlgebraicGeometry.ProEtale.CondensedRing
