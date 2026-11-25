/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaExtendScalars

/-!
# The coefficient change `𝒪_E ⟶ E` of the projection formula, unfolded

The private theorem
`isIso_projectionMap_app_app_padicSubfield_of_padicIntegers_aux`
is the coefficient change with the coefficient rings written out, for the proofs that use it
through `import all`. Being private, its large statement is skipped by the export of
library-suggestion data; the public statement uses the names of `ProjectionFormulaExtendScalars`.
-/

-- The module is private on purpose: its statement is too large for the library-suggestion export.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section ExtendScalars

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f]

/-- `isIso_projectionMap_app_app_padicSubfield_of_padicIntegers` with the coefficient rings
written out, for `isIso_projectionMap_padicAlgClRingObj_of_integral`. It is private, so its
large statement is skipped by the export of library-suggestion data. -/
private theorem isIso_projectionMap_app_app_padicSubfield_of_padicIntegers_aux
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (M₀ : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (n m : ℤ) (hn : K₀.IsGE n)
    (hm : (((curriedTensor _).obj K₀).obj
      (((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).leftDerivedFunctor.obj M₀)).IsGE m)
    (h : IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E.1) f).app K₀).app M₀)) :
    IsIso (((projectionMap (Profinite.continuousMapRingObj E.1) f).app
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        X)).leftDerivedFunctor.obj K₀)).app
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        Y)).leftDerivedFunctor.obj M₀)) := by
  have e := isIso_projectionMap_app_app_extendScalars_of_isIso
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) f K₀ M₀
    (by exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f K₀ n)
    (by exact_mod_proofs (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f
      (((curriedTensor _).obj K₀).obj
        (((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).leftDerivedFunctor.obj M₀)) m))
    (by exact_mod_proofs h)
  exact_mod_proofs e

end ExtendScalars

end AlgebraicGeometry.ProEtale.CondensedRing
