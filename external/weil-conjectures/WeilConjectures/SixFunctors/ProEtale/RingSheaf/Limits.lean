/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ExtensionZeroProducts
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.Defs

/-!
# Limits and the open–closed operations on module sheaves over a sheaf of rings

Let `X` be quasi-compact and quasi-separated, `j : U ⟶ X` a quasi-compact open immersion with
closed complement `i : Z ⟶ X`, and `B` a sheaf of `R`-algebras on `X_proét`. On `B`-module
sheaves (blueprint `proposition-extension-zero-restriction-closed-subscheme`):

* `i^*` preserves all small limits and colimits
  (`ProEtale.RingSheaf.preservesLimitsOfSize_upperStar_of_isCompl`);
* `j_!` preserves products
  (`ProEtale.RingSheaf.preservesLimitsOfShape_discrete_openImmersionLowerShriek`).

Both follow from the statements for sheaves of `R`-modules, since the forgetful functor from
module objects creates limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R] {Z U X : Scheme.{u}} [CompactSpace X]
  [QuasiSeparatedSpace X] (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

include j hij in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (and
`proposition-extension-zero-restriction-closed-subscheme`) for module sheaves over a sheaf of rings
`B`: the pullback `i^*` along a closed immersion with quasi-compact open complement, on a qcqs
scheme, preserves all small limits. -/
theorem preservesLimitsOfSize_upperStar_of_isCompl :
    PreservesLimitsOfSize.{u + 1, u + 1} (upperStar B i) := by
  have := ProEtale.preservesLimitsOfSize_upperStar_of_isCompl (R := R) i j hij
  have : PreservesLimitsOfSize.{u + 1, u + 1} (upperStar B i ⋙ Mod.forget _) :=
    inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1}
      (Mod.forget B ⋙ (i)^*[ModuleCat.{u + 1} R]))
  exact preservesLimits_of_reflects_of_preserves (upperStar B i) (Mod.forget _)

omit [CompactSpace X] [QuasiSeparatedSpace X] [IsClosedImmersion i] in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` for module sheaves over a
sheaf of rings `B`: the pullback `i^*` preserves all small colimits, being a left adjoint. -/
theorem preservesColimitsOfSize_upperStar :
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStar B i) :=
  (upperStarLowerStarAdjunction B i).leftAdjoint_preservesColimits

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` and
`proposition-extension-zero-restriction-closed-subscheme` for module sheaves over a sheaf of rings
`B`: on a qcqs scheme, the extension by zero along a quasi-compact open immersion with closed
complement `i` preserves products. -/
theorem preservesLimitsOfShape_discrete_openImmersionLowerShriek (β : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete β) (openImmersionLowerShriek B i j hij) := by
  have : PreservesLimitsOfShape (Discrete β) (j)_!open[ModuleCat.{u + 1} R] :=
    have (N : β → Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :
        PreservesLimit (Discrete.functor N) (j)_!open[ModuleCat.{u + 1} R] :=
      have := isIso_piComparison_openImmersionLowerShriek i j hij N
      PreservesProduct.of_iso_comparison _ _
    preservesLimitsOfShape_of_discrete _
  have : PreservesLimitsOfShape (Discrete β) (openImmersionLowerShriek B i j hij ⋙ Mod.forget B) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete β)
      (Mod.forget _ ⋙ (j)_!open[ModuleCat.{u + 1} R]))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Mod.forget B)

end AlgebraicGeometry.ProEtale.RingSheaf
