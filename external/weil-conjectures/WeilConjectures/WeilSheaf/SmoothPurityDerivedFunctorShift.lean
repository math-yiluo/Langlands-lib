/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleModuleComparison
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullShift

/-! # Shift structures on the named derived coefficient and pullback functors -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

noncomputable instance purityDerivedCoefficientExtension_commShift
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) :
    (purityDerivedCoefficientExtension a X).CommShift ℤ :=
  inferInstanceAs (L(Mod.extendScalars (coefficientMap a X)).CommShift ℤ)

noncomputable instance purityDerivedPullback_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (purityDerivedPullback Λ g).CommShift ℤ :=
  inferInstanceAs (L((g)^*⟦Λ⟧).CommShift ℤ)

end AlgebraicGeometry.ProEtale.CondensedRing
