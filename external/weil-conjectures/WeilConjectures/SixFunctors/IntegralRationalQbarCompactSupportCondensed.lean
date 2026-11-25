/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Compact supports with integral, rational, and algebraically closed condensed coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/sec-n-change/
sk-prop-qlbar-two-colimit/det-def-sf-operations.md, clause (iv)
(blueprint: def-sf-condensed-compact-support-values).

Each value is the native compactification composite `Di_! ⋙ Rp_*` in the ordinary
uncompleted derived category of modules over the pulled-back condensed coefficient ring.
In particular the rational input is an E-module complex, and the algebraically closed
input is a module complex over the finite-subextension-valued condensed algebraic closure.
Constructibility and independence of the compactification are separate theorems.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The integral compact-support value is `Rp_* j_!` on modules over the condensed
valuation ring of the finite extension E. The compactification is supplied explicitly.
Source: blueprint theorem-f-shriek-ell-adic-coefficients--4, clause (iv), at Λ = O_E
(blueprint: def-sf-condensed-compact-support-values). -/
def sfIntegralCompactSupportValueCondensed (E : PadicAlgCl.FiniteIntermediateField l)
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E) X))) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E) Y)) :=
  (rightDerivedLowerShriekOfCompactification (Profinite.padicIntegersRingObj l E) c).obj K

/-- The rational compact-support value is `Rp_* j_!` directly on condensed E-modules.
Source: blueprint theorem-f-shriek-ell-adic-coefficients--4, clause (iv), at Λ = E
(blueprint: def-sf-condensed-compact-support-values). -/
def sfRationalCompactSupportValueCondensed (E : PadicAlgCl.FiniteIntermediateField l)
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y)) :=
  (rightDerivedLowerShriekOfCompactification (Profinite.continuousMapRingObj E) c).obj K

/-- The algebraically closed compact-support value is `Rp_* j_!` on condensed Qbar_l-modules.
The coefficient ring is the native finite-subextension-valued condensed ring.
Source: blueprint theorem-f-shriek-ell-adic-coefficients--4, clause (iv), at Λ = Qbar_l
(blueprint: def-sf-condensed-compact-support-values). -/
def sfQbarCompactSupportValueCondensed (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)) :=
  (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c).obj K

end WeilConjectures
