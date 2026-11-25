/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The principal closed-open datum

Source: blueprint sec-smooth-purity/sk-prop-an/def-pur-frame-class.md,
“Put D_j = V(f_j); the function f_j is a unit on U minus D_j”
(blueprint: def-pur-principal-closed-open).

The datum packages the canonical principal zero-locus closed immersion, the inclusion
of its complementary basic open, and the localization unit. All three constructions
are the existing scheme constructions, with no choice of a replacement closed subscheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The principal closed-open datum `(i, j, u)` of a global function on a `k`-scheme.
Here `k` is the field of the fixed purity setting `P`, and `X` includes its structure map
through `Over (Spec k)`. The closed subscheme is the one cut out by the ideal `(f)`:
on affine opens it is `Spec (R / fR)`. Its complementary open is the basic open `X_f`.
The unit is precisely the restriction of `f` to this open, supplied by `basicOpenUnit`.
The two inclusions carry the existing closed- and open-immersion predicates.
No nonemptiness, regularity, or nonzero assumption is made: units, nilpotent functions
(including zero), and the empty scheme are all permitted.

Source: blueprint sec-smooth-purity/sk-prop-an/def-pur-frame-class.md, the individual
principal factor `D_j = V(f_j)` and its unit on the complement
(blueprint: def-pur-principal-closed-open). -/
noncomputable def principalClosedOpenDatum (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Over (Spec (CommRingCat.of P.field.k))) (f : Γ(X.left, ⊤)) :
    {i : X.left.zeroLocusSubscheme {f} ⟶ X.left // IsClosedImmersion i} ×
      {j : (X.left.basicOpen f).toScheme ⟶ X.left // IsOpenImmersion j} ×
        Γ((X.left.basicOpen f).toScheme, ⊤)ˣ :=
  ⟨⟨X.left.zeroLocusSubschemeι {f}, inferInstance⟩,
    ⟨(X.left.basicOpen f).ι, inferInstance⟩, X.left.basicOpenUnit f⟩

end WeilConjectures.PurityFiniteSetting
