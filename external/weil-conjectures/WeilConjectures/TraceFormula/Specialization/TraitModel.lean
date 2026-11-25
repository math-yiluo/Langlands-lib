/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# Models of finite type over the trait

A nearby-cycles model `M` of `X` with special fibre `X'` (a `k'`-scheme) is a *model of finite type
over the trait* `S = Spec k'⟦t⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModel`)
if its total space is separated and of finite type over `S`, and `j` and `i` are the inclusions of
the geometric generic fibre and of the special fibre. For these models nearby cycles are the
geometric nearby cycles of SGA 7 XIII, and Deligne's finiteness theorem applies.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- A nearby-cycles model of `X` with special fibre `X'` is *of finite type over the trait*
`Spec k'⟦t⟧` if its total space is separated, quasi-compact and locally of finite type over the
trait, and `j` and `i` are the inclusions of its geometric generic fibre and of its special
fibre. -/
structure IsTraitModel (M : NearbyCyclesModel X X'.left) : Prop where
  exists_isPullback : ∃ (q : M.total ⟶ trait k')
      (g : M.generic ⟶ Spec (.of (traitGenericField k'))),
    LocallyOfFiniteType q ∧ QuasiCompact q ∧ IsSeparated q ∧
      IsPullback M.j g q (traitGenericPoint k') ∧ IsPullback M.i X'.hom q (traitClosedPoint k')

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
