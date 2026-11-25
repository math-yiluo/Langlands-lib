/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Products of models over the trait

Let `S = Spec k'⟦t⟧` be the trait of a field `k'`. This file defines

* models of finite type over the trait along explicit structure morphisms `q : 𝒳 ⟶ S` and
  `g : 𝒳_η̄ ⟶ Spec Ω`
  (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOver`):
  `q` is separated and of finite type and `j`, `i` are the inclusions of the fibres of `q` over the
  geometric generic point and the closed point; this is `NearbyCyclesModel.IsTraitModel` with the
  structure morphisms made explicit;
* products over the trait of two such models
  (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitProduct`), the setting of
  Gabber's Künneth formula for nearby cycles
  (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap`).

The identification `ε : 𝒳_η̄ ⟶ X` of a model is arbitrary. The nearby cycles of SGA 7 XIII are
defined on complexes on the generic fibre `𝒳_η`, not on all complexes on the geometric generic
fibre `𝒳_η̄`; so the finiteness and Künneth theorems are stated for models whose `ε` factors
through the total space, `ε = j ≫ e` (then `Lε^* A = Lj^* Le^* A` comes from `𝒳_η`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

section TraitModel

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- A nearby-cycles model of `X` with special fibre `X'` is *of finite type over the trait*
`S = Spec k'⟦t⟧` *along* `q : 𝒳 ⟶ S` and `g : 𝒳_η̄ ⟶ Spec Ω` if `q` is separated, quasi-compact
and locally of finite type, `j` is the base change of `q` along the geometric generic point
(with projection `g`) and `i` is the base change of `q` along the closed point. -/
structure IsTraitModelOver (M : NearbyCyclesModel X X'.left) (q : M.total ⟶ trait k')
    (g : M.generic ⟶ Spec (.of (traitGenericField k'))) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType q
  quasiCompact : QuasiCompact q
  isSeparated : IsSeparated q
  isPullback_j : IsPullback M.j g q (traitGenericPoint k')
  isPullback_i : IsPullback M.i X'.hom q (traitClosedPoint k')

/-- A model of finite type over the trait along `q` and `g` is a model of finite type over the
trait. -/
lemma IsTraitModelOver.isTraitModel {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOver q g) :
    M.IsTraitModel :=
  ⟨⟨q, g, h.locallyOfFiniteType, h.quasiCompact, h.isSeparated, h.isPullback_j, h.isPullback_i⟩⟩

end TraitModel

section Product

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left}

/-- Morphisms of models `φ₁ : P ⟶ M` and `φ₂ : P ⟶ N` exhibit `P` as the *product over the trait*
of the models `M` and `N` of finite type over `S = Spec k'⟦t⟧`: the total space of `P` is the
fibre product `𝒳 ×_S 𝒴` of the total spaces (with the projections `φ₁.total`, `φ₂.total`), `P` is
a model of finite type over the trait along the induced structure morphism, the geometric generic
fibre of `P` is the product of those of `M` and `N` over the same geometric generic point
`Spec Ω` (the projections are compatible with the structure morphisms `gM`, `gN` to `Spec Ω`),
and the identifications `ε` of `M` and `N` factor through their total spaces. -/
structure IsTraitProduct (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂') : Prop where
  exists_isTraitModelOver : ∃ (qM : M.total ⟶ trait k')
      (gM : M.generic ⟶ Spec (.of (traitGenericField k'))) (qN : N.total ⟶ trait k')
      (gN : N.generic ⟶ Spec (.of (traitGenericField k'))),
    M.IsTraitModelOver qM gM ∧ N.IsTraitModelOver qN gN ∧ IsPullback φ₁.total φ₂.total qM qN ∧
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) ∧ φ₂.generic ≫ gN = φ₁.generic ≫ gM
  exists_comp_ε_left : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε
  exists_comp_ε_right : ∃ e : N.total ⟶ Y, N.j ≫ e = N.ε

end Product

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
