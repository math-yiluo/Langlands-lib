/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Basic

/-!
# An abstract formalism for compactly supported direct images

The compactly supported direct image `Rf_! = Rp_* ∘ i_!` attached to a compactification
`X ⟶[i] Z ⟶[p] Y` is assembled from three kinds of functors: pullbacks `f^*`, their right
adjoints `f_*`, and, for open immersions `j`, the left adjoint `j_!` of `j^*`. All the
comparison isomorphisms of the theory (base change for `j_!`, the exchange `j_! g'_* ⟶ g''_* j'_!`,
the comparison along a refinement of compactifications, the composition law of `Rf_!`) are
mates of the composition isomorphisms of the pullbacks. Their coherence is therefore formal.

The formal structure is `CategoryTheory.ExchangeFormalism`; this file specialises it to all
schemes, with the open immersions as the class of morphisms admitting an extension by zero:
`AlgebraicGeometry.CompactSupportFormalism`. It also records the two scheme-theoretic
hypotheses used in the theory:

- `HasBaseChange`: base change for the extension by zero along cartesian squares;
- `HasProperExchange`: proper base change in the form of the exchange isomorphism
  `j_! g'_* ≅ g''_* j'_!` for cartesian squares with proper bottom map.

The concrete instance, on the bounded below derived categories of étale sheaves, is used to
prove the composition law of blueprint `proposition-composition-base-change-rf-shriek--1`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option linter.checkUnivs false in
/-- **A formalism for compactly supported direct images**: the exchange formalism
(`CategoryTheory.ExchangeFormalism`) indexed by all schemes, with the open immersions as the
morphisms admitting an extension by zero. It consists of a category `obj X` for each scheme `X`,
a pullback pseudofunctor `f ↦ pb f`, a right adjoint `pf f` of each `pb f`, and a left adjoint
`sh j` of `pb j` for each open immersion `j`. -/
abbrev CompactSupportFormalism := ExchangeFormalism.{w, v} Scheme.{u} @IsOpenImmersion

/-- An open immersion belongs to the class of morphisms indexing the extensions by zero. -/
instance fact_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Fact (IsOpenImmersion j) :=
  ⟨inferInstance⟩

namespace CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

/-- Base change for the extension by zero: the base change map of a cartesian square is an
isomorphism. -/
class HasBaseChange : Prop where
  isIso_baseChange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsOpenImmersion l] [IsOpenImmersion r] (h : IsPullback t l r b) :
    IsIso (F.baseChange t l r b h.w)

/-- Proper base change in the form needed for compactly supported direct images: the exchange
map of a cartesian square whose bottom map is proper is an isomorphism. -/
class HasProperExchange extends F.HasBaseChange where
  isIso_exchange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsOpenImmersion l] [IsOpenImmersion r] [IsProper b] (h : IsPullback t l r b) :
    haveI := isIso_baseChange h
    IsIso (F.exchange t l r b h.w)

end CompactSupportFormalism

end AlgebraicGeometry
