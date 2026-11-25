/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Geometric Verdier biduality for constructible sheaves

This is the sheaf case, before the separate formal finite-truncation argument.
The target of the structure morphism is required to be isomorphic to the base point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- The geometric sheaf case of Verdier biduality for condensed algebraic-closure
coefficients. The hypothesis that S maps isomorphically to Spec k excludes a singular
relative base. The sheaf need not be lisse or locally free on the whole scheme.

Source: Bhatt--Scholze, Lemmas 6.7.13, 6.7.18--6.7.20 and Proposition 6.8.14;
blueprint sk-prop-sf-biduality-general, coefficient-duality paragraph.
(blueprint: lem-pd-constructible-sheaf-biduality)

Proof: a scheme of finite type over a field is excellent. Use the dimension
function normalized by the structure morphism. Bhatt--Scholze 6.7.18 identifies
finite-coefficient exceptional pullbacks with reductions of the integral
exceptional pullback constructed in 6.7.19. On Spec k the normalized dualizing
object is the coefficient unit. Thus the normalized dualizing object on X is
the exceptional pullback of this unit, with its specified adjunction evaluation.

First work over the integer ring O_E of a finite extension E/Q_l. The coherent
finite dualizing objects form the potential dualizing system of 6.7.20. Its
derived limit Omega has the stated finite reductions. For a constructible
integral complex L, 6.7.13 identifies the reduction of RHom(L,Omega) with the
finite-coefficient internal Hom, compatibly with evaluation. Apply this twice.
Finite-coefficient Verdier biduality makes every reduction of the canonical
double-dual map invertible. Its cone is derived complete and has zero reductions;
derived Nakayama, or the derived-limit triangle, makes that cone zero. This is
the proof of 6.7.20, including the actual transpose of evaluation.

For the sheaf M in the statement, Proposition 6.8.14 and its proof by finite
stratification and integral lattices give a finite extension E and an integral
constructible complex whose rationalized scalar extension represents M[0].
The internal-Hom and exceptional-pullback coefficient comparisons of 6.7.13,
6.7.18 and 6.8.15 identify its rational and algebraic-closure dualizing objects
with the exceptional pullbacks of the corresponding coefficient units. They
preserve evaluations: uncurrying either comparison gives scalar extension of
the original evaluation. Consequently the scalar extension of the integral
biduality isomorphism is exactly the displayed canonical map. Uniqueness of
right adjoints identifies the coefficient-passage exceptional pullback with
the chosen boundedConstructibleUpperShriek, preserving its counit, so no
choice of an unrelated dualizing object enters the assertion. If needed these
comparisons may be checked after etale localization and passage to a geometric
base field, where finite-stage geometric biduality applies, and descended by
conservativity. The empty scheme and rank-zero sheaf give zero objects on both
sides. Finally the isomorphism S -> Spec k and composition of exceptional
adjunctions identify the displayed target with this normalized dualizing object. -/
theorem isIso_biduality_constructible_sheaf [IsIso S.hom] (a : X ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hM : IsConstructibleModuleObject _ M) :
    IsIso (toIhomIhom
      ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
