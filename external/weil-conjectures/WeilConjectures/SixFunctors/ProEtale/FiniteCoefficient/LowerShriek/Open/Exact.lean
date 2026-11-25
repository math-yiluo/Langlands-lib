/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Exactness of the extension by zero on the pro-étale site

For an open immersion `j : U ⟶ X` the extension by zero `j_!` on sheaves for the small
pro-étale sites is exact (blueprint `proposition-extension-zero-restriction-closed-subscheme--7`):
it is a left adjoint, hence right exact, and it is left exact
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`), being the
presheaf-level extension by zero, which is computed objectwise, followed by sheafification.
Maps `j_! M ⟶ N` correspond to maps `M ⟶ j^* N`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekHomEquiv`, blueprint
`prose-03-02`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `prose-03-02`: for an open immersion `j`, maps
`j_! M ⟶ N` from the extension by zero of a pro-étale sheaf `M` on `U` correspond to maps
`M ⟶ j^* N`, naturally in both arguments: the hom-equivalence of the adjunction
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`. Since `j` is a
monomorphism, `j_!` is the left Kan extension along the localization functor `U_proét ⥤ X_proét`
(the presheaf being zero on objects not over `U`) followed by sheafification. -/
noncomputable def openImmersionLowerShriekHomEquiv (M : Sheaf (Scheme.ProEt.topology U) A)
    (N : Sheaf (Scheme.ProEt.topology X) A) :
    ((j)_!open[A].obj M ⟶ N) ≃ (M ⟶ (j)^*[A].obj N) :=
  (openImmersionLowerShriekUpperStarAdjunction A j).homEquiv M N

lemma openImmersionLowerShriekHomEquiv_naturality_left
    {M M' : Sheaf (Scheme.ProEt.topology U) A} {N : Sheaf (Scheme.ProEt.topology X) A}
    (a : M' ⟶ M) (b : (j)_!open[A].obj M ⟶ N) :
    openImmersionLowerShriekHomEquiv A j M' N ((j)_!open[A].map a ≫ b) =
      a ≫ openImmersionLowerShriekHomEquiv A j M N b :=
  (openImmersionLowerShriekUpperStarAdjunction A j).homEquiv_naturality_left a b

lemma openImmersionLowerShriekHomEquiv_naturality_right
    {M : Sheaf (Scheme.ProEt.topology U) A} {N N' : Sheaf (Scheme.ProEt.topology X) A}
    (b : (j)_!open[A].obj M ⟶ N) (c : N ⟶ N') :
    openImmersionLowerShriekHomEquiv A j M N' (b ≫ c) =
      openImmersionLowerShriekHomEquiv A j M N b ≫ (j)^*[A].map c :=
  (openImmersionLowerShriekUpperStarAdjunction A j).homEquiv_naturality_right b c

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--7`: Exactness of extension
by zero. For an open immersion `j : U ⟶ X`, the extension by zero `j_!` of pro-étale sheaves with
values in a Grothendieck abelian category `A` (for instance modules over a finite commutative ring
such as `A_{E,n}`) sends short exact sequences to short exact sequences: it preserves finite limits
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`) and, being a left
adjoint, finite colimits. -/
theorem shortExact_map_openImmersionLowerShriek
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology U) A)} (hS : S.ShortExact) :
    (S.map (j)_!open[A]).ShortExact :=
  hS.map_of_exact _

/-- The extension by zero `j_!` along an open immersion is exact: it preserves finite limits and
finite colimits (blueprint `proposition-extension-zero-restriction-closed-subscheme--7`). -/
theorem preservesFiniteLimits_and_preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open[A] ∧ PreservesFiniteColimits (j)_!open[A] :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale
