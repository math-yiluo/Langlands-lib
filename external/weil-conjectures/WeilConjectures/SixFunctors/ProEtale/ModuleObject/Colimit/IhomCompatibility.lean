/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibilityFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility

/-!

# The coefficient comparison for internal homs along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`k` a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` for the extension of scalars on bounded constructible complexes
(`ProEtale.boundedConstructibleExtendScalars`), a monoidal functor
(`ProEtale.CondensedRing.monoidal_boundedConstructibleExtendScalars`). This file proves the
internal Hom clause of blueprint `proposition-six-operations-change-coefficients` (2) for `𝒪_E ⟶ E`:
the comparison `v_{A,B} : T RHom(A, B) ⟶ RHom(T A, T B)`, the mate of the tensorator
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleExtendScalars`).

As for the comparisons of `Rf_*` and `Rf^!`, this holds because `T_X` is the rationalization of
`Dᵇc(X)⟦𝒪_E⟧` (`ProEtale.isLocalization_boundedConstructibleExtendScalars`, blueprint
`proposition-inverting-ell`), and `v` is the mate of the isomorphism
`T (A ⊗ -) ≅ T A ⊗ T -` along the adjunctions `A ⊗ - ⊣ RHom(A, -)`
(`CategoryTheory.Rationalization.isIso_mateEquiv_of_isLocalization`).

For the inclusion `E ⟶ ℚ̄_ℓ`, which is not a localization, the clause
(`ProEtale.CondensedRing.isIso_ihomComparison_constructibleToPadicAlgCl`) follows from the
finite subextensions `E ⊆ F`, where `F_X` is free over `E_X`, by the 2-colimit description of
`Dᵇc(X)⟦ℚ̄_ℓ⟧`. Together they give the clause for the composite
`𝒪_E ⟶ ℚ̄_ℓ`
(`ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl`), the
comparison of a composite being the composite of the comparisons.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The internal Hom comparison for `𝒪_E ⟶ E` is an isomorphism** (blueprint
`proposition-six-operations-change-coefficients` (2)): for bounded constructible `𝒪_E`-complexes `A`
and `B`, `v_{A,B} : T RHom(A, B) ⟶ RHom(T A, T B)` is an isomorphism, `T` being a rationalization
and `v` the mate of the tensorator. -/
theorem isIso_ihomComparison_boundedConstructibleExtendScalars
    (A : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso (Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleExtendScalars X.left ℓ E) A) := by
  have := noetherianSpace_left_of_over X
  let T := boundedConstructibleExtendScalars X.left ℓ E
  let τ : tensorLeft A ⋙ T ≅ T ⋙ tensorLeft (T.obj A) :=
    NatIso.ofComponents (fun B ↦ (Functor.Monoidal.μIso T A B).symm) fun f ↦ by
      exact (Functor.OplaxMonoidal.δ_natural_right T A f).symm
  exact Rationalization.isIso_mateEquiv_of_isLocalization (M := Submonoid.powers (ℓ : ℤ)) T T
    (ihom.adjunction A) (ihom.adjunction (T.obj A)) τ

/-- Blueprint
`proposition-six-operations-change-coefficients` (2), for the coefficient map `E ⟶ ℚ̄_ℓ`. For
bounded constructible `E`-complexes `A` and `B`, the comparison
`v_{A,B} : (RHom(A, B))_{ℚ̄_ℓ} ⟶ RHom(A_{ℚ̄_ℓ}, B_{ℚ̄_ℓ})`, the transpose of
`(RHom(A, B))_{ℚ̄_ℓ} ⊗ A_{ℚ̄_ℓ} ≅ (RHom(A, B) ⊗ A)_{ℚ̄_ℓ} ⟶ B_{ℚ̄_ℓ}` (the mate of the tensorator,
`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), is an isomorphism. -/
theorem isIso_ihomComparison_constructibleToPadicAlgCl
    (A : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    IsIso (Functor.LaxMonoidal.ihomComparison (constructibleToPadicAlgCl X.left ℓ E) A) :=
  isIso_ihomComparison_constructibleToPadicAlgCl_of_twoColimit ℓ X E A

/-- **The internal Hom comparison for `𝒪_E ⟶ ℚ̄_ℓ` is an isomorphism** (blueprint
`proposition-six-operations-change-coefficients` (2)): the comparison of the composite extension of
scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` is the composite of the comparisons. -/
theorem isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl
    (A : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso (Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E)
        A) := by
  have := isIso_ihomComparison_boundedConstructibleExtendScalars ℓ E A
  have := isIso_ihomComparison_constructibleToPadicAlgCl ℓ E
    ((boundedConstructibleExtendScalars X.left ℓ E).obj A)
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  rw [Functor.LaxMonoidal.ihomComparison_comp_app]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
