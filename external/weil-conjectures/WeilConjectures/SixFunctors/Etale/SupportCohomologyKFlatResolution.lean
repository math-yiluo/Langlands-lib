/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# K-flat resolutions computing cohomology with support

Let `X` be separated of finite type over an algebraically closed field `k`, let `Z ⊆ X` be a
closed subscheme and let `A` be a finite commutative ring. Every K-flat complex `P` of étale
sheaves of `A`-modules on `X` with bounded below cohomology admits a quasi-isomorphism
`P ⟶ I` to a K-flat complex `I` on which `RΓ_Z(X, -)` is computed termwise, i.e. the unit of
the right derived functor of `Γ_Z(X, -)` at `I` is an isomorphism.

This is recorded here as an input (`sorry`): its proof needs the finite cohomological
dimension of `Γ_Z(X, -)` on torsion étale sheaves of a scheme of finite type over a
separably closed field (SGA 4, Exp. X, Cor. 4.3, together with the excision triangle for
`Γ_Z`), the computation of right derived functors of functors of finite cohomological
dimension on complexes of acyclic objects (Spaltenstein, *Resolutions of unbounded
complexes*, Compositio Math. 65 (1988), §6), and the K-flatness of the truncated Godement
resolution `P ⟶ G⁰(P) ⟶ ⋯ ⟶ Gᴺ⁻¹(P) ⟶ Cᴺ(P)` of a K-flat complex, whose terms are
flasque, hence `Γ_Z`-acyclic, except the last one, which is `Γ_Z`-acyclic by dimension
shifting (SGA 4, Exp. XVII, 4.2). None of these inputs are formalized in the project yet.

## Main statements

- `exists_quasiIso_kFlat_isIso_rightDerivedFunctorUnit_globalSectionsWithSupport`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every K-flat complex of étale sheaves of modules over a finite ring, with bounded below
cohomology, on a scheme separated of finite type over an algebraically closed field, admits
a quasi-isomorphism to a K-flat complex on which the unit of the derived sections with
support in a closed subscheme is an isomorphism.

This input is not proved in the project: it combines the finite cohomological dimension of
sections with support (SGA 4, Exp. X, Cor. 4.3) with K-flat flasque resolutions (truncated
Godement resolutions, SGA 4, Exp. XVII, 4.2) and the computation of derived functors of
finite cohomological dimension on complexes of acyclic objects (Spaltenstein, Compositio
Math. 65 (1988), §6). It belongs to the étale cohomology chapter on cohomological
dimension. -/
theorem exists_quasiIso_kFlat_isIso_rightDerivedFunctorUnit_globalSectionsWithSupport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) (n : ℤ)
    (hn : (DerivedCategory.Q.obj P).IsGE n) :
    ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (φ : P ⟶ I),
      QuasiIso φ ∧ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
      IsIso ((globalSectionsWithSupport (ModuleCat.{u + 1} A) i).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj I)) := by
  sorry

end AlgebraicGeometry.Etale
