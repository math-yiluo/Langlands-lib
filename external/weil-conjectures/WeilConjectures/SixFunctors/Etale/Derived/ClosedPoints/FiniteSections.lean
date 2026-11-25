/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Support
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.ConstructibleSheaf.SpecializationCriterion

/-!
# Sheaves supported at closed points with finitely many global sections

Let `K` be a separably closed field, `X` a Noetherian scheme locally of finite type over `K`,
`Λ` a finite ring and `Q` an étale sheaf of `Λ`-modules on `X` whose stalks vanish at the
non-closed points. If `Γ(X, Q)` is finite, then `Q` is constructible
(`AlgebraicGeometry.Etale.isConstructibleSheaf_of_isZero_sheafFiber_of_finite`): `Q` is globally
generated (`AlgebraicGeometry.Etale.isGloballyGenerated_of_isZero_sheafFiber`), hence a quotient
of the finite sum `⊕_{s ∈ Γ(X, Q)} Λ_X` of constant sheaves, and quotients of constructible
sheaves on a Noetherian scheme are constructible.

This is the step of Deligne's proof of the finiteness of nearby cycles (SGA 4½, [Th. finitude],
proof of 3.2) controlling the part of a sheaf supported at closed points by its global sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Epimorphic images of constructible sheaves are constructible.** On a Noetherian scheme, the
target of an epimorphism out of a constructible sheaf of modules over a finite ring is
constructible: it is the coimage of the epimorphism, the cokernel of the inclusion of the kernel,
which is constructible as a subsheaf (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`). -/
theorem Scheme.IsConstructibleSheaf.of_epi {X : Scheme.{u}} [IsNoetherian X]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ⟶ G) [Epi e]
    [IsConstructibleSheaf F] : IsConstructibleSheaf G :=
  have : IsConstructibleSheaf (Limits.kernel e) := of_mono (Limits.kernel.ι e)
  have : IsConstructibleSheaf (Abelian.coimage e) := cokernel (Limits.kernel.ι e)
  IsConstructibleSheaf.of_iso (asIso (Abelian.factorThruCoimage e))

namespace Etale

/-- **A sheaf supported at closed points with finite global sections is constructible.** Let `X`
be a Noetherian scheme locally of finite type over a separably closed field and `Q` an étale sheaf
of modules over a finite ring whose stalks at the non-closed points vanish. If `Γ(X, Q)` is
finite, then `Q` is constructible: being globally generated, it is a quotient of a finite sum of
constant sheaves. -/
theorem isConstructibleSheaf_of_isZero_sheafFiber_of_finite {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Spec (.of K))
    [LocallyOfFiniteType p] (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hQ : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj Q))
    (hΓ : Finite (Q.obj.obj (op (etaleTerminal X)))) :
    IsConstructibleSheaf Q := by
  let Λ_X := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  have : IsConstructibleSheaf Λ_X := Scheme.isConstructibleSheaf_constantSheaf _
  have := isConstructibleSheaf_sigma_fin fun _ : Fin (Nat.card (Q.obj.obj (op (etaleTerminal X))))
    ↦ Λ_X
  have : IsConstructibleSheaf (∐ fun _ : Q.obj.obj (op (etaleTerminal X)) ↦ Λ_X) :=
    IsConstructibleSheaf.of_iso (Sigma.whiskerEquiv (Finite.equivFin _).symm fun _ ↦ Iso.refl _)
  have : Epi (globalSectionsEvaluation Λ X Q) := isGloballyGenerated_of_isZero_sheafFiber Q p hQ
  exact Scheme.IsConstructibleSheaf.of_epi (globalSectionsEvaluation Λ X Q)

end Etale

end AlgebraicGeometry
