/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Bounded complexes of flat constructible sheaves

A strictly bounded complex of constructible étale sheaves of modules over a noetherian ring is
bounded constructible (`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_Q_obj`):
its homology sheaves are constructible, constructible sheaves being closed under kernels and
cokernels. If moreover its terms are flat and the ring is finite, it lies in `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_Q_obj`), being its own bounded
flat model. This is the converse of the constructible flat model of
`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

section Complex

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- **The homology of a short complex of constructible sheaves of modules over a noetherian ring
is constructible**: it is the cokernel of a morphism into the cycles, the kernel of the second
morphism. -/
theorem Scheme.IsConstructibleSheaf.homology [IsNoetherianRing Λ]
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsConstructibleSheaf S.X₁] [IsConstructibleSheaf S.X₂] [IsConstructibleSheaf S.X₃] :
    IsConstructibleSheaf S.homology := by
  have := IsConstructibleSheaf.kernel S.g
  have : IsConstructibleSheaf S.cycles :=
    IsConstructibleSheaf.of_iso (F := Limits.kernel S.g)
      ((S.cyclesIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)).symm)
  have := IsConstructibleSheaf.cokernel S.toCycles
  exact IsConstructibleSheaf.of_iso (F := Limits.cokernel S.toCycles)
    ((cokernelIsCokernel S.toCycles).coconePointUniqueUpToIso S.homologyIsCokernel)

/-- A strictly bounded complex of constructible sheaves of modules over a noetherian ring is
bounded constructible: its homology sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.homology`). -/
theorem Etale.DerivedCategory.boundedConstructible_Q_obj [IsNoetherianRing Λ]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ n, IsConstructibleSheaf (P.X n)) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (DerivedCategory.Q.obj P) := by
  refine ⟨⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩, fun n ↦ ?_⟩
  have : IsConstructibleSheaf (P.sc n).X₁ := hP _
  have : IsConstructibleSheaf (P.sc n).X₂ := hP _
  have : IsConstructibleSheaf (P.sc n).X₃ := hP _
  have : IsConstructibleSheaf ((HomologicalComplex.homologyFunctor _ _ n).obj P) :=
    IsConstructibleSheaf.homology (P.sc n)
  exact IsConstructibleSheaf.of_iso
    ((DerivedCategory.homologyFunctorFactors _ n).app P).symm

/-- A strictly bounded complex of flat constructible sheaves of modules over a finite ring lies in
`Dctf(X, Λ)`: it is bounded constructible, and it is its own flat model, so it has finite Tor
amplitude. -/
theorem Etale.DerivedCategory.constructibleFiniteTor_Q_obj [Finite Λ]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hflat : ∀ n, ObjectProperty.flat (P.X n))
    (hP : ∀ n, IsConstructibleSheaf (P.X n)) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (DerivedCategory.Q.obj P) :=
  ⟨Etale.DerivedCategory.boundedConstructible_Q_obj P a b hP, a, b,
    DerivedCategory.torAmplitudeIn_Q_obj_of_flat P a b hflat⟩

end Complex

end AlgebraicGeometry
