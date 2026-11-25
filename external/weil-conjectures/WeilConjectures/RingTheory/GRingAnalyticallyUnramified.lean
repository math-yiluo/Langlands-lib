/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.LocalProperties.Reduced
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.IsN1OfIsAnalyticallyUnramified

/-!
# Local G-domains are analytically unramified

Let `A` be a Noetherian local domain which is a G-ring. The completion map `A → Â` is regular
(`AdicCompletion.isRegular_of_isGRing`), so it is flat and its generic fibre `K ⊗_A Â`
(`K = Frac A`) is a regular, hence reduced, ring. By flatness `Â ↪ K ⊗_A Â`, so `Â` is reduced:
`A` is analytically unramified, and therefore its normalization is finite
(`isN1_of_isAnalyticallyUnramified`, Stacks, Tag 032Y). This is the part of "excellent local
rings are Nagata" (Stacks, Tag 07QV) used for the branches of local curves.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

/-- A regular ring is reduced: its localizations at maximal ideals are regular local rings,
hence domains. -/
theorem IsRegularRing.isReduced (R : Type u) [CommRing R] [IsRegularRing R] : IsReduced R :=
  isReduced_ofLocalizationMaximal R fun _ _ ↦ inferInstance

/-- A Noetherian local domain whose completion map is regular is analytically unramified: the
generic fibre of the completion map is regular, hence reduced, and contains the completion by
flatness. -/
theorem isAnalyticallyUnramified_of_isRegular (A : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hreg : RingHom.IsRegular (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsAnalyticallyUnramified A := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  let : Algebra A Ahat := (algebraMap A Ahat).toAlgebra
  have : Module.Flat A Ahat := hreg.1
  let K := (⊥ : Ideal A).ResidueField
  have hgeo := (hreg.2 (⊥ : Ideal A)).2 K
  have : IsRegularRing ((⊥ : Ideal A).Fiber Ahat) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid K _).toRingEquiv
  have : IsReduced ((⊥ : Ideal A).Fiber Ahat) := IsRegularRing.isReduced _
  have hK : Function.Injective (algebraMap A K) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ RingHom.ker (algebraMap A K) := ha
    rwa [Ideal.ker_algebraMap_residueField] at this
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : Ahat →ₐ[A] K ⊗[A] Ahat) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Ahat)
      (Algebra.linearMap A K) hK
    have : (Algebra.TensorProduct.includeRight : Ahat →ₐ[A] K ⊗[A] Ahat) =
        (LinearMap.rTensor Ahat (Algebra.linearMap A K)) ∘ (TensorProduct.lid A Ahat).symm := by
      funext x
      simp [Algebra.TensorProduct.includeRight_apply]
    rw [this]
    exact h.comp (TensorProduct.lid A Ahat).symm.injective
  exact isReduced_of_injective _ hinj

/-- A Noetherian local domain which is a G-ring is analytically unramified: its completion map
is regular (`AdicCompletion.isRegular_of_isGRing`). -/
theorem isAnalyticallyUnramified_of_isGRing (A : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : IsGRing A) : IsAnalyticallyUnramified A :=
  isAnalyticallyUnramified_of_isRegular A (AdicCompletion.isRegular_of_isGRing A _ hA)

/-- The normalization of a Noetherian local domain which is a G-ring is finite. -/
theorem isN1_of_isGRing (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : IsGRing A) : IsN1 A (FractionRing A) :=
  isN1_of_isAnalyticallyUnramified A _ (isAnalyticallyUnramified_of_isGRing A hA)
