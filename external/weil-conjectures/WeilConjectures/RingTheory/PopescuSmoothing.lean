/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.FieldTheory.SeparablyGenerated
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.PopescuFinalSolve
import WeilConjectures.RingTheory.PopescuReduceToField
import WeilConjectures.RingTheory.PopescuResolveCharP
import WeilConjectures.RingTheory.PopescuResolveSeparable

/-!
# Popescu smoothing

Source: Stacks Project, Smoothing Ring Maps, Theorem 07GC; Morphisms, Lemma 01V6
(blueprint: lem-weil-pbc-popescu-smoothing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RingHom

-- Stacks 07GC: maximize the radicals of extended singular ideals over all
-- finitely presented factorizations, then apply 07EU.
private theorem smooth_factorization_of_resolutions
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (hresolve : ∀ (A : CommAlgCat.{u} k) [Algebra.FinitePresentation k A]
      (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ),
      q.asIdeal ∈ (Algebra.popescuIdeal α).minimalPrimes →
        Algebra.CanBePopescuResolved α q)
    (A : CommAlgCat.{u} k) [Algebra.FinitePresentation k A] (α : A →ₐ[k] Λ) :
    ∃ (D : CommAlgCat.{u} k), Algebra.Smooth k D ∧
      ∃ (β : A →ₐ[k] D) (γ : D →ₐ[k] Λ), γ.comp β = α := by
  classical
  let Φ : Set (Ideal Λ) := {I | ∃ (B : CommAlgCat.{u} k),
    Algebra.FinitePresentation k B ∧ ∃ (β : A →ₐ[k] B) (γ : B →ₐ[k] Λ),
      γ.comp β = α ∧ Algebra.popescuIdeal γ = I}
  have hΦ : Φ.Nonempty :=
    ⟨Algebra.popescuIdeal α, A, inferInstance, AlgHom.id k A, α, by simp, rfl⟩
  obtain ⟨I, hI, hmax⟩ :=
    (set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian Λ Λ)) Φ hΦ
  obtain ⟨B, hB, β, γ, hcomp, rfl⟩ := hI
  have := hB
  have htop : Algebra.popescuIdeal γ = ⊤ := by
    by_contra hproper
    obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hproper
    let Q : PrimeSpectrum Λ := ⟨q, hq.isPrime⟩
    obtain ⟨C, hC, aC, δ, ε, hfp, hε, hle, hnot⟩ := hresolve B γ Q hq
    let D : CommAlgCat.{u} k := CommAlgCat.of k C
    have hmem : Algebra.popescuIdeal ε ∈ Φ := by
      refine ⟨D, hfp, δ.comp β, ε, ?_, rfl⟩
      rw [← AlgHom.comp_assoc, hε, hcomp]
    apply hmax _ hmem
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnot
    exact heq ▸ hq.le
  have hunit : Ideal.map γ.toRingHom (Algebra.singularIdeal k B) = ⊤ :=
    Ideal.radical_eq_top.mp htop
  obtain ⟨D, hD, aD, hsmooth, δ, ε, hε⟩ :=
    Algebra.exists_smooth_factorization_of_singularIdeal_map_eq_top γ hunit
  refine ⟨CommAlgCat.of k D, hsmooth, δ.comp β, ε, ?_⟩
  rw [← AlgHom.comp_assoc, hε, hcomp]

-- Identify the residue field of the zero ideal of k with k. For each finite purely
-- inseparable extension L/k, cancel the residue-field base change in its regular fibre.
private theorem geometricallyRegular_of_regular_field
    (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (hreg : (algebraMap k Λ).IsRegular) : Algebra.IsGeometricallyRegular k Λ := by
  classical
  let p : Ideal k := ⊥
  let K := p.ResidueField
  let e : k ≃ₐ[k] K := p.algEquivResidueFieldOfField
  have hfiber : Algebra.IsGeometricallyRegular K (p.Fiber Λ) := by
    rw [RingHom.IsRegular, toAlgebra_algebraMap] at hreg
    exact hreg.2 p
  refine ⟨inferInstance, ?_⟩
  intro L hL aL hfinite hpure
  let : Algebra K L := ((algebraMap k L).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap k L x = algebraMap k L (e.symm (e x))
    rw [e.symm_apply_apply])
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite k K L
  have : IsPurelyInseparable K L := IsPurelyInseparable.tower_top k K L
  have : IsRegularRing (TensorProduct K L (p.Fiber Λ)) := hfiber.2 L
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k K L L Λ).toRingEquiv

-- Stacks 07GC: resolve at minimal primes by 07FE or 07FJ and apply criterion 07C3.
private theorem field_ind_smooth
    (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (hreg : (algebraMap k Λ).IsRegular) :
    ObjectProperty.ind.{u} (fun B : CommAlgCat.{u} k ↦ Algebra.Smooth k B)
      (CommAlgCat.of k Λ) := by
  have hresolve : ∀ (A : CommAlgCat.{u} k) [Algebra.FinitePresentation k A]
      (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ),
      q.asIdeal ∈ (Algebra.popescuIdeal α).minimalPrimes →
        Algebra.CanBePopescuResolved α q := by
    have hgeom := geometricallyRegular_of_regular_field k Λ hreg
    have : IsRegularRing (TensorProduct k k Λ) := hgeom.2 k
    have : IsRegularRing Λ :=
      IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k Λ).toRingEquiv
    intro A hA α q hq
    obtain hzero | ⟨p, hp, hchar⟩ := CharP.exists' k
    · have : CharZero k := hzero
      have hsep : Algebra.IsSeparableExtension k q.asIdeal.ResidueField := by
        intro F hF
        have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
        obtain ⟨s, hs, hsep⟩ :=
          exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
        exact ⟨(s : Set F), hs, hsep⟩
      exact Algebra.canBePopescuResolved_of_regularLocalRing_separable α q hq hsep
    · have : CharP k p := hchar
      exact Algebra.canBePopescuResolved_of_char_pos p hp.out.pos α q hgeom hq
  obtain ⟨J, hcat, hfilt, B, ι, hB, hc⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization k (CommAlgCat.of k Λ)
      {B | Algebra.Smooth k B}
      (fun B hB ↦ by
        have : Algebra.Smooth k B := hB
        infer_instance) (by
        intro A hA α
        have := hA
        obtain ⟨D, hD, β, γ, heq⟩ := smooth_factorization_of_resolutions hresolve A α.hom
        exact ⟨D, hD, CommAlgCat.ofHom β, CommAlgCat.ofHom γ,
          CommAlgCat.hom_ext heq⟩)
  exact ⟨J, hcat, hfilt, ⟨B, ι, hc.some⟩, hB⟩

/-- A regular map of Noetherian rings presents its target as a filtered colimit of smooth
algebras, with the colimit universal property in commutative rings. The regular map
`φ : R → Λ` is the structure map `algebraMap R Λ` of an `[Algebra R Λ]` instance, as in the
landed Popescu modules. `R` and `Λ` share the universe `u` because the smoothness clause is
stated for `Spec.map` of a ring map in `CommRingCat.{u}`; the index category lives there too.
Source: Stacks Project, Theorem 07GC and Lemma 01V6
(blueprint: lem-weil-pbc-popescu-smoothing).

Proof:
1. By `lem-weil-pbc-popescu-reduce-to-field` (07F5), reduce to a field `k` and a
Noetherian geometrically regular `k`-algebra. Taking the trivial purely inseparable extension
shows its prime localizations are regular local rings.
2. Use `lem-weil-pbc-factorization-criterion-filtered-colimit` (07C3): it suffices to
factor each map from a finitely presented `k`-algebra through a smooth `k`-algebra. Smooth
algebras can be represented by polynomial quotients, so the resulting indexing category is small.
3. At a prime minimal over the radical of the extended singular ideal, resolve the local
problem using `lem-weil-pbc-popescu-resolve-separable` (07FE) in characteristic zero, with
`lem-weil-pbc-char-zero-field-extension-separable`; in positive characteristic use
`lem-weil-pbc-popescu-resolve-char-p` (07FJ).
4. Among radicals of extended singular ideals for finitely presented factorizations, choose a
maximal one by `lem-weil-pbc-noetherian-ideal-set-maximal`. If it is proper, choose a minimal
prime above it by `lem-weil-pbc-minimal-prime-over-proper-ideal`. The resolution of step 3
strictly enlarges the radical, contradicting maximality. Thus some radical is the unit ideal.
5. The singular ideal then also extends to the unit ideal. Apply
`lem-weil-pbc-popescu-final-solve` (07EU), and compose with the original factorization.
This establishes the criterion of step 2; step 1 returns the result for the original base ring.
6. Apply `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` (01V6) to each stage and
`lem-weil-pbc-filtered-colimit-algebras-elementwise` (1) to obtain the colimit in rings.
-/
theorem popescu_smoothing {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] (hφ : (algebraMap R Λ).IsRegular) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (B : J ⥤ CommAlgCat.{u} R),
      (∀ j : J, AlgebraicGeometry.Smooth
        (Spec.map (CommRingCat.ofHom (algebraMap R (B.obj j))))) ∧
      ∃ ι : B ⟶ (Functor.const J).obj (CommAlgCat.of R Λ),
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone
          { pt := CommAlgCat.of R Λ, ι := ι })) := by
  obtain ⟨J, hcat, hfilt, pres, hB⟩ :=
    popescu_reduce_to_field.{u, u} field_ind_smooth R Λ hφ
  let _ := hcat
  have := hfilt
  refine ⟨J, hcat, hfilt, pres.diag, ?_, pres.ι, ?_⟩
  · intro j
    have := hB j
    apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
    exact (RingHom.smooth_algebraMap).mpr inferInstance
  · let E := (commAlgCatEquivUnder (CommRingCat.of R)).functor
    have : IsConnected J := IsFiltered.isConnected J
    have : E.IsEquivalence := inferInstance
    have : PreservesColimit pres.diag
        (E ⋙ Under.forget (CommRingCat.of R)) := inferInstance
    exact ⟨isColimitOfPreserves (E ⋙ Under.forget (CommRingCat.of R)) pres.isColimit⟩

end RingHom
