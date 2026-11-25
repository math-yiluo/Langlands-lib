/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Algebra.Shrink
import WeilConjectures.FieldTheory.SeparableSmoothColimit

/-!
# The localized zero-dimensional separable problem

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE; its zero-dimensional case.
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem exists_smooth_subalgebra_factor
    {k : Type u} {A : Type v} {L : Type w}
    [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    [FiniteType k A] (f : A →ₐ[k] L) (hsep : IsSeparableExtension k L) :
    ∃ S : Subalgebra k L, Smooth k S ∧ S.FG ∧ ∀ a : A, f a ∈ S := by
  classical
  obtain ⟨hne, hdir, hcover, -⟩ :=
    FieldTheory.separable_extension_is_filtered_colimit_smooth hsep
  have hfinite (s : Finset L) :
      ∃ S : {S : Subalgebra k L // Smooth k S ∧ S.FG}, ∀ x ∈ s, x ∈ S.1 := by
    induction s using Finset.induction_on with
    | empty => obtain ⟨S⟩ := hne; exact ⟨S, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨S, hS⟩ := ih
      obtain ⟨T, hT⟩ := hcover x
      obtain ⟨U, hSU, hTU⟩ := hdir S T
      exact ⟨U, by intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
                   · exact hTU hT
                   · exact hSU (hS y hy)⟩
  obtain ⟨s, hs⟩ := (inferInstance : FiniteType k A).out
  obtain ⟨S, hS⟩ := hfinite (s.image f)
  have hle : Algebra.adjoin k (f '' (s : Set A)) ≤ S.1 := by
    apply Algebra.adjoin_le
    rintro x ⟨a, ha, rfl⟩
    exact hS _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  rw [Algebra.adjoin_image, hs, Algebra.map_top] at hle
  exact ⟨S.1, S.2.1, S.2.2, fun a ↦ hle (f.mem_range_self a)⟩

/-- The localized problem is resolvable when the target localization is regular of
 dimension zero with separable residue field. Minimality in the global target is unnecessary.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, zero-dimensional
case in step 2 of the repaired proof; Algebra 07BV.
(blueprint: lem-weil-pbc-popescu-separable-height-zero-local).

Proof: a regular local ring of dimension zero has maximal ideal zero, hence is a field.
Its residue-field map is an isomorphism identifying the field and its `k`-algebra structure
with `κ(q)`. Apply 07BV directly to `κ(q)` to obtain a nonempty directed family of smooth
finitely generated subalgebras covering the field. The preimage of `q` in the field `k`
is zero, so its localization `K` is canonically `k`. Consequently `K ⊗[k] A` is of finite
type over `k`. A finite set of algebra generators has image in one smooth subalgebra `S`
of the residue field: choose one for each generator, and combine them using directedness.
Their images generate the range, so the entire map takes values in `S`. Finite type makes
`S` small in universe `max u v`; transport it to `Shrink S` with its induced algebra
structure. Composition with the inverse residue-field map gives the target map. Give this
intermediate ring its `K`-algebra structure via the source map; compatibility follows
from the factorization. Formal smoothness over `K` follows by restriction of scalars,
since the localization `k → K` is formally unramified, and finite presentation over `K`
follows from finite presentation over `k` and finite type of `K/k`. Hence it is smooth
 over `K`. Its singular ideal is the unit ideal: its localization at one is smooth.
The extended radical ideal is therefore the whole target, containing the starting ideal
and escaping the proper maximal ideal. This gives the displayed local resolution.
No global domination or delocalization is asserted here. -/
theorem popescu_separable_height_zero_local
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0)
    (hsep : IsSeparableExtension k q.asIdeal.ResidueField) :
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under k) q.asIdeal
    CanBePopescuResolved
      (Algebra.TensorProduct.lift
        (Algebra.ofId (Localization.AtPrime (q.asIdeal.under k))
          (Localization.AtPrime q.asIdeal))
        ((IsScalarTower.toAlgHom k Λ (Localization.AtPrime q.asIdeal)).comp α)
        (fun _ _ => Commute.all _ _))
      ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩ := by
  classical
  let K := Localization.AtPrime (q.asIdeal.under k)
  let L := Localization.AtPrime q.asIdeal
  let : Algebra K L := Localization.AtPrime.algebraOfLiesOver
    (q.asIdeal.under k) q.asIdeal
  let C := TensorProduct k K A
  let f : C →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    ((IsScalarTower.toAlgHom k Λ L).comp α) (fun _ _ => Commute.all _ _)
  have hmax : IsLocalRing.maximalIdeal L = ⊥ := by
    apply (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal L))).mp
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := L)
    rw [hdim] at h
    exact_mod_cast h
  let e : k ≃ₐ[k] K := IsLocalization.atUnits k (q.asIdeal.under k).primeCompl (S := K)
    (by intro x hx; exact isUnit_iff_ne_zero.mpr (by
          intro h; exact hx (h ▸ (q.asIdeal.under k).zero_mem)))
  have : FinitePresentation k K := FinitePresentation.equiv e
  have : FiniteType k C := FiniteType.trans (inferInstance : FiniteType k K)
    (inferInstance : FiniteType K C)
  let res : L →ₐ[k] q.asIdeal.ResidueField := IsScalarTower.toAlgHom k L _
  have hres : Function.Bijective res := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    rw [RingHom.injective_iff_ker_eq_bot]
    exact (IsLocalRing.ker_residue (R := L)).trans hmax
  let E : L ≃ₐ[k] q.asIdeal.ResidueField := AlgEquiv.ofBijective res hres
  obtain ⟨S, hS, hfg, hmem⟩ := exists_smooth_subalgebra_factor
    (E.toAlgHom.comp (f.restrictScalars k)) hsep
  have : Smooth k S := hS
  obtain ⟨n, π, hπ⟩ := FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : FiniteType k S)
  have : Small.{max u v} S := small_of_surjective hπ
  let B := Shrink.{max u v} S
  let EB : B ≃ₐ[k] S := Shrink.algEquiv k S
  have : Smooth k B := Smooth.of_equiv EB.symm
  let kB : C →ₐ[k] B := EB.symm.toAlgHom.comp
    ((E.toAlgHom.comp (f.restrictScalars k)).codRestrict S hmem)
  let kγ : B →ₐ[k] L := E.symm.toAlgHom.comp (S.val.comp EB.toAlgHom)
  let : Algebra K B := (kB.toRingHom.comp (algebraMap K C)).toAlgebra
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    change algebraMap k B r = kB (algebraMap K C (algebraMap k K r))
    rw [← IsScalarTower.algebraMap_apply k K C]
    exact (kB.commutes r).symm)
  have : FormallyUnramified k K := FormallyUnramified.of_isLocalization
    (q.asIdeal.under k).primeCompl
  have : FormallySmooth K B := FormallySmooth.of_restrictScalars k K B
  have : FinitePresentation K B :=
    FinitePresentation.of_restrict_scalars_finitePresentation k K B
  have : Smooth K B := Smooth.mk
  let β : C →ₐ[K] B :=
    { toRingHom := kB.toRingHom
      commutes' := fun r ↦ rfl }
  let γ : B →ₐ[K] L :=
    { toRingHom := kγ.toRingHom
      commutes' := by
        intro r
        change kγ (kB (algebraMap K C r)) = algebraMap K L r
        simp [kγ, kB, E, EB, AlgHom.coe_codRestrict, f.commutes] }
  have hsing : singularIdeal K B = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.le_radical
    apply Ideal.subset_span
    change Smooth K (Localization.Away (1 : B))
    have : Smooth B (Localization.Away (1 : B)) := Smooth.of_isLocalization_Away 1
    exact Smooth.comp K B (Localization.Away (1 : B))
  have htop : popescuIdeal γ = ⊤ := by
    unfold popescuIdeal
    rw [hsing, Ideal.map_top, Ideal.radical_top]
  refine ⟨B, inferInstance, inferInstance, β, γ, inferInstance, ?_, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    change kγ (kB x) = f x
    simp [kγ, kB]
  · rw [htop]
    exact le_top
  · rw [htop, top_le_iff]
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top

end Algebra
