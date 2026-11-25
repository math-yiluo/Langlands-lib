/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.CompatibleRingTowerRecursion
import WeilConjectures.RingTheory.FlatLocalMonogenicExtension
import WeilConjectures.RingTheory.FlatLocalTowerDirectLimit

/-!
# A coherent system of flat local rings covering a residue-field extension

Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), first four proof paragraphs.
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), first four proof paragraphs.
(blueprint: lem-weil-pbc-residue-field-tower-system)

Proof: Well-order the underlying set of K (lifted to the common universe). At each
index x take the colimit of the rings already constructed, using R at the first
index. Their compatible maps to K induce a map on this colimit. Each element is
represented at a stage: a nonzero image means that its representative is a unit,
and a zero image means that it belongs to the image of the maximal ideal of R.
Thus the colimit is local with this maximal ideal. Its underlying R-module is the
module colimit, by the representative and eventual-equality criteria; filtered
colimits preserve flatness. Now adjoin the element x. If it is transcendental over
this ring's residue field, localize the polynomial ring at the extended maximal
ideal. If it is algebraic, lift the coefficients of its monic minimal polynomial
and take the monic quotient. The former is flat by freeness and localization;
the latter is finite free, and integral contraction of maximal ideals shows it
is local. In both cases evaluation has kernel the extended maximal ideal and
its image is the simple field extension. Compose all earlier transition maps
with this new map. Transfinite recursion and induction give the directed-system
identities and compatibility with R and K. The image at index x contains x,
so the stage images cover K. The polynomial, quotient and localization
constructions, and colimits over subsets of K, all stay in Type (max u v).
No final colimit or residue-field isomorphism is asserted here. -/
theorem exists_residue_field_tower_system
    (R : Type u) [CommRing R] [IsLocalRing R] (K : Type v) [Field K]
    (ι : ResidueField R →+* K) :
    ∃ (_ : LinearOrder (ULift.{u} K))
      (A : ULift.{u} K → Type (max u v))
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsLocalRing (A i))
      (_ : ∀ i, Algebra R (A i))
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j),
      DirectedSystem A (fun i j h ↦ f i j h) ∧
      ∃ (ψ : ∀ i, A i →+* K),
        (∀ i j h x, ψ j (f i j h x) = ψ i x) ∧
        (∀ i, (algebraMap R (A i)).Flat) ∧
        (∀ i, (maximalIdeal R).map (algebraMap R (A i)) = maximalIdeal (A i)) ∧
        (∀ i, RingHom.ker (ψ i) = maximalIdeal (A i)) ∧
        (∀ i, (ψ i).comp (algebraMap R (A i)) = ι.comp (residue R)) ∧
        (∀ x : K, ∃ i a, ψ i a = x) := by
  classical
  let η := ι.comp (residue R)
  have hη : RingHom.ker η = maximalIdeal R := by
    ext r
    change ι (residue R r) = 0 ↔ r ∈ maximalIdeal R
    rw [map_eq_zero, ← ker_residue (R := R)]
    rfl
  let P : ∀ (A : Type (max u v)) [CommRing A] [Algebra R A], (A →+* K) → Prop :=
    fun A _ _ ψ ↦ ∃ (_ : IsLocalRing A),
      (algebraMap R A).Flat ∧
      (maximalIdeal R).map (algebraMap R A) = maximalIdeal A ∧
      RingHom.ker ψ = maximalIdeal A ∧ ψ.comp (algebraMap R A) = η
  have hbase : ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A)
      (ψ : A →+* K), P A ψ := by
    let A := ULift.{v} R
    let e : A ≃+* R := ULift.ringEquiv
    have : IsLocalRing A := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
    have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective e.toRingHom e.surjective
    refine ⟨A, inferInstance, inferInstance, η.comp e.toRingHom, inferInstance,
      ?_, ?_, ?_, ?_⟩
    · exact RingHom.Flat.of_bijective e.symm.bijective
    · exact map_ringEquiv_maximalIdeal e.symm
    · ext a
      change η a.down = 0 ↔ a ∈ maximalIdeal A
      rw [← RingHom.mem_ker, hη]
      rw [← maximalIdeal_comap e.toRingHom]
      rfl
    · ext r
      rfl
  have hstep : ∀ (J : Type (max u v)) [LinearOrder J] [Nonempty J]
      (A : J → Type (max u v)) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j)
      [DirectedSystem A (fun i j h ↦ f i j h)] (ψ : ∀ j, A j →+* K),
      (∀ i j h a, ψ j (f i j h a) = ψ i a) →
      (∀ j, P (A j) (ψ j)) → ∀ x : K,
      ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B) (φ : B →+* K)
        (g : ∀ j, A j →ₐ[R] B),
        (∀ i j h a, g j (f i j h a) = g i a) ∧
        (∀ j a, φ (g j a) = ψ j a) ∧ P B φ ∧ ∃ b, φ b = x := by
    intro J _ _ A _ _ f _ ψ hψ hP x
    have : ∀ j, IsLocalRing (A j) := fun j ↦ (hP j).choose
    have hs := flat_local_tower_directLimit η hη A f ψ hψ
      (fun j ↦ (hP j).choose_spec.1)
      (fun j ↦ (hP j).choose_spec.2.1)
      (fun j ↦ (hP j).choose_spec.2.2.1)
      (fun j ↦ (hP j).choose_spec.2.2.2)
    obtain ⟨hlocal, _, hflat, hmax, hker⟩ := hs
    let S := DirectLimit A f
    let q : S →+* K := DirectLimit.Ring.lift A f K ψ hψ
    have hqcomp : q.comp (algebraMap R S) = η := by
      ext r
      let j : J := Classical.arbitrary J
      rw [RingHom.comp_apply, DirectLimit.algebraMap_def j]
      exact DFunLike.congr_fun ((hP j).choose_spec.2.2.2) r
    obtain ⟨B, _, hB, _, φ, hflatB, hmaxB, hkerB, hφ, hx⟩ :=
      exists_flat_local_monogenic_extension S K q hker x
    let β := algebraMap S B
    let : Algebra R B := (β.comp (algebraMap R S)).toAlgebra
    let g : ∀ j, A j →ₐ[R] B := fun j ↦
      { __ := β.comp (DirectLimit.Ring.of A f j)
        commutes' := fun r ↦ by
          change β (DirectLimit.Ring.of A f j (algebraMap R (A j) r)) =
            β (algebraMap R S r)
          congr 1
          exact (DirectLimit.Algebra.of A f j).commutes r }
    refine ⟨B, inferInstance, inferInstance, φ, g, ?_, ?_, ?_, hx⟩
    · intro i j h a
      change β (DirectLimit.Ring.of A f j (f i j h a)) =
        β (DirectLimit.Ring.of A f i a)
      rw [DirectLimit.Ring.of_f]
    · intro j a
      change φ (β (DirectLimit.Ring.of A f j a)) = ψ j a
      rw [← RingHom.comp_apply, hφ]
      rfl
    · refine ⟨hB, hflat.comp hflatB, ?_, hkerB, ?_⟩
      · change (maximalIdeal R).map (β.comp (algebraMap R S)) = maximalIdeal B
        rw [← Ideal.map_map, hmax]
        exact hmaxB
      · change φ.comp (β.comp (algebraMap R S)) = η
        rw [← RingHom.comp_assoc, hφ, hqcomp]
  obtain ⟨ord, A, rings, algebras, f, hsys, ψ, hcompat, hP, hstage⟩ :=
    exists_compatible_ring_tower R K (ULift.{u} K) ULift.down P hbase hstep
  let locals : ∀ i, IsLocalRing (A i) := fun i ↦ (hP i).choose
  refine ⟨ord, A, rings, locals, algebras, f, hsys, ψ, hcompat,
    (fun i ↦ (hP i).choose_spec.1), (fun i ↦ (hP i).choose_spec.2.1),
    (fun i ↦ (hP i).choose_spec.2.2.1),
    (fun i ↦ (hP i).choose_spec.2.2.2), ?_⟩
  intro x
  obtain ⟨a, ha⟩ := hstage (ULift.up x)
  exact ⟨ULift.up x, a, ha⟩

end IsLocalRing
