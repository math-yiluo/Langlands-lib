/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3
public import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Localization.Cardinality

/-! # Cardinality of the principal w-localization

Source: Stacks Project, Tag 0976 (blueprint: lem-weil-pbc-principal-w-localization-size).
-/

@[expose] public section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

private theorem list_bound {X : Type u} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hX : #X ≤ κ) :
    #(List X) ≤ κ :=
  (mk_list_le_max X).trans (max_le hκ hX)

theorem finset_bound {X : Type u} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hX : #X ≤ κ) :
    #(Finset X) ≤ κ := by
  classical
  exact (mk_le_of_surjective (f := List.toFinset) (fun s ↦ ⟨s.toList, by simp⟩)).trans
    (list_bound hκ hX)

theorem sigma_bound {I : Type u} {X : I → Type u} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) (hX : ∀ i, #(X i) ≤ κ) : #(Σ i, X i) ≤ κ := by
  rw [mk_sigma]
  exact (sum_le_mk_mul_iSup _).trans
    (mul_le_of_le hκ hI (ciSup_le' hX))

private theorem finite_pi_bound {I : Type u} [Finite I] {X : I → Type u}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hX : ∀ i, #(X i) ≤ κ) : #(∀ i, X i) ≤ κ := by
  let := Fintype.ofFinite I
  rw [mk_pi]
  exact (prod_le_prod _ _ hX).trans (by simpa using power_nat_le (n := Fintype.card I) hκ)

private theorem basic_data_bound (R : Type u) [CommRing R] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) : #(PrimeSpectrum.BasicConstructibleSetData R) ≤ κ := by
  let f : PrimeSpectrum.BasicConstructibleSetData R → R × List R :=
    fun C ↦ (C.f, List.ofFn C.g)
  have hf : Function.Injective f := by
    intro C D h
    have h₁ : C.f = D.f := congrArg Prod.fst h
    have h₂ : List.ofFn C.g = List.ofFn D.g := congrArg Prod.snd h
    have hn : C.n = D.n := by simpa using congrArg List.length h₂
    cases C
    cases D
    dsimp at h₁ hn h₂
    subst hn
    congr
    exact List.ofFn_injective h₂
  refine (mk_le_of_injective hf).trans ?_
  rw [mk_prod, lift_id, lift_id]
  exact mul_le_of_le hκ hR (list_bound hκ hR)

private theorem constructible_bound (R : Type u) [CommRing R] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) :
    #{E : Set (PrimeSpectrum R) // Topology.IsConstructible E} ≤ κ := by
  let f : PrimeSpectrum.ConstructibleSetData R →
      {E : Set (PrimeSpectrum R) // Topology.IsConstructible E} :=
    fun C ↦ ⟨C.toSet, C.isConstructible_toSet⟩
  have hf : Function.Surjective f := by
    intro E
    obtain ⟨C, hC⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr E.property
    exact ⟨C, Subtype.ext hC⟩
  exact (mk_le_of_surjective hf).trans (finset_bound hκ (basic_data_bound R κ hκ hR))

private noncomputable def indexCode {R : Type u} [CommRing R] (i : Index R) :
    Finset ({E : Set (PrimeSpectrum R) // Topology.IsConstructible E} × R) := by
  classical
  exact i.parts.attach.image (fun E ↦ (⟨E.val, i.constructible E.val E.property⟩,
    i.denominator E))

private theorem indexCode_injective {R : Type u} [CommRing R] :
    Function.Injective (indexCode (R := R)) := by
  classical
  intro i j hij
  have hp : i.parts = j.parts := by
    ext E
    constructor
    · intro hE
      have hmem : (⟨E, i.constructible E hE⟩, i.denominator ⟨E, hE⟩) ∈ indexCode j := by
        rw [← hij]
        exact Finset.mem_image.mpr ⟨⟨E, hE⟩, by simp, rfl⟩
      obtain ⟨F, _, hF⟩ := Finset.mem_image.mp hmem
      have heq : F.val = E := congrArg (fun x ↦ x.1.val) hF
      exact heq ▸ F.property
    · intro hE
      have hmem : (⟨E, j.constructible E hE⟩, j.denominator ⟨E, hE⟩) ∈ indexCode i := by
        rw [hij]
        exact Finset.mem_image.mpr ⟨⟨E, hE⟩, by simp, rfl⟩
      obtain ⟨F, _, hF⟩ := Finset.mem_image.mp hmem
      have heq : F.val = E := congrArg (fun x ↦ x.1.val) hF
      exact heq ▸ F.property
  cases i with
  | mk pi ni ci qi di vi =>
    cases j with
    | mk pj nj cj qj dj vj =>
      dsimp at hp
      subst pj
      have hd : di = dj := by
        funext E
        have hmem : (⟨E.val, ci E.val E.property⟩, di E) ∈
            indexCode ⟨pi, nj, cj, qj, dj, vj⟩ := by
          rw [← hij]
          exact Finset.mem_image.mpr ⟨E, by simp, rfl⟩
        obtain ⟨F, _, hF⟩ := Finset.mem_image.mp hmem
        have heq : F = E := Subtype.ext (congrArg (fun x ↦ x.1.val) hF)
        subst F
        exact (congrArg Prod.snd hF).symm
      subst dj
      rfl

private theorem index_bound (R : Type u) [CommRing R] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) : #(Index R) ≤ κ := by
  refine (mk_le_of_injective (indexCode_injective (R := R))).trans (finset_bound hκ ?_)
  rw [mk_prod, lift_id, lift_id]
  exact mul_le_of_le hκ (constructible_bound R κ hκ hR) hR

/-- Principal w-localization preserves any infinite cardinal bound.
Source: Stacks Project, Tag 0976 (blueprint: lem-weil-pbc-principal-w-localization-size).

Proof: constructible sets are finite unions of basic constructible sets, encoded by a ring
coefficient and a finite list of coefficients. An index is a finite constructible partition
with one denominator per part. Finite products of its principal localizations have the same
infinite bound, since localization does not increase cardinality. Every element of the
filtered colimit is represented at a stage. The disjoint union of stages therefore surjects
onto the colimit and has the required bound. -/
theorem cardinalMk_le (R : Type u) [CommRing R] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) : #(algebra R) ≤ κ := by
  have hstage (i : Index R) : #(Stage i) ≤ κ :=
    finite_pi_bound hκ (fun E ↦
      (IsLocalization.cardinalMk_le (L := Localization.Away (i.denominator E))
        (Submonoid.powers (i.denominator E))).trans hR)
  have hsurj := Concrete.from_union_surjective_of_isColimit
    (diagram (A := R)) (colimit.isColimit (diagram (A := R)))
  exact (mk_le_of_surjective hsurj).trans
    (sigma_bound hκ (index_bound R κ hκ hR) hstage)

end PrincipalWLocalization
