/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.ArtinianFlatSubalgebras
import WeilConjectures.RingTheory.PopescuFlatCoordinatesSetup

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra
/-- An admissible Artinian subalgebra containing a finite set in the prime-power quotient.
(blueprint: lem-weil-pbc-popescu-flat-coordinates-a0)

Source: Stacks Project, Tag 07FG, applied in the first paragraph of the proof of Tag 07FH.

Proof: Put L = Λ_q, J = qL and B = L/J^n. Localization preserves Noetherianity
and geometric regularity: after each finite purely inseparable field extension the base
change is a localization of a regular ring, hence regular. The prime q makes L local
with maximal ideal J. Since n ≥ 1, J^n is proper, and its radical is J; the quotient B
is Noetherian local with nilpotent maximal ideal, hence Artinian. Its residue field is
canonically the residue field K of L. The injectivity assertion of Tag 07E5 embeds
H1Cotangent k K in J/J². This conormal space is finite over K because J is finitely
generated; consequently H1Cotangent k K is finite. Transport this finiteness across the
residue-field isomorphism to B. Tag 07FG, as stated by
`exists_directed_artinian_flat_subalgebras`, supplies a directed covering family S of
subalgebras of B, each Artinian local, essentially of finite type, flat into B, and
whose maximal ideal extends to JB. Pick one member containing 0, so the family is
nonempty even when E is empty. Induct over the finite set E: for a new element choose
a member containing it and use directedness to find a member above this member and
the member already containing the preceding elements. The resulting member contains
all of E. Its four recorded properties are exactly `IsPopescuAdmissible JB`. -/
theorem exists_popescu_admissible_containing_finset
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∀ e ∈ E, e ∈ A := by
  let B := Localization.AtPrime q ⧸
    (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n
  obtain ⟨hArt, hLoc, hMax, hFin⟩ :=
    popescu_flat_coordinates_setup k Λ p hp hreg q n hn
  let : IsArtinianRing B := hArt
  let : IsLocalRing B := hLoc
  obtain ⟨S, hdir, hcover, hprops, _⟩ :=
    exists_directed_artinian_flat_subalgebras.{u, v, 0} k B p hp hFin
  have hnonempty : S.Nonempty := by
    obtain ⟨A, hA, hmem⟩ := hcover (0 : B)
    exact ⟨A, hA⟩
  have hfin : ∃ A ∈ S, ∀ e ∈ E, e ∈ A := by
    classical
    induction E using Finset.induction_on with
    | empty =>
        obtain ⟨A, hA⟩ := hnonempty
        exact ⟨A, hA, by simp⟩
    | @insert x s hx ih =>
        obtain ⟨A, hA, hs⟩ := ih
        obtain ⟨A', hA', hxA'⟩ := hcover x
        obtain ⟨C, hC, hAC, hA'C⟩ := hdir A hA A' hA'
        exact ⟨C, hC, fun e he ↦ by
          by_cases heq : e = x
          · simpa [heq] using hA'C hxA'
          · exact hAC (hs e (Finset.mem_of_mem_insert_of_ne he heq))⟩
  obtain ⟨A, hA, hE⟩ := hfin
  obtain ⟨hAloc, hAart, hAflat, hm, hAeft⟩ := hprops A hA
  let : IsLocalRing A := hAloc
  refine ⟨A, hAloc, ?_, hE⟩
  exact ⟨hAart, hAeft, ⟨hAloc, hAflat, hm.trans hMax⟩⟩

end Algebra
