/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! Finite prime-chain contraction in filtered colimits.

Source: Stacks Project, More on Algebra, Tag 06LK.
(blueprint: lem-sc-filtered-colimit-prime-chain-contraction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A finite prime chain in a filtered colimit contracts strictly at one stage.
The proof chooses separating elements, represents them in stages, and uses filteredness
to dominate the finitely many stages. Contractions of primes remain prime, and the
separating representatives preserve strictness.
(blueprint: lem-sc-filtered-colimit-prime-chain-contraction) -/
theorem filteredColimit_prime_chain_contraction
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) :
    ∀ (n : ℕ) (p : Fin (n + 1) → Ideal (colimit R : CommRingCat.{u})),
      (∀ j, (p j).IsPrime) → StrictMono p →
      ∃ i : I,
        (∀ j, (Ideal.comap (colimit.ι R i).hom (p j)).IsPrime) ∧
        StrictMono (fun j ↦ Ideal.comap (colimit.ι R i).hom (p j)) := by
  classical
  intro n p hp hmono
  let P := {q : Fin (n + 1) × Fin (n + 1) // q.1 < q.2}
  have hsep (q : P) : ∃ x ∈ p q.val.2, x ∉ p q.val.1 :=
    IsConcreteLE.exists_of_lt (hmono q.property)
  choose x hx hn using hsep
  have hrep (q : P) : ∃ (i : I) (y : R.obj i), (colimit.ι R i).hom y = x q :=
    Concrete.colimit_exists_rep R (x q)
  choose i y hy using hrep
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (q : P) : i q ⟶ k := (hk (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩)).some
  have hstage (q : P) : (colimit.ι R k).hom ((R.map (f q)).hom (y q)) = x q := by
    calc
      (colimit.ι R k).hom ((R.map (f q)).hom (y q)) =
          (colimit.ι R (i q)).hom (y q) :=
        DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (colimit.w R (f q))) (y q)
      _ = x q := hy q
  refine ⟨k, ?_, ?_⟩
  · intro j
    exact @Ideal.comap_isPrime _ _ _ _ _ _ (colimit.ι R k).hom (p j) _ (hp j)
  · intro a b hab
    refine lt_of_le_not_ge (Ideal.comap_mono (hmono hab).le) ?_
    intro hba
    let q : P := ⟨(a, b), hab⟩
    have hmem : (R.map (f q)).hom (y q) ∈ Ideal.comap (colimit.ι R k).hom (p b) := by
      change (colimit.ι R k).hom ((R.map (f q)).hom (y q)) ∈ p b
      rw [hstage q]
      exact hx q
    have hnot := hn q
    apply hnot
    have := hba hmem
    change (colimit.ι R k).hom ((R.map (f q)).hom (y q)) ∈ p a at this
    rwa [hstage q] at this

end CommRingCat
