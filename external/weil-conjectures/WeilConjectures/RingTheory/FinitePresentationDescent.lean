/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Descent of finitely presented algebras along filtered colimits

If `A = colim A_i` is a filtered colimit of commutative rings and `B` is a finitely presented
`A`-algebra, then `B ≅ A ⊗[A_i] B_i` for some `i` and some finitely presented `A_i`-algebra
`B_i`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
  {c : Cocone F}

/-- Finitely many elements of a filtered colimit of commutative rings all come from a single
stage. -/
theorem exists_stage_of_finset (hc : IsColimit c) (s : Finset c.pt) :
    ∃ j : J, ∀ x ∈ s, x ∈ Set.range (c.ι.app j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨IsFiltered.nonempty.some, by simp⟩
  | insert x s _ ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, y, hy⟩ := Concrete.isColimit_exists_rep F hc x
    refine ⟨IsFiltered.max j k, fun z hz ↦ ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · refine ⟨F.map (IsFiltered.rightToMax j k) y, ?_⟩
      rw [← hy, ← c.w (IsFiltered.rightToMax j k)]
      rfl
    · obtain ⟨w, rfl⟩ := hj z hz
      refine ⟨F.map (IsFiltered.leftToMax j k) w, ?_⟩
      rw [← c.w (IsFiltered.leftToMax j k)]
      rfl

end CommRingCat

namespace Algebra

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
  {c : Cocone F}

/-- Blueprint `lem-kun-fp-algebra-descent`: let `A = colim_{i ∈ J} A_i` be a filtered colimit
of commutative rings and `B` a finitely presented `A`-algebra. Then there are a stage `i` and
a finitely presented `A_i`-algebra `B_i` with an isomorphism of `A`-algebras
`A ⊗[A_i] B_i ≅ B`.

Proof: write `B ≅ A[x_1, …, x_n] / (f_1, …, f_m)`. The finitely many coefficients of the `f_j`
come from a single stage `A_i`; lift the `f_j` to `g_j ∈ A_i[x_1, …, x_n]` and put
`B_i = A_i[x] / (g_j)`. Base change commutes with polynomial rings and with quotients. -/
theorem exists_finitePresentation_tensorProduct_algEquiv (hc : IsColimit c) (B : Type u)
    [CommRing B] [Algebra c.pt B] [FinitePresentation c.pt B] :
    ∃ i : J, letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      ∃ (Bi : Type u) (_ : CommRing Bi) (_ : Algebra (F.obj i) Bi),
        FinitePresentation (F.obj i) Bi ∧ Nonempty (c.pt ⊗[F.obj i] Bi ≃ₐ[c.pt] B) := by
  classical
  obtain ⟨n, I, e, hI⟩ := FinitePresentation.iff.1 (inferInstance : FinitePresentation c.pt B)
  obtain ⟨gens, hgens⟩ := hI
  obtain ⟨i, hi⟩ := CommRingCat.exists_stage_of_finset hc (gens.biUnion fun p ↦ p.coeffs)
  let φ : F.obj i →+* c.pt := (c.ι.app i).hom
  let := φ.toAlgebra
  have hlift (p : gens) : ∃ q : MvPolynomial (Fin n) (F.obj i), MvPolynomial.map φ q = p := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.2 fun a ha ↦ hi a ?_
    exact Finset.mem_biUnion.2 ⟨p, p.2, ha⟩
  choose q hq using hlift
  let Ii : Ideal (MvPolynomial (Fin n) (F.obj i)) := Ideal.span (Set.range q)
  have hIi : Ii.FG := ⟨(Finset.univ : Finset gens).image q, by simp [Ii]⟩
  refine ⟨i, _ ⧸ Ii, inferInstance, inferInstance, FinitePresentation.quotient hIi, ⟨?_⟩⟩
  let eP := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) (F.obj i) c.pt
  have heP (p : gens) :
      eP (Algebra.TensorProduct.includeRight (A := c.pt) (R := F.obj i) (q p)) = p := by
    rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul,
      one_smul, RingHom.algebraMap_toAlgebra, hq]
  have hmap : I = (Ii.map (Algebra.TensorProduct.includeRight (A := c.pt) (R := F.obj i))).map
      (eP : c.pt ⊗[F.obj i] MvPolynomial (Fin n) (F.obj i) →+* MvPolynomial (Fin n) c.pt) := by
    rw [Ideal.map_span, Ideal.map_span, Set.image_image, ← Set.range_comp, ← hgens]
    congr 1
    ext p
    refine ⟨fun hp ↦ ⟨⟨p, hp⟩, heP ⟨p, hp⟩⟩, ?_⟩
    rintro ⟨p, rfl⟩
    rw [Function.comp_apply, Finset.mem_coe]
    convert p.2 using 1
    exact heP p
  exact (Algebra.TensorProduct.tensorQuotientEquiv c.pt _ c.pt Ii).trans
    ((Ideal.quotientEquivAlg _ _ eP hmap).trans e)

end Algebra
