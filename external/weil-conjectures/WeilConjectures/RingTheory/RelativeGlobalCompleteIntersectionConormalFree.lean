/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence

/-!
# Conormal basis of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma 00SV (3)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-conormal-free).
-/

@[expose] public section

universe v

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- Ideal generators span the conormal module over the quotient ring. -/
private theorem span_conormal_generators (D : Type v) [CommRing D]
    (c : ℕ) (f : Fin c → D) :
    Submodule.span (D ⧸ Ideal.span (Set.range f))
      (Set.range fun j ↦ (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) = ⊤ := by
  let I := Ideal.span (Set.range f)
  let e : Fin c → I.Cotangent := fun j ↦
    I.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩
  have hD : Submodule.span D (Set.range e) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
    refine Submodule.span_induction
      (p := fun z hz ↦ I.toCotangent ⟨z, hz⟩ ∈ Submodule.span D (Set.range e))
      ?_ ?_ ?_ ?_ x.property
    · rintro z ⟨j, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self j)
    · change I.toCotangent 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy hxx hyy
      change I.toCotangent (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hxx hyy
    · intro r x hx hxx
      change I.toCotangent (r • ⟨x, hx⟩) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ r hxx
  apply (Submodule.restrictScalars_eq_top_iff D (D ⧸ I) I.Cotangent).mp
  rw [Submodule.restrictScalars_span D (D ⧸ I) Ideal.Quotient.mk_surjective]
  exact hD

set_option backward.isDefEq.respectTransparency false in
/-- A linear combination of equation classes is the class of the lifted combination. -/
private theorem conormal_sum (D : Type v) [CommRing D] (c : ℕ) (f a : Fin c → D) :
    let I := Ideal.span (Set.range f)
    ∑ j, Ideal.Quotient.mk I (a j) •
        I.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩ =
      I.toCotangent (∑ j, a j •
        (⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩ : I)) := by
  dsimp only
  rw [map_sum]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- A conormal basis detects the coefficients of a relation modulo the square. -/
private theorem coefficients_mem_of_conormal_basis (D : Type v) [CommRing D]
    (c : ℕ) (f a : Fin c → D)
    (b : Module.Basis (Fin c) (D ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j, b j = (Ideal.span (Set.range f)).toCotangent
      ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩)
    (ha : ∑ j, a j * f j ∈ Ideal.span (Set.range f) ^ 2) :
    ∀ j, a j ∈ Ideal.span (Set.range f) := by
  let I := Ideal.span (Set.range f)
  have hz : ∑ j, Ideal.Quotient.mk I (a j) • b j = 0 := by
    simp_rw [hb]
    rw [conormal_sum, Ideal.toCotangent_eq_zero]
    simpa only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul] using ha
  intro j
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ hz j)

set_option backward.isDefEq.respectTransparency false in
/-- Local conormal bases detect every coefficient by maximal-localization ideal membership. -/
private theorem coefficients_mem_of_locally_regular (D : Type v) [CommRing D]
    (c : ℕ) (f a : Fin c → D)
    (hreg : ∀ (m : Ideal D) [m.IsPrime], Ideal.span (Set.range f) ≤ m →
      RingTheory.Sequence.IsRegular (Localization.AtPrime m)
        (List.ofFn fun j ↦ algebraMap D (Localization.AtPrime m) (f j)))
    (ha : ∑ j, a j * f j ∈ Ideal.span (Set.range f) ^ 2) :
    ∀ j, a j ∈ Ideal.span (Set.range f) := by
  let I := Ideal.span (Set.range f)
  intro j
  apply Ideal.mem_of_localization_maximal
  intro m hm
  have : m.IsMaximal := hm
  by_cases hle : I ≤ m
  · let B := Localization.AtPrime m
    let g : Fin c → B := fun j ↦ algebraMap D B (f j)
    have hmap : I.map (algebraMap D B) = Ideal.span (Set.range g) := by
      rw [Ideal.map_span]
      congr 1
      exact Set.range_comp (algebraMap D B) f |>.symm
    obtain ⟨_, ⟨b, hb⟩, _⟩ :=
      RingTheory.Sequence.regularSequence_conormal_free B c g (hreg m hle)
    have ha' : ∑ j, algebraMap D B (a j) * g j ∈ Ideal.span (Set.range g) ^ 2 := by
      have hh := Ideal.mem_map_of_mem (algebraMap D B) ha
      rw [Ideal.map_pow, hmap] at hh
      simpa only [map_sum, map_mul] using hh
    rw [hmap]
    exact coefficients_mem_of_conormal_basis B c g (fun j ↦ algebraMap D B (a j))
      b hb ha' j
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime m) hle]
    exact Submodule.mem_top

/-- The equation classes form a basis of the conormal module of the specified relative global
complete intersection; hence it is free and isomorphic to the finite direct sum of `c`
copies of the quotient ring. Source: Stacks Project, Algebra, Lemma 00SV (3)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-conormal-free).

Proof:
1. The classes `e_j` span `I/I²`: use ideal-span induction on a representative in `I`
   and then restrict scalars from `P` to `P/I`.
2. At a maximal ideal `m` of `P` containing `I`, its image in `P/I` is prime and has
   inverse image `m`. Apply 00SV (1) to obtain regularity in `P_m`.
3. By 00LN, the localized equations have a conormal basis. If `∑ a_j f_j ∈ I²`,
   map this relation to `P_m`. Linear independence of that basis implies every
   `a_j/1` belongs to the ideal generated by the localized equations.
4. If `m` does not contain `I`, the extended ideal is the unit ideal. Thus each
   coefficient belongs to the extended ideal at every maximal ideal. Mathlib's
   `Ideal.mem_of_localization_maximal` (00HN (1) for `P/I`) gives `a_j ∈ I`.
5. Lift the coefficients of a relation among the `e_j` to `P`. Step 4 makes all
   quotient coefficients zero. Combine this linear independence with step 1 using
   `Module.Basis.mk`, and obtain freeness and the isomorphism from that basis.
   Empty equation families and the zero quotient require no separate cases. -/
theorem relativeGlobalCompleteIntersection_conormal_free
    {R : Type v} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f) :
    (∃ b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent,
      ∀ j : Fin c, b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) ∧
    Module.Free (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent ∧
    Nonempty ((Ideal.span (Set.range f)).Cotangent ≃ₗ[
      MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)]
      (Fin c → (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) := by
  classical
  let P := MvPolynomial (Fin n) R
  let I := Ideal.span (Set.range f)
  let e : Fin c → I.Cotangent := fun j ↦
    I.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩
  have hreg : ∀ (m : Ideal P) [m.IsPrime], I ≤ m →
      RingTheory.Sequence.IsRegular (Localization.AtPrime m)
        (List.ofFn fun j ↦ algebraMap P (Localization.AtPrime m) (f j)) := by
    intro m hm hle
    let q := m.map (Ideal.Quotient.mk I)
    have : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
    have heq : q.comap (Ideal.Quotient.mk I) = m := Ideal.comap_map_mk hle
    have hr := isRegular_localization_of_relativeGlobalCompleteIntersection f h q
    change RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))
      (List.ofFn fun i ↦ algebraMap P
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) (f i)) at hr
    have transport : ∀ (m' : Ideal P) [m'.IsPrime],
        m' = q.comap (Ideal.Quotient.mk I) →
        RingTheory.Sequence.IsRegular (Localization.AtPrime m')
          (List.ofFn fun i ↦ algebraMap P (Localization.AtPrime m') (f i)) := by
      intro m' hm' he
      subst m'
      exact hr
    exact transport m heq.symm
  have hli : LinearIndependent (P ⧸ I) e := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha j
    choose t ht using fun i ↦ Ideal.Quotient.mk_surjective (a i)
    have hz : I.toCotangent (∑ i, t i •
        (⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ : I)) = 0 := by
      rw [← conormal_sum]
      change ∑ i, Ideal.Quotient.mk I (t i) • e i = 0
      calc
        _ = ∑ i, a i • e i := Finset.sum_congr rfl fun i _ ↦
          congrArg (fun z : P ⧸ I ↦ z • e i) (ht i)
        _ = 0 := ha
    have hsq : ∑ i, t i * f i ∈ I ^ 2 := by
      rw [Ideal.toCotangent_eq_zero] at hz
      simpa only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul] using hz
    rw [← ht j]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (coefficients_mem_of_locally_regular P c f t hreg hsq j)
  let b : Module.Basis (Fin c) (P ⧸ I) I.Cotangent :=
    Module.Basis.mk hli (span_conormal_generators P c f).ge
  refine ⟨⟨b, ?_⟩, Module.Free.of_basis b, ⟨b.equivFun⟩⟩
  exact Module.Basis.mk_apply _ _

end Algebra
