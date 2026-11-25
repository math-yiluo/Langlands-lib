/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.PopescuSmoothing
import Mathlib.Algebra.Category.Ring.FinitePresentation

/-! # Factoring polynomial solutions through a smooth algebra

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 0AH5, second paragraph.
(blueprint: lem-weil-pbc-smooth-polynomial-factorization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- A finite polynomial solution along a regular map factors through a smooth algebra.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 0AH5, second paragraph;
Theorem 07GC and Algebra Lemma 00QO.
(blueprint: lem-weil-pbc-smooth-polynomial-factorization).

Proof: put C = A[X_1,...,X_n]/(f_1,...,f_m). Evaluation at the given solution
kills the ideal of equations and therefore induces an A-algebra map C to Λ.
C is finitely presented, since there are finitely many variables and equations.
Popescu smoothing expresses Λ as a filtered colimit in commutative rings of
smooth A-algebras with A-algebra coprojections. The finite-presentation
factorization lemma factors C to Λ through one stage B, by an A-algebra map.
Take b_k to be the image of X_k in B. The defining relations give f_j(b) = 0,
and commutativity with the coprojection ψ gives ψ(b_k) = a_k.
This argument also covers no variables and no equations by the empty
polynomial presentation. No henselian hypothesis or approximation is used.
-/
theorem exists_smooth_polynomial_factorization
    {A Λ : Type u} [CommRing A] [CommRing Λ] [Algebra A Λ]
    [IsNoetherianRing A] [IsNoetherianRing Λ]
    (hreg : RingHom.IsRegular (algebraMap A Λ)) {m n : ℕ}
    (f : Fin m → MvPolynomial (Fin n) A) (a : Fin n → Λ)
    (hzero : ∀ j, MvPolynomial.eval₂ (algebraMap A Λ) a (f j) = 0) :
    ∃ (B : CommAlgCat.{u} A),
      Smooth (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) ∧
      ∃ (ψ : B →ₐ[A] Λ) (b : Fin n → B),
        (∀ j, MvPolynomial.eval₂ (algebraMap A B) b (f j) = 0) ∧
        (∀ k, ψ (b k) = a k) := by
  classical
  let K := Ideal.span (Set.range f)
  have hK : K.FG := Submodule.fg_span (Set.finite_range f)
  let C := MvPolynomial (Fin n) A ⧸ K
  have : Algebra.FinitePresentation A C := Algebra.FinitePresentation.quotient hK
  let ev := MvPolynomial.aeval (R := A) a
  have hkill : ∀ x ∈ K, ev x = 0 := by
    have hle : K ≤ RingHom.ker ev.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hzero j
    exact fun x hx ↦ hle hx
  let g := Ideal.Quotient.liftₐ K ev hkill
  obtain ⟨J, hcat, hfiltered, B, hB, ι, ⟨hc⟩⟩ := RingHom.popescu_smoothing hreg
  let F := B ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}
  let α : (Functor.const J).obj (CommRingCat.of A) ⟶ F :=
    { app := fun j ↦ CommRingCat.ofHom (algebraMap A (B.obj j))
      naturality := by intro i j h; ext x; exact ((B.map h).hom.commutes x).symm }
  obtain ⟨j, g', hg'A, hg'⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (CommRingCat.of A) F α (CommRingCat.ofHom (algebraMap A C))
      ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).mapCocone
        { pt := CommAlgCat.of A Λ, ι := ι }) hc
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (CommRingCat.ofHom g.toRingHom) (by
        intro j
        ext x
        exact (g.commutes x).trans ((ι.app j).hom.commutes x).symm)
  let gA : C →ₐ[A] B.obj j :=
    { g'.hom with commutes' := fun x ↦ congrArg (fun h ↦ h.hom x) hg'A }
  let b := fun k ↦ gA (Ideal.Quotient.mk K (MvPolynomial.X k))
  refine ⟨B.obj j, ?_, (ι.app j).hom, b, ?_, ?_⟩
  · exact hB j
  · intro i
    let t := gA.comp (Ideal.Quotient.mkₐ A K)
    have he := MvPolynomial.eval₂_comp_left t.toRingHom
      MvPolynomial.C MvPolynomial.X (f i)
    have hcC : t.toRingHom.comp MvPolynomial.C = algebraMap A (B.obj j) := by
      ext x
      exact t.commutes x
    have hz : t (f i) = 0 := by
      change gA (Ideal.Quotient.mk K (f i)) = 0
      have hfmem : f i ∈ K := Ideal.subset_span (Set.mem_range_self i)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hfmem, map_zero]
    rw [MvPolynomial.eval₂_eta, hcC] at he
    exact he.symm.trans hz
  · intro k
    have hh := congrArg (fun h ↦ h.hom (Ideal.Quotient.mk K (MvPolynomial.X k))) hg'
    change g (Ideal.Quotient.mk K (MvPolynomial.X k)) =
      (ι.app j).hom (b k) at hh
    simpa [g, ev] using hh.symm
