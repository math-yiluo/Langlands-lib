/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.RingTheory.MinimalPresentationTor
import WeilConjectures.RingTheory.GradedKernelFinite
import WeilConjectures.RingTheory.GradedNakayamaGeneration
import WeilConjectures.RingTheory.MinimalGradedPresentationExists
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Graded Nakayama freeness criterion

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, proof, graded Nakayama criterion
applied to `K_2` (blueprint: lem-sc-p1-graded-nakayama-free).
-/

@[expose] public section

universe u

open CategoryTheory

namespace MvPolynomial

private theorem homogeneous_submodule_internal {R M : Type u} [Ring R]
    [AddCommGroup M] [Module R M] (ℳ : ℤ → AddSubgroup M)
    (hℳ : DirectSum.IsInternal ℳ) (K : Submodule R M)
    (hK : letI := hℳ.chooseDecomposition; K.IsHomogeneous ℳ) :
    DirectSum.IsInternal (fun j ↦ (ℳ j).comap K.subtype.toAddMonoidHom) := by
  classical
  let := hℳ.chooseDecomposition
  let 𝒦 := fun j ↦ (ℳ j).comap K.subtype.toAddMonoidHom
  let incl : ∀ j, 𝒦 j →+ ℳ j := fun j ↦
    { toFun := fun x ↦ ⟨x.val.val, x.property⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have comm : ∀ x : DirectSum ℤ (fun j ↦ 𝒦 j),
      DirectSum.coeAddMonoidHom ℳ (DirectSum.map incl x) =
        K.subtype (DirectSum.coeAddMonoidHom 𝒦 x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j x => simp [incl]
    | add x y hx hy => simp [hx, hy]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply (DirectSum.map_injective incl).mpr ?_ (hℳ.injective ?_)
    · intro j x y h
      apply Subtype.ext
      exact Subtype.ext (congrArg (fun z : ℳ j ↦ z.val) h)
    · rw [comm, comm, hxy]
  · intro x
    let c : ∀ j, 𝒦 j := fun j ↦
      ⟨⟨(DirectSum.decompose ℳ x.val j).val, hK j x.property⟩,
        (DirectSum.decompose ℳ x.val j).property⟩
    refine ⟨∑ j ∈ (DirectSum.decompose ℳ x.val).support, DirectSum.of (fun j ↦ ↥(𝒦 j)) j (c j), ?_⟩
    apply Subtype.ext
    change K.subtype (DirectSum.coeAddMonoidHom 𝒦 _) = x.val
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    change (∑ j ∈ (DirectSum.decompose ℳ x.val).support,
      (DirectSum.decompose ℳ x.val j : M)) = x.val
    exact DirectSum.sum_support_decompose ℳ x.val

/-- A finitely generated graded module over `k[x₀,x₁]` whose first Tor with the residue
field vanishes has a finite homogeneous basis.

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, proof, graded Nakayama criterion
applied to `K_2`.

Proof: choose homogeneous lifts of a basis modulo the irrelevant ideal and form the minimal
finite graded free presentation. The minimal-presentation Tor calculation identifies the first
Tor with the kernel modulo the irrelevant ideal. Its vanishing and finite graded generation of
the kernel imply that the kernel is zero by graded Nakayama, so the presentation is an
isomorphism. The source basis then gives the asserted finite homogeneous basis.
(blueprint: lem-sc-p1-graded-nakayama-free) -/
theorem graded_nakayama_free (k : Type u) [Field k]
    (N : Type u) [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        f • x ∈ ℳ ((n : ℤ) + j))
    (hN : ∃ s : Set N, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (hTor : Subsingleton (((Tor' (ModuleCat.{u} (MvPolynomial (Fin 2) k)) 1).obj
      (ModuleCat.of (MvPolynomial (Fin 2) k) N)).obj
      ((ModuleCat.restrictScalars
        (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k)).obj
        (ModuleCat.of k k)))) :
    ∃ (r : ℕ) (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) N)
      (d : Fin r → ℤ), ∀ i : Fin r, b i ∈ ℳ (d i) := by
  classical
  obtain ⟨F, ℱ, hF, hsmulF, r, b, d, hb, q, hq, hgraded, hmin⟩ :=
    exists_minimal_graded_presentation k N ℳ hℳ hsmul hN
  let P : MinimalGradedPresentation k :=
    { N := ModuleCat.of (MvPolynomial (Fin 2) k) N
      F := F
      nGrading := ℳ
      fGrading := ℱ
      nDecomposition := hℳ
      finite := hN
      fDecomposition := hF
      n_smul := hsmul
      f_smul := hsmulF
      rank := r
      basis := b
      degree := d
      basis_mem := hb
      q := q
      surjective := hq
      graded := hgraded
      minimal := hmin }
  have hfiniteF : ∃ s : Set F, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℱ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤ := by
    refine ⟨Set.range b, Set.finite_range b, ?_, ?_⟩
    · rintro x ⟨i, rfl⟩
      exact ⟨d i, hb i⟩
    · exact b.span_eq
  obtain ⟨hK, s, hs, _, hspan⟩ :=
    graded_kernel_finite ℱ hF ℳ hℳ hsmulF hfiniteF q hgraded
  let : Module.Finite (MvPolynomial (Fin 2) k) q.ker :=
    Module.Finite.of_fg (hspan ▸ Submodule.fg_span hs)
  let 𝒦 : ℤ → AddSubgroup q.ker := fun j ↦ (ℱ j).comap q.ker.subtype.toAddMonoidHom
  have h𝒦 : DirectSum.IsInternal 𝒦 := homogeneous_submodule_internal ℱ hF q.ker hK
  have hsmulK : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : q.ker),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒦 j →
        f • x ∈ 𝒦 ((n : ℤ) + j) := by
    intro n j f x hf hx
    exact hsmulF n j f x.val hf hx
  obtain ⟨_, hzero, _⟩ := exists_minimalPresentationTor_equiv k
  have hquot := hzero P hTor
  let : Subsingleton q.ker :=
    subsingleton_of_graded_quotient_subsingleton 𝒦 h𝒦 hsmulK hquot
  have hinj : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  let e : F ≃ₗ[MvPolynomial (Fin 2) k] N := LinearEquiv.ofBijective q ⟨hinj, hq⟩
  refine ⟨r, b.map e, d, ?_⟩
  intro i
  simpa [e] using hgraded (d i) (b i) (hb i)

end MvPolynomial
