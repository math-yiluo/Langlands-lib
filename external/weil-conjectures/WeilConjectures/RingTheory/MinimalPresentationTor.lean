/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MinimalGradedPresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.TorKernelBoundaryNaturality
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Tor one of a minimal finite graded free presentation

Source: stage-1 minimal-presentation refinement of the graded free resolution argument in
blueprint `theorem-riemann-roch-coherent-serre-duality`, proof;
Stacks Project, Algebra, Tag 00M0 and Section 00LY
(blueprint: lem-sc-p1-minimal-presentation-tor).
-/

@[expose] public section

universe v

open CategoryTheory

namespace MvPolynomial

private noncomputable def presentationResidueEquiv (k : Type v) [Field k] :
    let S := MvPolynomial (Fin 2) k
    let I : Ideal S := Ideal.span (Set.range (X : Fin 2 → S))
    (S ⧸ I) ≃ₗ[S]
      (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k) := by
  let S := MvPolynomial (Fin 2) k
  let I : Ideal S := Ideal.span (Set.range (X : Fin 2 → S))
  have hI : I ≤ RingHom.ker (constantCoeff : S →+* k) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X k i
  let f : (S ⧸ I) →+* k :=
    Ideal.Quotient.lift I constantCoeff (fun x hx => hI hx)
  have hm (p : S) : Ideal.Quotient.mk I (C (constantCoeff p)) =
      Ideal.Quotient.mk I p := by
    have he : (Ideal.Quotient.mk I).comp (C.comp constantCoeff) =
        Ideal.Quotient.mk I := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change Ideal.Quotient.mk I (C (constantCoeff (C r))) = _
        rw [constantCoeff_C]
      · intro i
        change Ideal.Quotient.mk I (C (constantCoeff (X i))) = _
        rw [constantCoeff_X, map_zero, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_range_self i))).symm
    exact DFunLike.congr_fun he p
  let g : (S ⧸ I) →ₗ[S]
      (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro r x
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
        change f (Ideal.Quotient.mk I (r * p)) = constantCoeff r * f _
        simp only [f, Ideal.Quotient.lift_mk, map_mul]
        rfl }
  exact LinearEquiv.ofBijective g ⟨by
    intro x y h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    change constantCoeff p = constantCoeff q at h
    rw [← hm p, ← hm q, h], by
    intro r
    refine ⟨Ideal.Quotient.mk I (C (R := k) (show k from r)), ?_⟩
    change constantCoeff (C (R := k) (show k from r)) = (show k from r)
    simp⟩

/-- Tor one is naturally isomorphic to the kernel modulo the irrelevant ideal for a minimal
finite graded free presentation. The equivalences are oriented from the kernel quotient to
Tor. Naturality is stated on quotient generators for every commuting square of graded
presentations, with `c` its induced kernel map. The zero-module consequence is included explicitly.

Source: stage-1 minimal-presentation refinement of the graded free resolution argument in
blueprint `theorem-riemann-roch-coherent-serre-duality`, proof;
Stacks Project, Algebra, Tag 00M0 and Section 00LY.

Proof: (1) Use `exists_tor_kernel_boundary_natural` for the short exact sequence
`0 → ker q → F → N → 0`, with second variable the residue field. Its boundary
is exact at Tor one and at the tensor of the kernel, and natural in presentation maps.
(2) Minimality implies `ker q ⊆ S₊F`. Every scalar in `S₊` has zero constant
coefficient, so it annihilates the residue field. Induction on ideal multiples shows
that `ker q ⊗ k → F ⊗ k` is zero. Exactness therefore makes the boundary surjective.
The homogeneous basis of `F` makes it projective, so its first Tor vanishes;
exactness at Tor one makes the boundary injective.
(3) Construct `S/S₊ ≃ₗ[S] k` using constant coefficient, with inverse induced by
constant polynomials. Compose Mathlib's tensor/quotient equivalence with this residue
identification and the inverse boundary to obtain the requested equivalences.
On a quotient generator the inverse tensor identification sends `[x]` to `x ⊗ 1`.
The boundary naturality square and this formula give the displayed naturality.
Finally transport subsingletonness along the injective equivalence.
(blueprint: lem-sc-p1-minimal-presentation-tor) -/
theorem exists_minimalPresentationTor_equiv (k : Type v) [Field k] :
    let S := MvPolynomial (Fin 2) k
    let I : Ideal S := Ideal.span (Set.range (X : Fin 2 → S))
    let residue : ModuleCat.{v} S :=
      (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k)
    let T := Tor' (ModuleCat.{v} S) 1
    ∃ e : ∀ P : MinimalGradedPresentation k,
        (LinearMap.ker P.q ⧸ (I • (⊤ : Submodule S (LinearMap.ker P.q)))) ≃ₗ[S]
          ((T.obj P.N).obj residue),
      (∀ P : MinimalGradedPresentation k,
        Subsingleton ((T.obj P.N).obj residue) →
          Subsingleton (LinearMap.ker P.q ⧸ (I • (⊤ : Submodule S (LinearMap.ker P.q))))) ∧
      (∀ (P Q : MinimalGradedPresentation k) (a : P.F →ₗ[S] Q.F)
          (b : P.N →ₗ[S] Q.N) (c : LinearMap.ker P.q →ₗ[S] LinearMap.ker Q.q),
        (∀ (j : ℤ) (x : P.F), x ∈ P.fGrading j → a x ∈ Q.fGrading j) →
        (∀ (j : ℤ) (x : P.N), x ∈ P.nGrading j → b x ∈ Q.nGrading j) →
        Q.q.comp a = b.comp P.q →
        (∀ x : LinearMap.ker P.q, (c x : Q.F) = a (x : P.F)) →
        ∀ x : LinearMap.ker P.q,
          ((T.map (ModuleCat.ofHom b)).app residue).hom
              (e P ((I • (⊤ : Submodule S (LinearMap.ker P.q))).mkQ x)) =
            e Q ((I • (⊤ : Submodule S (LinearMap.ker Q.q))).mkQ (c x))) := by
  classical
  dsimp only
  let S := MvPolynomial (Fin 2) k
  let I : Ideal S := Ideal.span (Set.range (X : Fin 2 → S))
  let residue : ModuleCat.{v} S :=
    (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k)
  let T := Tor' (ModuleCat.{v} S) 1
  let r := presentationResidueEquiv k
  let τ (M : ModuleCat.{v} S) : (TensorProduct S M residue) ≃ₗ[S] M ⧸ (I • ⊤) :=
    TensorProduct.congr (LinearEquiv.refl S M) r.symm ≪≫ₗ
      TensorProduct.tensorQuotEquivQuotSMul M I
  have hτ (M : ModuleCat.{v} S) (x : M) :
      (τ M).symm ((I • (⊤ : Submodule S M)).mkQ x) = TensorProduct.tmul S x (r 1) := by
    change (TensorProduct.congr (LinearEquiv.refl S M) r.symm).symm
      ((TensorProduct.tensorQuotEquivQuotSMul M I).symm
        (Submodule.Quotient.mk x)) = _
    rw [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]
    rfl
  obtain ⟨δ, hδ, hnat⟩ := exists_tor_kernel_boundary_natural S residue
  have hbij (P : MinimalGradedPresentation k) :
      Function.Bijective (δ P.F P.N P.q P.surjective) := by
    have : Projective P.F := ModuleCat.projective_of_free P.basis
    have hz := ModuleCat.subsingleton_of_isZero
      (isZero_Tor'_succ_of_projective (ModuleCat.{v} S) P.F residue 0)
    obtain ⟨he₁, he₂⟩ := hδ P.F P.N P.q P.surjective
    have hzero : (LinearMap.ker P.q).subtype.rTensor residue = 0 := by
      apply TensorProduct.ext'
      intro x z
      change TensorProduct.tmul S (x : P.F) z = 0
      have hx : (x : P.F) ∈ I • (⊤ : Submodule S P.F) :=
        P.minimal x (by rw [LinearMap.mem_ker.mp x.property]; exact Submodule.zero_mem _)
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr n _
        have hr₀ : constantCoeff r = 0 := by
          have hI : I ≤ RingHom.ker (constantCoeff : S →+* k) := by
            refine Ideal.span_le.mpr ?_
            rintro _ ⟨i, rfl⟩
            exact constantCoeff_X k i
          exact hI hr
        rw [TensorProduct.smul_tmul]
        have hz : r • z = 0 := by
          change constantCoeff r • (show k from z) = 0
          rw [hr₀, zero_smul]
        rw [hz, TensorProduct.tmul_zero]
      · intro y₁ y₂ h₁ h₂
        rw [TensorProduct.add_tmul, h₁, h₂, add_zero]
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy⟩ := (he₁ x).mp hx
        have : y = 0 := hz.elim y 0
        subst y
        rw [map_zero] at hy
        exact hy.symm
      · exact bot_le
    · intro y
      exact (he₂ y).mp (by rw [hzero]; rfl)
  let d (P : MinimalGradedPresentation k) :
      ((T.obj P.N).obj residue) ≃ₗ[S] (TensorProduct S (LinearMap.ker P.q) residue) :=
    LinearEquiv.ofBijective (δ P.F P.N P.q P.surjective) (hbij P)
  let e (P : MinimalGradedPresentation k) :
      (LinearMap.ker P.q ⧸ (I • ⊤)) ≃ₗ[S] ((T.obj P.N).obj residue) :=
    (τ (ModuleCat.of S (LinearMap.ker P.q))).symm ≪≫ₗ (d P).symm
  refine ⟨e, ?_, ?_⟩
  · intro P h
    exact ⟨fun x y => (e P).injective (h.elim _ _)⟩
  · intro P Q a b c _ _ hcomm hc x
    have hp : d P (e P ((I • (⊤ : Submodule S (LinearMap.ker P.q))).mkQ x)) =
        TensorProduct.tmul S x (r 1) := by
      change d P ((d P).symm ((τ (ModuleCat.of S (LinearMap.ker P.q))).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, hτ]
    have hq : d Q (e Q ((I • (⊤ : Submodule S (LinearMap.ker Q.q))).mkQ (c x))) =
        TensorProduct.tmul S (c x) (r 1) := by
      change d Q ((d Q).symm ((τ (ModuleCat.of S (LinearMap.ker Q.q))).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, hτ]
    apply (d Q).injective
    calc
      d Q (((T.map (ModuleCat.ofHom b)).app residue).hom
          (e P ((I • (⊤ : Submodule S (LinearMap.ker P.q))).mkQ x))) =
          c.rTensor residue
            (d P (e P ((I • (⊤ : Submodule S (LinearMap.ker P.q))).mkQ x))) :=
        hnat P.F P.N Q.F Q.N P.q Q.q P.surjective Q.surjective a b c hcomm hc _
      _ = TensorProduct.tmul S (c x) (r 1) := by rw [hp]; rfl
      _ = d Q (e Q ((I • (⊤ : Submodule S (LinearMap.ker Q.q))).mkQ (c x))) := hq.symm

end MvPolynomial
