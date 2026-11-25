/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology

/-!
# The Noetherian cohomology criterion for pseudo-coherence

Source: Stacks Project, More on Algebra, Tag 066E,
lemma-Noetherian-pseudo-coherent, clause (2)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Over a commutative Noetherian ring, pseudo-coherence is equivalent to bounded-above,
finite cohomology. No lower cohomology bound or Tor-dimension assumption is imposed.

Source: Stacks Project, More on Algebra, Tag 066E,
lemma-Noetherian-pseudo-coherent, clause (2)
(auxiliary; not a blueprint node).

Proof plan:
1. Unpack `def-pc-ring-pseudo-coherent-complex`: choose a bounded-above finite-free
   complex `E` and an isomorphism from `Q.obj E` to `K`. Above its term bound, its
   cohomology, and hence that of `K`, vanishes.
2. Each cycle module is a submodule of a finite free module. By
   `lem-weil-pbc-noetherian-submodule-finite`, it is finitely generated. Project its
   generators to the quotient by the boundaries and then transport them through the
   cohomology isomorphism to obtain finite generation of every cohomology module of `K`.
3. Conversely, resolve each finite cohomology module by finite free modules using
   `lem-weil-pbc-finite-free-resolution-noetherian`. Put resolution term `j` in degree
   `-j`, with zero positive terms. The augmentation is a cochain map to the module in
   degree zero: exactness gives zero negative cohomology, the required module in degree
   zero, and zero positive cohomology. It is therefore a quasi-isomorphism, exhibiting
   the degree-zero cohomology module as pseudo-coherent.
4. Apply `lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent` with the given
   upper bound and the pseudo-coherent cohomology modules from step 3. This proves that
   `K` is pseudo-coherent (the pseudo-coherent clause of Tag 066B used in Tag 066E). -/
theorem isPseudoCoherent_iff_boundedAbove_finite_homology
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    IsPseudoCoherent K ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat R) i).obj K)) ∧
        ∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat R) i).obj K) := by
  constructor
  · rintro ⟨E, b, hbound, hterms, ⟨e⟩⟩
    have := hbound
    have hfinite (i : ℤ) : Module.Finite R (E.X i) := (hterms i).2
    constructor
    · refine ⟨b, fun i hi ↦ ?_⟩
      exact (isZero_of_isLE (Q.obj E) b i hi).of_iso
        ((homologyFunctor (ModuleCat R) i).mapIso e).symm
    · intro i
      have : Module.Finite R (E.cycles i) :=
        Module.Finite.of_injective (E.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      have : Module.Finite R (E.homology i) :=
        Module.Finite.of_surjective (E.homologyπ i).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      let φ : E.homology i ≅ (homologyFunctor (ModuleCat R) i).obj K :=
        ((homologyFunctorFactors (ModuleCat R) i).app E).symm ≪≫
        (homologyFunctor (ModuleCat R) i).mapIso e
      exact Module.Finite.of_surjective φ.hom.hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  · rintro ⟨hbound, hfinite⟩
    apply isPseudoCoherent_of_homology R K hbound
    intro i
    have := hfinite i
    classical
    -- Lift the finite free resolution into the universe of the cohomology modules.
    let M := (homologyFunctor (ModuleCat R) i).obj K
    obtain ⟨n, ε, d, hε, hker, hd⟩ := Module.exists_finite_free_resolution R M
    let X (j : ℕ) : ModuleCat.{max u v} R :=
      ModuleCat.of R (ULift.{v} (Fin (n j) → R))
    let e (j : ℕ) : X j ≃ₗ[R] (Fin (n j) → R) := ULift.moduleEquiv
    let δ (j : ℕ) : X (j + 1) ⟶ X j :=
      ModuleCat.ofHom ((e j).symm.toLinearMap ∘ₗ d j ∘ₗ (e (j + 1)).toLinearMap)
    have sq (j : ℕ) : δ (j + 1) ≫ δ j = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (e j).symm (d j (d (j + 1) (e (j + 2) x))) = 0
      have h : d (j + 1) (e (j + 2) x) ∈ LinearMap.ker (d j) := by
        rw [hd j]
        exact ⟨_, rfl⟩
      rw [LinearMap.mem_ker] at h
      rw [h, map_zero]
    let C := ChainComplex.of X δ sq
    have cd (j : ℕ) : C.d (j + 1) j = δ j := ChainComplex.of_d X δ j
    have hex (j : ℕ) : C.ExactAt (j + 1) := by
      rw [HomologicalComplex.exactAt_iff' C (j + 2) (j + 1) j (by simp) (by simp)]
      simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', cd]
      apply (ShortComplex.moduleCat_exact_iff _).2
      intro x hx
      have hx' : e (j + 1) x ∈ LinearMap.ker (d j) := by
        change (e j).symm (d j (e (j + 1) x)) = 0 at hx
        simpa using congrArg (e j) hx
      rw [hd j] at hx'
      obtain ⟨y, hy⟩ := hx'
      refine ⟨(e (j + 2)).symm y, ?_⟩
      change (e (j + 1)).symm (d (j + 1) y) = x
      rw [hy, LinearEquiv.symm_apply_apply]
    let ε' : C.X 0 ⟶ M := ModuleCat.ofHom (ε ∘ₗ (e 0).toLinearMap)
    have hw : C.d 1 0 ≫ ε' = 0 := by
      rw [cd]
      ext x
      change ε (d 0 (e 1 x)) = 0
      have h : d 0 (e 1 x) ∈ LinearMap.ker ε := by
        rw [hker]
        exact ⟨_, rfl⟩
      exact h
    have hex₀ : (ShortComplex.mk (C.d 1 0) ε' hw).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).2
      intro x hx
      have hx' : e 0 x ∈ LinearMap.ker ε := hx
      rw [hker] at hx'
      obtain ⟨y, hy⟩ := hx'
      refine ⟨(e 1).symm y, ?_⟩
      change (e 0).symm (d 0 y) = x
      rw [hy, LinearEquiv.symm_apply_apply]
    have hepi : Epi ε' := by
      apply (ModuleCat.epi_iff_surjective _).2
      intro x
      obtain ⟨y, hy⟩ := hε x
      exact ⟨(e 0).symm y, hy⟩
    -- Exactness in positive chain degrees and the augmentation give a quasi-isomorphism.
    let π := (ChainComplex.toSingle₀Equiv C M).symm ⟨ε', hw⟩
    have hπ : QuasiIso π := by
      constructor
      intro j
      cases j with
      | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · exact ⟨hex₀, hepi⟩
        all_goals rfl
      | succ j =>
        rw [quasiIsoAt_iff_exactAt' π (j + 1)
          (ChainComplex.exactAt_succ_single_obj _ _)]
        exact hex j
    have hfree (j : ℕ) : Module.Free R (C.X j) :=
      Module.Free.of_equiv (e j).symm
    have hfin (j : ℕ) : Module.Finite R (C.X j) :=
      Module.Finite.equiv (e j).symm
    let P : ProjectiveResolution M :=
      { complex := C
        π := π
        quasiIso := hπ
        projective := fun j ↦ by
          have := hfree j
          infer_instance }
    -- Extend by zero to positive cochain degrees, retaining finite free terms.
    refine ⟨P.cochainComplex, 0, inferInstance, ?_,
      ⟨asIso (Q.map P.π')⟩⟩
    intro j
    by_cases hj : j ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hj
      have := hfree k
      have := hfin k
      let t := (P.cochainComplexXIso (-k) k).symm.toLinearEquiv
      exact ⟨Module.Free.of_equiv t, Module.Finite.equiv t⟩
    · have : Subsingleton (P.cochainComplex.X j) :=
        ModuleCat.subsingleton_of_isZero
          (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j (by omega))
      exact ⟨inferInstance, inferInstance⟩

end DerivedCategory
