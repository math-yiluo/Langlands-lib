/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.CohenMacaulayFreeResolutionConstruction
import WeilConjectures.RingTheory.ProjectiveResolutionKernelProjective
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeExactSequenceResolution

/-! Bounded finite free resolution construction.
(blueprint: stage3-b4-bounded-finite-free-resolution) -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat
/-- Construction from the infinite finite-free resolution and the projective d-th syzygy.
Source: Stacks Project, Algebra, Tag 0CXF.
Proof:
If `d = 0`, the augmentation of the given length-zero projective resolution is an
isomorphism, so `M` is projective. A finite projective module over a local ring is free
(Tag 00NX); put `M` in degree zero, with identity augmentation and zero terms above it.
If `d > 0`, use Tag 00LP to resolve `M` by finite free modules. Let `K` be the kernel
of the map out of degree `d - 1`, using the augmentation when `d = 1`. Tag 00O5 and
the given length bound imply that `K` is projective. Since it is a submodule of a finite
module over a Noetherian ring, it is finite (Tag 00IK), and hence free by Tag 00NX.
Replace the term of degree `d` by `K`, with differential the kernel inclusion, and
put zero modules above degree `d`. Exactness at degree `d - 1` follows from the
kernel-image equality, and at degree `d` from injectivity of the inclusion. Exactness
in lower degrees and surjectivity of the augmentation are inherited. All terms are
projective since they are free, so the augmented complex gives a ProjectiveResolution.
The zero modules are finite and free as well.
(blueprint: stage3-b4-bounded-finite-free-resolution) -/
theorem exists_bounded_finite_free_resolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (d : ℕ) (h : HasProjectiveResolutionLE M d) :
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) := by
  classical
  cases d with
  | zero =>
    let : Module.Projective R M := projective_of_projective_resolution_length_zero M h
    let : Module.Free R M := Module.free_of_flat_of_isLocalRing
    refine ⟨ProjectiveResolution.self M, ?_, ?_⟩
    · intro i hi
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    · intro i
      cases i with
      | zero =>
        change Module.Finite R (((ChainComplex.single₀ _).obj M).X 0) ∧
          Module.Free R (((ChainComplex.single₀ _).obj M).X 0)
        rw [ChainComplex.single₀_obj_zero]
        exact ⟨inferInstance, inferInstance⟩
      | succ i =>
        have hz : IsZero ((ProjectiveResolution.self M).complex.X (i + 1)) :=
          HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
        let := ModuleCat.subsingleton_of_isZero hz
        exact ⟨inferInstance, inferInstance⟩
  | succ k =>
    obtain ⟨T, hT, hzero, hlast, ⟨e⟩, hfree⟩ :=
      IsLocalRing.exists_finite_free_resolution_data (R := R) M (k + 1)
    let S := (ComposableArrows.natAddLEFunctor
      (n := k + 1 + 3) (k := 2) (l := k + 1) (by omega)).obj T
    let j : T.obj' 1 ⟶ S.left := T.map' 1 2
    have hj : Mono j := (hT.exact 0).mono_g (hzero.eq_of_src _ _)
    let := hj
    have hpre : (S.precomp j).Exact := by
      refine ComposableArrows.exact_of_δ₀ ?_ ?_
      · refine ComposableArrows.exact₂_mk _ ?_ ?_
        · change T.map' 1 2 ≫ T.map' 2 3 = 0
          exact hT.toIsComplex.zero 1
        · exact hT.exact 1
      · exact ComposableArrows.natAddLEFunctor_obj_exact _ hT
    have hepi : Epi (S.map' k (k + 1)) := by
      change Epi (T.map' (2 + k) (2 + (k + 1)))
      have hg : T.map' (2 + (k + 1)) (k + 4) = 0 := hlast.eq_of_tgt _ _
      exact (hT.exact' (2 + k) (2 + (k + 1)) (k + 4)
        (by omega) (by omega) (by omega)).epi_f hg
    let := hepi
    have hM : HasProjectiveResolutionLE S.right (k + 1) := by
      change HasProjectiveResolutionLE (T.obj' (2 + (k + 1))) (k + 1)
      have he : 2 + (k + 1) = k + 1 + 2 := by omega
      simp only [ComposableArrows.obj', he]
      obtain ⟨P, hP⟩ := h
      let Q : ProjectiveResolution (T.obj' (k + 1 + 2)) :=
        { complex := P.complex
          projective := P.projective
          π := P.π ≫ (ChainComplex.single₀ _).map e.toModuleIso.inv }
      exact ⟨Q, hP⟩
    have hF (i : ℕ) (hi : i < k + 1) :
        Module.Projective R (S.obj' i (Nat.le_of_lt hi)) := by
      change Module.Projective R (T.obj' (2 + i) (by omega))
      have he : 2 + i = i + 2 := by omega
      have heX : T.obj' (2 + i) (by omega) = T.obj' (i + 2) (by omega) := by
        exact congrArg T.obj (Fin.ext he)
      rw [heX]
      let : Module.Free R (T.obj' (i + 2) (by omega)) := (hfree ⟨i, hi⟩).1
      infer_instance
    let : Epi (S.map' ((k + 1) - 1) (k + 1)) := by
      simpa only [Nat.add_sub_cancel] using hepi
    let : Module.Projective R (T.obj' 1) :=
      projective_of_exact_partial_projective_resolution (k + 1) (by omega)
        S hM _ j hpre hF
    let : Module.Finite R S.left := (hfree ⟨0, by omega⟩).2
    let : Module.Finite R (T.obj' 1) :=
      Module.Finite.of_injective j.hom ((ModuleCat.mono_iff_injective j).1 hj)
    let : Module.Free R (T.obj' 1) := Module.free_of_flat_of_isLocalRing
    have hf (i : ℕ) (hi : i ≤ k + 1) :
        Module.Finite R (T.obj' (i + 1) (by omega)) ∧
          Module.Free R (T.obj' (i + 1) (by omega)) := by
      cases i with
      | zero => exact ⟨inferInstance, inferInstance⟩
      | succ i =>
        have hi' : i < k + 1 := by omega
        exact ⟨(hfree ⟨i, hi'⟩).2, (hfree ⟨i, hi'⟩).1⟩
    obtain ⟨P, hP, hfin⟩ :=
      exists_bounded_finite_free_resolution_of_exact_sequence (k + 1) T hT hzero hlast hf
    let Q : ProjectiveResolution M :=
      { complex := P.complex
        projective := P.projective
        π := P.π ≫ (ChainComplex.single₀ _).map e.toModuleIso.hom }
    exact ⟨Q, hP, hfin⟩
end ModuleCat
