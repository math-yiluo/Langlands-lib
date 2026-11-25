/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Projective kernels in partial projective resolutions

Source: Stacks Project, Algebra, Lemma 00O5 and its proof using Schanuel's Lemma 00O3
(blueprint: lem-weil-pbc-projective-resolution-kernel-projective).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

private theorem kernel_dimension
    {C : Type*} [Category C] [Abelian C] (e n : ℕ)
    (S : ComposableArrows C (e + 1))
    (hM : HasProjectiveDimensionLT S.right (n + e + 2))
    (hS : S.Exact) [Epi (S.map' e (e + 1))]
    (hF : ∀ (i : ℕ) (hi : i < e + 1), Projective (S.obj' i (Nat.le_of_lt hi))) :
    HasProjectiveDimensionLT (kernel (S.map' 0 1)) (n + 1) := by
  induction e generalizing n with
  | zero =>
      let := hF 0 (by omega)
      let T := ShortComplex.mk (kernel.ι (S.map' 0 1)) (S.map' 0 1)
        (kernel.condition _)
      have hT : T.ShortExact := { exact := ShortComplex.exact_kernel _ }
      exact hT.hasProjectiveDimensionLT_X₁ (n + 1)
        (hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)) hM
  | succ e ih =>
      have hep : Epi (S.δ₀.map' e (e + 1)) := by
        simpa [ComposableArrows.map', ComposableArrows.δ₀,
          ComposableArrows.δ₀Functor] using
          (inferInstance : Epi (S.map' e.succ (e.succ + 1) (Nat.le_succ _) le_rfl))
      have htail : HasProjectiveDimensionLT (kernel (S.map' 1 2)) (n + 2) := by
        apply ih (n + 1) S.δ₀
        · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm, ComposableArrows.right, ComposableArrows.obj',
            ComposableArrows.δ₀, ComposableArrows.δ₀Functor,
            ComposableArrows.whiskerLeftFunctor, ComposableArrows.whiskerLeft,
            Functor.comp_obj, Fin.succFunctor_obj, Fin.succ_mk] using hM
        · exact hS.δ₀
        · intro i hi
          exact hF (i + 1) (by omega)
      let g := S.map' 1 2
      let f := kernel.lift g (S.map' 0 1) (hS.zero 0)
      have hf : Epi f := (S.sc hS.toIsComplex 0).exact_iff_epi_kernel_lift.mp
        (hS.exact 0)
      let := hf
      let := hF 0 (by omega)
      let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hT : T.ShortExact := { exact := ShortComplex.exact_kernel f }
      have hk : HasProjectiveDimensionLT (kernel f) (n + 1) :=
        hT.hasProjectiveDimensionLT_X₁ (n + 1)
          (hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)) htail
      let := hk
      exact hasProjectiveDimensionLT_of_iso
        ((kernelCompMono f (kernel.ι g)).symm ≪≫
          kernelIsoOfEq (show f ≫ kernel.ι g = S.map' 0 1 from
            kernel.lift_ι _ _ _)) (n + 1)

/-- The kernel of the first arrow of `F_e → ... → F_0 → M` is projective if
`M` has a projective resolution of length at most `d` and `d ≤ e + 1`.
The objects of `S` are indexed from the left, so `S.right` is `M` and
`S.map' 0 1` is `F_e → F_{e-1}`, or `F_0 → M` when `e = 0`.
Exactness at `M` is the epimorphism hypothesis; no exactness at `F_e` is imposed.

Source: Stacks Project, Algebra, Lemma 00O5
(blueprint: lem-weil-pbc-projective-resolution-kernel-projective).

Proof plan, following the node's Steps 1–8:
1. Induct on `d` with the claim for all bounds `e ≥ max(0,d-1)` and modules
   admitting a resolution of length at most `d`.
2. For `d = 0`, the augmentation of a length-zero resolution is an isomorphism,
   so `M` is projective (lem-weil-pbc-projective-direct-summand).
3. Split `F_0 → M` (lem-weil-pbc-ses-projective-quotient-splits). Its kernel is
   a projective direct summand; replace `M` by that kernel and induct on `e`.
4. For `d > 0`, choose a length-`d` resolution `P` and use
   lem-weil-pbc-schanuel to identify `K_0 ⊕ P_0` with `L_0 ⊕ F_0`, where
   `K_0 = ker(F_0 → M)` and `L_0 = ker(P_0 → M)`.
5. If `e = 0`, then `d = 1` and `L_0 ≅ P_1`. Thus `K_0 ⊕ P_0` is projective
   by lem-weil-pbc-projective-direct-sum, and its summand `K_0` is projective.
6. Otherwise resolve `L_0 ⊕ F_0` by `P_1 ⊕ F_0` followed by `P_2,...,P_d`.
   Exactness follows from that of `P`; transport along Schanuel to obtain a
   resolution of `N = K_0 ⊕ P_0` of length at most `d-1`.
7. The sequence ending in `F_1 ⊕ P_0 → N`, preceded by `F_2,...,F_e`, is
   exact: the last map is `(x,p) ↦ (∂_1 x,p)` and the preceding map is
   `x ↦ (∂_2 x,0)`. All terms are projective. Apply the induction hypothesis
   to `N`, since `e-1 ≥ max(0,d-2)`.
8. For `e ≥ 3` the resulting kernel is the original kernel. For `e = 2` the
   extra zero component does not change it; for `e = 1` it is isomorphic to
   `ker(∂_1)` via `x ↦ (x,0)`. Use invariance under isomorphisms
   (lem-weil-pbc-projective-direct-summand) to finish. -/
theorem projective_kernel_of_partial_projective_resolution
    {R : Type u} [CommRing R] (d e : ℕ)
    (S : ComposableArrows (ModuleCat.{max u v} R) (e + 1))
    (hM : HasProjectiveResolutionLE S.right d) (he : d ≤ e + 1)
    (hS : S.Exact) [Epi (S.map' e (e + 1))]
    (hF : ∀ (i : ℕ) (hi : i < e + 1),
      Module.Projective R (S.obj' i (Nat.le_of_lt hi))) :
    Module.Projective R (kernel (C := ModuleCat.{max u v} R) (S.map' 0 1)) := by
  have := HasExt.standard (ModuleCat.{max u v} R)
  obtain ⟨P, hP⟩ := hM
  have hdim : HasProjectiveDimensionLT S.right (e + 2) := by
    apply HasProjectiveDimensionLT.mk
    intro i hi Y x
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective x (i + 1) (by omega)
    have hfzero : f = 0 := (hP i (by omega)).eq_of_src _ _
    subst f
    exact P.extMk_zero _ _
  have hcat : ∀ i (hi : i < e + 1),
      Projective (S.obj' i (Nat.le_of_lt hi)) := by
    intro i hi
    let := hF i hi
    infer_instance
  have hk : HasProjectiveDimensionLT (kernel (S.map' 0 1)) 1 :=
    kernel_dimension e 0 S (by simpa using hdim) hS hcat
  let := hk
  infer_instance

/-- In an exact sequence `0 → K → F_{d-1} → ... → F_0 → M → 0`, with
`d ≥ 1`, all `F_i` projective, and `M` admitting a projective resolution of
length at most `d`, the module `K` is projective.

Source: Stacks Project, Algebra, Lemma 00O5, particular case
(blueprint: lem-weil-pbc-projective-resolution-kernel-projective).

Proof (node Step 9): apply the kernel assertion with `e = d-1` to `S`.
Exactness of `S.precomp j` and injectivity of `j` identify `K` with the kernel
of the first arrow of `S`. Transfer projectivity along that isomorphism using
lem-weil-pbc-projective-direct-summand. -/
theorem projective_of_exact_partial_projective_resolution
    {R : Type u} [CommRing R] (d : ℕ) (hd : 1 ≤ d)
    (S : ComposableArrows (ModuleCat.{max u v} R) d)
    (hM : HasProjectiveResolutionLE S.right d)
    (K : ModuleCat.{max u v} R) (j : K ⟶ S.left) [Mono j]
    (hS : (S.precomp j).Exact) [Epi (S.map' (d - 1) d)]
    (hF : ∀ (i : ℕ) (hi : i < d),
      Module.Projective R (S.obj' i (Nat.le_of_lt hi))) :
    Module.Projective R K := by
  cases d with
  | zero => omega
  | succ e =>
      have hep : Epi (S.map' e (e + 1)) := by
        simpa using (inferInstance : Epi (S.map' (e.succ - 1) e.succ (Nat.sub_le _ _) le_rfl))
      have hker := projective_kernel_of_partial_projective_resolution
        (e + 1) e S hM (by omega) hS.δ₀ hF
      let := hker
      have hkcat : CategoryTheory.Projective (kernel (S.map' 0 1)) := inferInstance
      let T := (S.precomp j).sc hS.toIsComplex 0
      have hT : T.Exact := hS.exact 0
      have hm : Mono T.f := by
        change Mono j
        infer_instance
      let iso := hT.fIsKernel.conePointUniqueUpToIso (kernelIsKernel (S.map' 0 1))
      have hp : CategoryTheory.Projective K := Projective.of_iso iso.symm hkcat
      let := hp
      infer_instance

/-- A module admitting a length-zero projective resolution is projective.
Source: Stacks Project, Algebra, proof of Lemma 00O5, case `d = 0`
(blueprint: lem-weil-pbc-projective-resolution-kernel-projective).

Proof (node Steps 2 and 9): the resolution is `0 → P_0 → M → 0`, so its
augmentation is both injective and surjective. It gives an isomorphism from
projective `P_0` to `M`; use lem-weil-pbc-projective-direct-summand (2). -/
theorem projective_of_projective_resolution_length_zero
    {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R)
    (hM : HasProjectiveResolutionLE M 0) : Module.Projective R M := by
  obtain ⟨P, hP⟩ := hM
  have hd : P.complex.d 1 0 = 0 := (hP 1 (by omega)).eq_of_src _ _
  have hi : CategoryTheory.IsIso (P.π.f 0) :=
    CategoryTheory.Limits.CokernelCofork.IsColimit.isIso_π
      P.cokernelCofork P.isColimitCokernelCofork hd
  have hp : CategoryTheory.Projective M :=
    CategoryTheory.Projective.of_iso (CategoryTheory.asIso (P.π.f 0)) (P.projective 0)
  let := hp
  infer_instance

end ModuleCat
