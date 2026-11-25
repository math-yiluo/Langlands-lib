/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.StdBasis
import WeilConjectures.RingTheory.FiniteFreeResolution

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- The zero-step truncation in the finite-free resolution construction.
Source: Stacks Project, Algebra, Tag 00LP, part (2).
The identity complex with zero endpoints supplies the base case.
(blueprint: lem-weil-pbc-cm-local-free-resolution-construction-zero) -/
theorem exists_finite_free_resolution_data_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ S : ComposableArrows (ModuleCat.{max u v} R) (0 + 3),
      S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (0 + 3)) ∧
      Nonempty ((S.obj' (0 + 2)) ≃ₗ[R] M) ∧
      (∀ i : Fin 0,
        Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
        Module.Finite R (S.obj' (i.val + 2) (by omega))) := by
  let U := ModuleCat.of R (ULift.{max u v} M)
  let Z := ModuleCat.of R PUnit
  let z : Z ⟶ U := 0
  let e : U ⟶ U := 𝟙 _
  let S := ComposableArrows.mk₃ z e (0 : U ⟶ Z)
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · change (ComposableArrows.mk₃ (0 : Z ⟶ U) (𝟙 U) (0 : U ⟶ Z)).Exact
    apply ComposableArrows.exact_of_δ₀
    · apply ComposableArrows.exact₂_mk _ (by simp [ComposableArrows.Precomp.map])
      apply (CategoryTheory.ShortComplex.exact_iff_mono _ (by simp)).2
      change Mono (𝟙 U)
      infer_instance
    · apply ComposableArrows.exact₂_mk _ (by simp [ComposableArrows.Precomp.map])
      apply (CategoryTheory.ShortComplex.exact_iff_epi _ (by simp [ComposableArrows.Precomp.map])).2
      change Epi (𝟙 U)
      infer_instance
  · change IsZero Z
    exact ModuleCat.isZero_of_subsingleton _
  · change IsZero Z
    exact ModuleCat.isZero_of_subsingleton _
  · exact ⟨ULift.moduleEquiv⟩
  · intro i
    exact i.elim0

private def tailData {R : Type u} [Ring R]
    (F : ℕ → ModuleCat.{v} R) (d : ∀ k, F (k + 1) ⟶ F k)
    (M Z : ModuleCat.{v} R) (ε : F 0 ⟶ M) :
    (k : ℕ) → Σ S : ComposableArrows (ModuleCat.{v} R) (k + 1), F k ⟶ S.left
  | 0 => ⟨ComposableArrows.mk₁ (0 : M ⟶ Z), ε⟩
  | k + 1 =>
    let T := tailData F d M Z ε k
    ⟨T.1.precomp T.2, d k⟩
private def tail {R : Type u} [Ring R]
    (F : ℕ → ModuleCat.{v} R) (d : ∀ k, F (k + 1) ⟶ F k)
    (M Z : ModuleCat.{v} R) (ε : F 0 ⟶ M) (k : ℕ) :
    ComposableArrows (ModuleCat.{v} R) (k + 2) :=
  (tailData F d M Z ε k).1.precomp (tailData F d M Z ε k).2
private theorem tail_exact {R : Type u} [Ring R]
    (F : ℕ → ModuleCat.{v} R) (d : ∀ k, F (k + 1) ⟶ F k)
    (M Z : ModuleCat.{v} R) (ε : F 0 ⟶ M)
    (hε : Function.Surjective ε)
    (h₀ : LinearMap.range (d 0).hom = LinearMap.ker ε.hom)
    (hd : ∀ k, LinearMap.range (d (k + 1)).hom = LinearMap.ker (d k).hom)
    (k : ℕ) : (tail F d M Z ε k).Exact := by
  induction k with
  | zero =>
    change (ComposableArrows.mk₂ ε (0 : M ⟶ Z)).Exact
    apply ComposableArrows.exact₂_mk _ (by simp [ComposableArrows.Precomp.map])
    apply (ShortComplex.exact_iff_epi _ (by simp [ComposableArrows.Precomp.map])).2
    exact (ModuleCat.epi_iff_surjective ε).2 hε
  | succ k ih =>
    change ((tail F d M Z ε k).precomp (d k)).Exact
    refine ComposableArrows.exact_of_δ₀ (S :=
      (tail F d M Z ε k).precomp (d k)) ?_ ?_
    swap
    · exact ih
    cases k with
    | zero =>
      refine ComposableArrows.exact₂_mk _ ?_ ?_
      · change d 0 ≫ ε = 0
        ext x
        exact show ε (d 0 x) = 0 from
          (show d 0 x ∈ LinearMap.ker ε.hom from h₀ ▸ ⟨x, rfl⟩)
      · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
        exact h₀
    | succ k =>
      refine ComposableArrows.exact₂_mk _ ?_ ?_
      · change d (k + 1) ≫ d k = 0
        ext x
        exact show d k (d (k + 1) x) = 0 from
          (show d (k + 1) x ∈ LinearMap.ker (d k).hom from hd k ▸ ⟨x, rfl⟩)
      · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
        exact hd k

private theorem tail_obj_last {R : Type u} [Ring R]
    (F : ℕ → ModuleCat.{v} R) (d : ∀ k, F (k + 1) ⟶ F k)
    (M Z : ModuleCat.{v} R) (ε : F 0 ⟶ M) (k : ℕ) :
    (tail F d M Z ε k).obj' (k + 2) = Z := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

private theorem tail_obj_penultimate {R : Type u} [Ring R]
    (F : ℕ → ModuleCat.{v} R) (d : ∀ k, F (k + 1) ⟶ F k)
    (M Z : ModuleCat.{v} R) (ε : F 0 ⟶ M) (k : ℕ) :
    (tail F d M Z ε k).obj' (k + 1) = M := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

private theorem tail_free {R : Type u} [Ring R]
    (F : ℕ → ModuleCat.{v} R) (d : ∀ k, F (k + 1) ⟶ F k)
    (M Z : ModuleCat.{v} R) (ε : F 0 ⟶ M)
    (hf : ∀ k, Module.Free R (F k) ∧ Module.Finite R (F k))
    (k : ℕ) (i : ℕ) (hi : i ≤ k) :
    Module.Free R ((tail F d M Z ε k).obj' i (by omega)) ∧
    Module.Finite R ((tail F d M Z ε k).obj' i (by omega)) := by
  induction k generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact hf 0
  | succ k ih =>
    cases i with
    | zero => exact hf (k + 1)
    | succ i => exact ih i (by omega)


/-- The successor step, adjoining one finite-free presentation to a truncation.
Source: Stacks Project, Algebra, Tag 00LP, part (2).
The kernel of a finite free surjection is finite over a Noetherian ring and the
induction truncation is spliced to that presentation.
(blueprint: lem-weil-pbc-cm-local-free-resolution-construction-succ) -/
theorem exists_finite_free_resolution_data_succ
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (k : ℕ) :
    ∃ S : ComposableArrows (ModuleCat.{max u v} R) (k + 1 + 3),
      S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (k + 1 + 3)) ∧
      Nonempty ((S.obj' (k + 1 + 2)) ≃ₗ[R] M) ∧
      (∀ i : Fin (k + 1),
        Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
        Module.Finite R (S.obj' (i.val + 2) (by omega))) := by
  obtain ⟨n, ε, d, hε, h₀, hd⟩ := Module.exists_finite_free_resolution R M
  let U := ModuleCat.of R (ULift.{max u v} M)
  let Z := ModuleCat.of R PUnit
  let F (i : ℕ) := ModuleCat.of R (ULift.{max u v} (Fin (n i) → R))
  let ε' : F 0 ⟶ U := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap.comp (ε.comp ULift.moduleEquiv.toLinearMap))
  let d' (i : ℕ) : F (i + 1) ⟶ F i := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap.comp ((d i).comp ULift.moduleEquiv.toLinearMap))
  have hε' : Function.Surjective ε' := by
    intro ⟨x⟩
    obtain ⟨y, hy⟩ := hε x
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  have h₀' : LinearMap.range (d' 0).hom = LinearMap.ker ε'.hom := by
    ext ⟨x⟩
    change (∃ y : F 1, ULift.up (d 0 y.down) = ULift.up x) ↔ ULift.up (ε x) = 0
    constructor
    · rintro ⟨⟨y⟩, hy⟩
      have hy' : d 0 y = x := congrArg ULift.down hy
      have hx : ε x = 0 := by
        rw [← hy']
        exact show d 0 y ∈ LinearMap.ker ε from
          h₀.symm ▸ (show d 0 y ∈ LinearMap.range (d 0) from ⟨y, rfl⟩)
      exact congrArg ULift.up hx
    · intro hx
      have hx' : ε x = 0 := congrArg ULift.down hx
      obtain ⟨y, hy⟩ := (show x ∈ LinearMap.range (d 0) from h₀ ▸ hx')
      exact ⟨ULift.up y, congrArg ULift.up hy⟩
  have hd' : ∀ i, LinearMap.range (d' (i + 1)).hom = LinearMap.ker (d' i).hom := by
    intro i
    ext ⟨x⟩
    change (∃ y : F (i + 2), ULift.up (d (i + 1) y.down) = ULift.up x) ↔ ULift.up (d i x) = 0
    constructor
    · rintro ⟨⟨y⟩, hy⟩
      have hy' : d (i + 1) y = x := congrArg ULift.down hy
      have hx : d i x = 0 := by
        rw [← hy']
        exact show d (i + 1) y ∈ LinearMap.ker (d i) from
          (hd i).symm ▸
            (show d (i + 1) y ∈ LinearMap.range (d (i + 1)) from ⟨y, rfl⟩)
      exact congrArg ULift.up hx
    · intro hx
      have hx' : d i x = 0 := congrArg ULift.down hx
      obtain ⟨y, hy⟩ := (show x ∈ LinearMap.range (d (i + 1)) from hd i ▸ hx')
      exact ⟨ULift.up y, congrArg ULift.up hy⟩
  let T := tail F d' U Z ε' k
  let g := T.map' 0 1
  let K := ModuleCat.of R (LinearMap.ker g.hom)
  let ι : K ⟶ T.left := ModuleCat.ofHom (LinearMap.ker g.hom).subtype
  let S := (T.precomp ι).precomp (0 : Z ⟶ K)
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · apply ComposableArrows.exact_of_δ₀ (S := S)
    · refine ComposableArrows.exact₂_mk _ ?_ ?_
      · change (0 : Z ⟶ K) ≫ ι = 0
        simp
      · apply (ShortComplex.exact_iff_mono _ (by
          change (0 : Z ⟶ K) = 0
          rfl)).2
        change Mono ι
        exact (ModuleCat.mono_iff_injective ι).2 Subtype.val_injective
    · apply ComposableArrows.exact_of_δ₀ (S := T.precomp ι)
      · refine ComposableArrows.exact₂_mk _ ?_ ?_
        · change ι ≫ g = 0
          ext x
          exact x.property
        · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
          change LinearMap.range (LinearMap.ker g.hom).subtype = LinearMap.ker g.hom
          exact Submodule.range_subtype _
      · exact tail_exact F d' U Z ε' hε' h₀' hd' k
  · change IsZero Z
    exact ModuleCat.isZero_of_subsingleton _
  · change IsZero (T.obj' (k + 2))
    rw [tail_obj_last]
    exact ModuleCat.isZero_of_subsingleton _
  · change Nonempty ((T.obj' (k + 1)) ≃ₗ[R] M)
    rw [tail_obj_penultimate]
    exact ⟨ULift.moduleEquiv⟩
  · intro i
    change Module.Free R (T.obj' i.val (by omega)) ∧
      Module.Finite R (T.obj' i.val (by omega))
    exact tail_free F d' U Z ε' (fun j ↦ ⟨inferInstance, inferInstance⟩) k i.val
      (by omega)

/-- A finite free sequence of any prescribed length, with an unrestricted left kernel.
Source: Stacks Project, Algebra, Tag 00LP, part (2), the finite truncation of its
successive finite-free-surjection construction
(blueprint: lem-weil-pbc-cm-local-free-resolution-construction).

Proof: Induct on `k`, for all finite modules `M`, including the zero module.
At `k = 0`, take `0 → ULift M → ULift M → 0`, with the identity middle map and
`ULift.moduleEquiv` identifying the penultimate object with `M`. For the successor
step choose finite generators of `M` and the associated surjection `F → M` from a
finite free module. Its kernel `N` is finite because it is a submodule of a finite
module over a Noetherian ring. Apply the induction hypothesis to `N`. Replace that
sequence's terminal `N → 0` by `N → F → M → 0`, using the kernel inclusion and the
chosen surjection. Exactness at `N` follows from injectivity of the kernel inclusion;
at `F` it follows from image(kernel inclusion) = kernel(surjection); at `M` it follows
from surjectivity. The preceding terms keep their exactness and finite freeness.
Lift all modules into universe `max u v` and conjugate the maps by the lift
isomorphisms. This preserves exactness and finite freeness and gives the asserted
module equivalence. No assertion about depth or Cohen--Macaulayness is involved. -/
theorem exists_finite_free_resolution_data
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (k : ℕ) :
    ∃ S : ComposableArrows (ModuleCat.{max u v} R) (k + 3),
      S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (k + 3)) ∧
      Nonempty ((S.obj' (k + 2)) ≃ₗ[R] M) ∧
      (∀ i : Fin k,
        Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
        Module.Finite R (S.obj' (i.val + 2) (by omega))) := by
  induction k with
  | zero => simpa using exists_finite_free_resolution_data_zero M
  | succ k =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        exists_finite_free_resolution_data_succ M k

end IsLocalRing
