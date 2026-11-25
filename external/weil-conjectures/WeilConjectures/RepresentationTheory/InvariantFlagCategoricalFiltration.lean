/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Realizing an invariant flag in the category of representations

Source: Stacks Project, Tag 0A3R, the passage from an invariant flag to successive
extensions of the trivial rank-one representation.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace Rep

private theorem cokernel_inclusion_iso_quotient
    {k : Type*} [Field k] {P : Type u} [Group P] (M : Rep.{v} k P)
    (A B : Submodule k M.V) (hA : ∀ g, A ≤ A.comap (M.ρ g))
    (hB : ∀ g, B ≤ B.comap (M.ρ g)) (hle : A ≤ B) :
    let S := M.subrepresentation A hA
    let S' := M.subrepresentation B hB
    let f : S ⟶ S' := Rep.ofHom ⟨Submodule.inclusion hle, fun _ ↦ rfl⟩
    let K := A.comap B.subtype
    let hK : ∀ g, K ≤ K.comap (S'.ρ g) := fun g _x hx ↦ hA g hx
    Nonempty (cokernel f ≅ S'.quotient K hK) := by
  intro S S' f K hK
  let q := S'.mkQ K hK
  have hcomp : f ≫ q = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero K).2 x.property
  let C := ShortComplex.mk f q hcomp
  have hex : C.Exact := by
    rw [← C.exact_map_iff_of_faithful (forget₂ (Rep k P) (ModuleCat k))]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : B, K.mkQ x = 0 → ∃ y : A, Submodule.inclusion hle y = x
    intro x hx
    have hx' : x ∈ K := (Submodule.Quotient.mk_eq_zero K).1 hx
    exact ⟨⟨x.val, hx'⟩, Subtype.ext rfl⟩
  have hepi : Epi q := (Rep.epi_iff_surjective q).2 K.mkQ_surjective
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso hex.gIsCokernel⟩

/-- Realize a stable vector-space flag with trivial rank-one factors as categorical
monomorphisms and cokernels. This is independent of the existence of a Sylow cover.

Source: Stacks Project, `etale-cohomology.tex`, Lemma 0A3R
(`lemma-pullback-filtered`), the representation-filtration step.
(blueprint: lemma-reduction-unipotent-local-system--1)

Proof: Put n = dim M and replace F i by F (min i n). These spaces are stable,
since their indices are at most n. Equip each with the restricted representation.
For i < n use the inclusion F i → F (i+1); thereafter use identities. The initial
representation is zero because F 0 = 0, and the final representation is M because
F n = M. The cokernel of an inclusion is the quotient representation
F (i+1)/F i. Its dimension is one: induction using the given dimensions shows
that dim F i = i, including the base dim F 0 = 0. The condition g*x-x ∈ F i
makes its action trivial. Choose a basis of this one-dimensional quotient to
identify it with the trivial representation ULift (ZMod ℓ). The cokernel universal
property in Rep is the equivariant linear-map universal property of this quotient.
For n = 0 use the zero representation throughout; there are no quotient conditions. -/
theorem exists_categorical_filtration_of_invariant_flag
    (ℓ : ℕ) [Fact ℓ.Prime] (P : Type u) [Group P]
    (M : Rep.{v} (ZMod ℓ) P) [FiniteDimensional (ZMod ℓ) M.V]
    (F : ℕ → Submodule (ZMod ℓ) M.V)
    (h0 : F 0 = ⊥) (hn : F (Module.finrank (ZMod ℓ) M.V) = ⊤)
    (hstable : ∀ i ≤ Module.finrank (ZMod ℓ) M.V, ∀ g, F i ≤ (F i).comap (M.ρ g))
    (hstep : ∀ i < Module.finrank (ZMod ℓ) M.V,
      F i ≤ F (i + 1) ∧ Module.finrank (ZMod ℓ) (F (i + 1)) = i + 1 ∧
        ∀ g, ∀ x ∈ F (i + 1), M.ρ g x - x ∈ F i) :
    ∃ (W : ℕ → Rep.{v} (ZMod ℓ) P) (ι : ∀ i, W i ⟶ W (i + 1)),
      IsZero (W 0) ∧ Nonempty (W (Module.finrank (ZMod ℓ) M.V) ≅ M) ∧
      ∀ i < Module.finrank (ZMod ℓ) M.V, Mono (ι i) ∧
        Nonempty (cokernel (ι i) ≅ Rep.trivial (ZMod ℓ) P (ULift.{v} (ZMod ℓ))) := by
  classical
  let n := Module.finrank (ZMod ℓ) M.V
  let B (i : ℕ) := F (min i n)
  have hB (i : ℕ) : ∀ g, B i ≤ (B i).comap (M.ρ g) :=
    hstable _ (Nat.min_le_right _ _)
  have hle (i : ℕ) : B i ≤ B (i + 1) := by
    by_cases hi : i < n
    · simpa [B, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi] using (hstep i hi).1
    · simp [B, Nat.min_eq_right (by omega : n ≤ i),
        Nat.min_eq_right (by omega : n ≤ i + 1)]
  let W (i : ℕ) := M.subrepresentation (B i) (hB i)
  let ι (i : ℕ) : W i ⟶ W (i + 1) :=
    Rep.ofHom ⟨Submodule.inclusion (hle i), fun _ ↦ rfl⟩
  have hzero : IsZero (W 0) := by
    apply (Rep.isZero_iff (W 0)).mpr
    change Subsingleton (B 0)
    have : B 0 = ⊥ := by simpa [B] using h0
    rw [this]
    infer_instance
  have hend : Nonempty (W n ≅ M) := by
    let f := M.subtype (B n) (hB n)
    have htop : B n = ⊤ := by simpa [B, n] using hn
    have : Mono f := (Rep.mono_iff_injective f).2 Subtype.val_injective
    have : Epi f := (Rep.epi_iff_surjective f).2 (by
      intro x
      exact ⟨⟨x, htop ▸ Submodule.mem_top⟩, rfl⟩)
    let : IsIso f := isIso_of_mono_of_epi f
    exact ⟨asIso f⟩
  refine ⟨W, ι, hzero, hend, ?_⟩
  intro i (hi : i < n)
  have hmono : Mono (ι i) := (Rep.mono_iff_injective (ι i)).2 (by
    intro x y h
    change Submodule.inclusion (hle i) x = Submodule.inclusion (hle i) y at h
    exact Subtype.ext (congrArg (fun z : B (i + 1) ↦ z.val) h))
  refine ⟨hmono, ?_⟩
  let K := (B i).comap (B (i + 1)).subtype
  have hK : ∀ g, K ≤ K.comap ((W (i + 1)).ρ g) := fun g _x hx ↦ hB i g hx
  let Q := (W (i + 1)).quotient K hK
  obtain ⟨eQ⟩ := cokernel_inclusion_iso_quotient M (B i) (B (i + 1))
    (hB i) (hB (i + 1)) (hle i)
  have hrank (j : ℕ) (hj : j ≤ n) : Module.finrank (ZMod ℓ) (B j) = j := by
    cases j with
    | zero => simp [B, h0]
    | succ j =>
      have hj' : j + 1 ≤ n := hj
      change Module.finrank (ZMod ℓ) (F (min (j + 1) n)) = j + 1
      rw [Nat.min_eq_left hj']
      exact (hstep j hj).2.1
  have hdim : Module.finrank (ZMod ℓ) Q.V = 1 := by
    have hsum := K.finrank_quotient_add_finrank
    have hsmall : Module.finrank (ZMod ℓ) K = i :=
      (Submodule.comapSubtypeEquivOfLe (hle i)).finrank_eq.trans (hrank i (by omega))
    have hlarge := hrank (i + 1) hi
    change Module.finrank (ZMod ℓ) Q.V + Module.finrank (ZMod ℓ) K =
      Module.finrank (ZMod ℓ) (B (i + 1)) at hsum
    omega
  have htriv (g : P) (x : Q.V) : Q.ρ g x = x := by
    obtain ⟨x, rfl⟩ := K.mkQ_surjective x
    change K.mkQ ((W (i + 1)).ρ g x) = K.mkQ x
    apply (Submodule.Quotient.eq K).2
    change M.ρ g x.val - x.val ∈ B i
    have hx : x.val ∈ F (i + 1) := by
      simpa [B, Nat.min_eq_left hi] using x.property
    simpa [B, Nat.min_eq_left (Nat.le_of_lt hi)] using (hstep i hi).2.2 g x.val hx
  obtain ⟨e⟩ : Nonempty (Q.V ≃ₗ[ZMod ℓ] ULift.{v} (ZMod ℓ)) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simpa using hdim)
  let e' : Q.ρ.Equiv (Representation.trivial (ZMod ℓ) P (ULift.{v} (ZMod ℓ))) :=
    Representation.Equiv.mk e (fun g ↦ by
      apply LinearMap.ext
      intro x
      change e (Q.ρ g x) = e x
      rw [htriv])
  exact ⟨eQ ≪≫ Rep.mkIso e'⟩

end Rep
