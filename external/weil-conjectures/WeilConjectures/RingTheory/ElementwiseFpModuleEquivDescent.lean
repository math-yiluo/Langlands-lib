/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Order.Directed
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Isomorphism descent from an elementwise ring-colimit criterion

Source: Stacks Project, Algebra, Tag 05N7 (2), (3).
(blueprint: lem-pc-elementwise-fp-module-equiv-descent)
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Lift a map from a finitely presented module through a directed system with the
representative and eventual-zero properties. Lift the finite generators together,
then move to one stage killing the images of the finitely many kernel generators.
Source: Stacks Project, Algebra Tag 05LI (3). -/
private theorem fp_lift
    {R : Type*} [CommRing R] {J : Type*} [Preorder J] [Nonempty J]
    [IsDirected J (· ≤ ·)] (D : J → Type*)
    [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
    (d : ∀ {i j : J}, i ≤ j → D i →ₗ[R] D j)
    (dc : ∀ {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) (x : D i),
      d hjk (d hij x) = d (hij.trans hjk) x)
    {P : Type*} [AddCommGroup P] [Module R P] (μ : ∀ i, D i →ₗ[R] P)
    (hc : ∀ {i j : J} (hij : i ≤ j) (x : D i), μ j (d hij x) = μ i x)
    (hs : ∀ x : P, ∃ i, ∃ y : D i, μ i y = x)
    (hz : ∀ i (x : D i), μ i x = 0 → ∃ j, ∃ hij : i ≤ j, d hij x = 0)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (h : M →ₗ[R] P) : ∃ i, ∃ a : M →ₗ[R] D i, (μ i).comp a = h := by
  classical
  have finite_lift (s : Finset P) : ∃ i, ∀ x ∈ s, ∃ y : D i, μ i y = x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary J, by simp⟩
    | @insert x s hxs ih =>
      obtain ⟨i, y, hy⟩ := hs x
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨d hik y, (hc hik y).trans hy⟩
      · obtain ⟨y, hy⟩ := hj z hz
        exact ⟨d hjk y, (hc hjk y).trans hy⟩
  have finite_zero (i : J) (s : Finset (D i)) (hs : ∀ x ∈ s, μ i x = 0) :
      ∃ j, ∃ hij : i ≤ j, ∀ x ∈ s, d hij x = 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, le_rfl, by simp⟩
    | @insert x s hxs ih =>
      obtain ⟨j, hij, hj⟩ := hz i x (hs x (Finset.mem_insert_self _ _))
      obtain ⟨k, hik, hk⟩ := ih (fun y hy ↦ hs y (Finset.mem_insert_of_mem hy))
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
      refine ⟨l, hij.trans hjl, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [← dc hij hjl, hj, map_zero]
      · have he := dc hik hkl y
        rw [hk y hy, map_zero] at he
        exact he.symm
  -- A finite free cover and a finite generating set for its kernel.
  obtain ⟨σ, ⟨hσ, hτ⟩⟩ := (inferInstance : Module.FinitePresentation R M)
  obtain ⟨τ, hτ⟩ := hτ
  let π := Finsupp.linearCombination R ((↑) : σ → M)
  have hπ : Function.Surjective π :=
    LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, Subtype.range_val, ← hσ])
  obtain ⟨i, hi⟩ := finite_lift (σ.image h)
  have hlift (x : σ) : ∃ y : D i, μ i y = h x :=
    hi (h x) (Finset.mem_image.mpr ⟨x, x.property, rfl⟩)
  choose v hv using hlift
  let a₀ := Finsupp.linearCombination R v
  have ha₀ : (μ i).comp a₀ = h.comp π := by
    ext x
    simpa [a₀, π] using hv x
  have hrel (x : τ) : μ i (a₀ x) = 0 := by
    change ((μ i).comp a₀) x = 0
    rw [ha₀, LinearMap.comp_apply]
    have hx : π x = 0 := by
      rw [← LinearMap.mem_ker, ← hτ]
      exact Submodule.subset_span x.property
    rw [hx, map_zero]
  obtain ⟨j, hij, hj⟩ := finite_zero i (τ.image a₀) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hrel ⟨x, hx⟩)
  let b := (d hij).comp a₀
  have hker : LinearMap.ker π ≤ LinearMap.ker b := by
    rw [← hτ, Submodule.span_le]
    intro x hx
    exact hj (a₀ x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  -- The transported map kills the whole kernel, so descends through the quotient.
  let a := (LinearMap.ker π).liftQ b hker ∘ₗ
    (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
  refine ⟨j, a, ?_⟩
  apply LinearMap.ext
  intro m
  obtain ⟨x, rfl⟩ := hπ m
  change μ j (a (π x)) = h (π x)
  have hax : a (π x) = b x := by simp [a]
  rw [hax]
  exact (hc hij (a₀ x)).trans (LinearMap.congr_fun ha₀ x)


private theorem tensor_elementwise
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (A : J → Type*) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
    (f : ∀ j k, j ≤ k → A j →ₐ[R] A k)
    (hself : ∀ j a, f j j le_rfl a = a)
    (hcomp : ∀ j k l (hjk : j ≤ k) (hkl : k ≤ l) a,
      f k l hkl (f j k hjk a) = f j l (hjk.trans hkl) a)
    (g : ∀ j, A j →ₐ[R] C)
    (hg : ∀ j k (hjk : j ≤ k) a, g k (f j k hjk a) = g j a)
    (hsurj : ∀ c : C, ∃ j a, g j a = c)
    (hzero : ∀ j a, g j a = 0 → ∃ k, ∃ hjk : j ≤ k, f j k hjk a = 0)
    (M : Type*) [AddCommGroup M] [Module R M] :
    (∀ x : C ⊗[R] M, ∃ j, ∃ t : A j ⊗[R] M, (g j).toLinearMap.rTensor M t = x) ∧
    (∀ j (t : A j ⊗[R] M), (g j).toLinearMap.rTensor M t = 0 →
      ∃ k, ∃ hjk : j ≤ k, (f j k hjk).toLinearMap.rTensor M t = 0) := by
  classical
  let d (j k : J) (h : j ≤ k) := (f j k h).toLinearMap
  let μ (j : J) := (g j).toLinearMap
  let : DirectedSystem A (fun {j k} h ↦ d j k h) :=
    { map_self := hself
      map_map := fun {k j i} hij hjk a ↦ hcomp i j k hij hjk a }
  let q : Module.DirectLimit A d →ₗ[R] C :=
    Module.DirectLimit.lift R J A d μ hg
  have qinj : Function.Injective q := by
    intro x y hxy
    obtain ⟨j, a, hx⟩ := Module.DirectLimit.exists_of x
    obtain ⟨k, b, hy⟩ := Module.DirectLimit.exists_of y
    rw [← hx, ← hy] at hxy ⊢
    simp only [q, Module.DirectLimit.lift_of] at hxy
    change g j a = g k b at hxy
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    have hz : g l (f j l hjl a - f k l hkl b) = 0 := by
      rw [map_sub, hg, hg, hxy, sub_self]
    obtain ⟨m, hlm, hm⟩ := hzero l _ hz
    have he : d j m (hjl.trans hlm) a = d k m (hkl.trans hlm) b := by
      simpa only [d, AlgHom.toLinearMap_apply, map_sub, hcomp, sub_eq_zero] using hm
    rw [← Module.DirectLimit.of_f (f := d) (i := j) (j := m)
        (hij := hjl.trans hlm),
      ← Module.DirectLimit.of_f (f := d) (i := k) (j := m) (hij := hkl.trans hlm), he]
  have qsurj : Function.Surjective q := by
    intro c
    obtain ⟨j, a, ha⟩ := hsurj c
    refine ⟨Module.DirectLimit.of R J A d j a, ?_⟩
    simpa only [q, μ, Module.DirectLimit.lift_of, AlgHom.toLinearMap_apply] using ha
  let E := LinearEquiv.ofBijective q ⟨qinj, qsurj⟩
  let dt (j k : J) (h : j ≤ k) := (d j k h).rTensor M
  let e : Module.DirectLimit (fun j ↦ A j ⊗[R] M) dt ≃ₗ[R] C ⊗[R] M :=
    (TensorProduct.directLimitLeft d M).symm.trans (E.rTensor M)
  have e_of (j : J) (t : A j ⊗[R] M) :
      e (Module.DirectLimit.of R J (fun j ↦ A j ⊗[R] M) dt j t) =
        (μ j).rTensor M t := by
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      dsimp only [e, dt]
      rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
        LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]
      change q (Module.DirectLimit.of R J A d j a) ⊗ₜ[R] m = μ j a ⊗ₜ[R] m
      simp only [q, Module.DirectLimit.lift_of]
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
  let : DirectedSystem (fun j ↦ A j ⊗[R] M) (fun {j k} h ↦ dt j k h) :=
    { map_self := by
        intro j t
        induction t using TensorProduct.inductionOn with
        | tmul a m => simp only [dt, LinearMap.rTensor_tmul, DirectedSystem.map_self']
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
      map_map := by
        intro j k l hjk hkl t
        induction t using TensorProduct.inductionOn with
        | tmul a m => simp only [dt, LinearMap.rTensor_tmul, DirectedSystem.map_map']
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu }
  constructor
  · intro x
    obtain ⟨j, t, ht⟩ := Module.DirectLimit.exists_of (e.symm x)
    refine ⟨j, t, ?_⟩
    rw [← e_of, ht, e.apply_symm_apply]
  · intro j t ht
    have hz : Module.DirectLimit.of R J (fun j ↦ A j ⊗[R] M) dt j t = 0 := by
      apply e.injective
      rw [e_of, map_zero]
      exact ht
    obtain ⟨k, hjk, he⟩ := Module.DirectLimit.of.zero_exact hz
    exact ⟨k, hjk, he⟩

private theorem tensor_map_smul
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M]
    (φ : A →ₐ[R] B) (a : A) (t : A ⊗[R] M) :
    φ.toLinearMap.rTensor M (a • t) = φ a • φ.toLinearMap.rTensor M t := by
  induction t using TensorProduct.inductionOn with
  | tmul b m => simp [TensorProduct.smul_tmul', map_mul]
  | add t u ht hu => simp only [smul_add, map_add, ht, hu]

private theorem tensor_lift_naturality
    {R A B M N : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (φ : A →ₐ[R] B) (a : M →ₗ[R] A ⊗[R] N) (t : A ⊗[R] M) :
    φ.toLinearMap.rTensor N (a.liftBaseChange A t) =
      ((φ.toLinearMap.rTensor N).comp a).liftBaseChange B
        (φ.toLinearMap.rTensor M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b m =>
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, LinearMap.comp_apply]
    exact tensor_map_smul φ b (a m)
  | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu

private theorem tensor_lift_limit
    {R A B M N : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (φ : A →ₐ[R] B) (a : M →ₗ[R] A ⊗[R] N)
    (E : B ⊗[R] M →ₗ[B] B ⊗[R] N)
    (ha : ∀ m, φ.toLinearMap.rTensor N (a m) = E (1 ⊗ₜ[R] m))
    (t : A ⊗[R] M) :
    φ.toLinearMap.rTensor N (a.liftBaseChange A t) = E (φ.toLinearMap.rTensor M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b m =>
    rw [LinearMap.liftBaseChange_tmul, tensor_map_smul, ha]
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    rw [show φ b ⊗ₜ[R] m = φ b • (1 ⊗ₜ[R] m) by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
  | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu

private theorem eventually_zero_hom
    {R : Type*} [CommRing R] {J : Type*} [Preorder J] [IsDirectedOrder J]
    (D : J → Type*) [∀ j, AddCommGroup (D j)] [∀ j, Module R (D j)]
    (d : ∀ {j k : J}, j ≤ k → D j →ₗ[R] D k)
    (dc : ∀ {j k l : J} (hjk : j ≤ k) (hkl : k ≤ l) t,
      d hkl (d hjk t) = d (hjk.trans hkl) t)
    {T : Type*} [AddCommGroup T] [Module R T] (μ : ∀ j, D j →ₗ[R] T)
    (hz : ∀ j (t : D j), μ j t = 0 → ∃ k, ∃ hjk : j ≤ k, d hjk t = 0)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (j : J) (a : M →ₗ[R] D j) (ha : ∀ m, μ j (a m) = 0) :
    ∃ k, ∃ hjk : j ≤ k, (d hjk).comp a = 0 := by
  classical
  have finite_zero (s : Finset (D j)) (hs : ∀ t ∈ s, μ j t = 0) :
      ∃ k, ∃ hjk : j ≤ k, ∀ t ∈ s, d hjk t = 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨j, le_rfl, by simp⟩
    | @insert t s hts ih =>
      obtain ⟨k, hjk, hk⟩ := hz j t (hs t (Finset.mem_insert_self _ _))
      obtain ⟨l, hjl, hl⟩ := ih (fun u hu ↦ hs u (Finset.mem_insert_of_mem hu))
      obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k l
      refine ⟨m, hjk.trans hkm, ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [← dc hjk hkm, hk, map_zero]
      · have he := dc hjl hlm u
        rw [hl u hu, map_zero] at he
        exact he.symm
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨k, hjk, hk⟩ := finite_zero (s.image a) (by
    intro t ht
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp ht
    exact ha m)
  refine ⟨k, hjk, ?_⟩
  apply LinearMap.ext_on hs
  intro m hm
  exact hk (a m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

/-- An isomorphism of the limit base changes of two fixed finitely presented
modules descends to one stage of a directed ring system.

Source: Stacks Project, Algebra, Tag 05N7 (2), (3).
(blueprint: lem-pc-elementwise-fp-module-equiv-descent)

Proof:
1. The representative and eventual-zero assumptions identify C as the ring
   colimit. Define the map to any other cocone on a representative g_j(a).
   Move two equal representatives to a common stage and apply eventual zero
   to their difference to prove independence of the representative. Common
   stages also prove the ring-map laws; representatives prove uniqueness.
   For a preorder, take its poset reflection and choose representatives;
   mutually comparable transitions are inverse by identity and composition.
   Lift rings, indices and modules to one common universe using ULift, so
   the categorical map-descent theorem applies, and transport back afterward.
2. Apply Tag 05N7 (2) to the isomorphism and its inverse. Move the two descended
   maps to a common stage. The canonical tensor comparisons satisfy the
   unit-tensor equations, so their extensions are the original maps.
3. The stage modules are finitely presented by base change. Each composite
   becomes the identity over C. Apply Tag 05N7 (3) to each composite and the
   appropriate identity, and take a common upper bound for the resulting
   equalities. Base change preserves composition and identities, so the two
   stage maps are inverse and define a linear equivalence. Transport back
   through the universe lifts and poset representatives. No flatness or
   finite presentation of any ring is needed. The proof also applies to zero
   rings, zero modules, and empty finite presentations.
-/
theorem exists_stage_equiv_of_elementwise_colimit
    {J : Type v} [Preorder J] [IsDirectedOrder J]
    (A : J → Type u) [∀ j, CommRing (A j)]
    (f : ∀ (j l : J), j ≤ l → A j →+* A l)
    (hself : ∀ j, f j j le_rfl = RingHom.id (A j))
    (hcomp : ∀ j l m (hjl : j ≤ l) (hlm : l ≤ m),
      (f l m hlm).comp (f j l hjl) = f j m (hjl.trans hlm))
    (C : Type w) [CommRing C] (g : ∀ j, A j →+* C)
    (hg : ∀ j l (hjl : j ≤ l), (g l).comp (f j l hjl) = g j)
    (hsurj : ∀ c : C, ∃ j a, g j a = c)
    (hzero : ∀ j a, g j a = 0 → ∃ (l : J) (hjl : j ≤ l), f j l hjl a = 0)
    (i : J) (P : Type x) (N : Type y) [AddCommMonoid P] [AddCommMonoid N]
    [Module (A i) P] [Module (A i) N]
    [Module.FinitePresentation (A i) P] [Module.FinitePresentation (A i) N]
    (e : letI : Algebra (A i) C := (g i).toAlgebra
      Nonempty (C ⊗[A i] P ≃ₗ[C] C ⊗[A i] N)) :
    ∃ (j : J) (hij : i ≤ j),
      letI : Algebra (A i) (A j) := (f i j hij).toAlgebra
      Nonempty (A j ⊗[A i] P ≃ₗ[A j] A j ⊗[A i] N) := by
  classical
  let R := A i
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  let : Algebra R C := (g i).toAlgebra
  obtain ⟨e⟩ := e
  let K := Set.Ici i
  let : Nonempty K := ⟨⟨i, le_rfl⟩⟩
  let : IsDirectedOrder K := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let B (j : K) := A j.val
  let : ∀ j, CommRing (B j) := fun j ↦ inferInstance
  let : ∀ j, Algebra R (B j) := fun j ↦ (f i j.val j.property).toAlgebra
  let t (j k : K) (hjk : j ≤ k) : B j →ₐ[R] B k :=
    { f j.val k.val hjk with
      commutes' := fun r ↦ congrArg (fun q : A i →+* A k.val ↦ q r)
        (hcomp i j.val k.val j.property hjk) }
  let q (j : K) : B j →ₐ[R] C :=
    { g j.val with
      commutes' := fun r ↦ congrArg (fun q : A i →+* C ↦ q r)
        (hg i j.val j.property) }
  have ts (j : K) (a : B j) : t j j le_rfl a = a := by
    exact congrArg (fun q : A j.val →+* A j.val ↦ q a) (hself j.val)
  have tc (j k l : K) (hjk : j ≤ k) (hkl : k ≤ l) (a : B j) :
      t k l hkl (t j k hjk a) = t j l (hjk.trans hkl) a :=
    congrArg (fun q : A j.val →+* A l.val ↦ q a)
      (hcomp j.val k.val l.val hjk hkl)
  have qc (j k : K) (hjk : j ≤ k) (a : B j) : q k (t j k hjk a) = q j a :=
    congrArg (fun q : A j.val →+* C ↦ q a) (hg j.val k.val hjk)
  have qs (c : C) : ∃ j : K, ∃ a : B j, q j a = c := by
    obtain ⟨j, a, ha⟩ := hsurj c
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨⟨k, hik⟩, f j k hjk a, ?_⟩
    exact (congrArg (fun q : A j →+* C ↦ q a) (hg j k hjk)).trans ha
  have qz (j : K) (a : B j) (ha : q j a = 0) :
      ∃ k : K, ∃ hjk : j ≤ k, t j k hjk a = 0 := by
    obtain ⟨k, hjk, hk⟩ := hzero j.val a ha
    exact ⟨⟨k, j.property.trans hjk⟩, hjk, hk⟩
  let DP (j : K) := B j ⊗[R] P
  let dP {j k : K} (hjk : j ≤ k) : DP j →ₗ[R] DP k :=
    (t j k hjk).toLinearMap.rTensor P
  let μP (j : K) : DP j →ₗ[R] C ⊗[R] P := (q j).toLinearMap.rTensor P
  have dcP {j k l : K} (hjk : j ≤ k) (hkl : k ≤ l) (x : DP j) :
      dP hkl (dP hjk x) = dP (hjk.trans hkl) x := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => exact congrArg (fun a ↦ a ⊗ₜ[R] m) (tc j k l hjk hkl a)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have μcP {j k : K} (hjk : j ≤ k) (x : DP j) : μP k (dP hjk x) = μP j x := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => exact congrArg (fun a ↦ a ⊗ₜ[R] m) (qc j k hjk a)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have criterionP := tensor_elementwise B t ts tc q qc qs qz P
  let DN (j : K) := B j ⊗[R] N
  let dN {j k : K} (hjk : j ≤ k) : DN j →ₗ[R] DN k :=
    (t j k hjk).toLinearMap.rTensor N
  let μN (j : K) : DN j →ₗ[R] C ⊗[R] N := (q j).toLinearMap.rTensor N
  have dcN {j k l : K} (hjk : j ≤ k) (hkl : k ≤ l) (x : DN j) :
      dN hkl (dN hjk x) = dN (hjk.trans hkl) x := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => exact congrArg (fun a ↦ a ⊗ₜ[R] m) (tc j k l hjk hkl a)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have μcN {j k : K} (hjk : j ≤ k) (x : DN j) : μN k (dN hjk x) = μN j x := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => exact congrArg (fun a ↦ a ⊗ₜ[R] m) (qc j k hjk a)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have criterionN := tensor_elementwise B t ts tc q qc qs qz N
  -- Lift the equivalence and its inverse on the original modules.
  let ep : P →ₗ[R] C ⊗[R] N :=
    (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R C P 1)
  let en : N →ₗ[R] C ⊗[R] P :=
    (e.symm.toLinearMap.restrictScalars R).comp (TensorProduct.mk R C N 1)
  obtain ⟨j, a, ha⟩ := fp_lift DN dN dcN μN μcN
    criterionN.1 criterionN.2 P ep
  obtain ⟨k, b, hb⟩ := fp_lift DP dP dcP μP μcP
    criterionP.1 criterionP.2 N en
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  let a' := (dN hjl).comp a
  let b' := (dP hkl).comp b
  have ha' (p : P) : μN l (a' p) = e (1 ⊗ₜ[R] p) :=
    (μcN hjl (a p)).trans (LinearMap.congr_fun ha p)
  have hb' (n : N) : μP l (b' n) = e.symm (1 ⊗ₜ[R] n) :=
    (μcP hkl (b n)).trans (LinearMap.congr_fun hb n)
  let U := a'.liftBaseChange (B l)
  let V := b'.liftBaseChange (B l)
  -- Kill both composite errors on finite generating sets before forming the equivalence.
  let errP : P →ₗ[R] DP l :=
    (V.restrictScalars R).comp a' - TensorProduct.mk R (B l) P 1
  let errN : N →ₗ[R] DN l :=
    (U.restrictScalars R).comp b' - TensorProduct.mk R (B l) N 1
  have errPzero (p : P) : μP l (errP p) = 0 := by
    change μP l (V (a' p) - 1 ⊗ₜ[R] p) = 0
    rw [map_sub, tensor_lift_limit (q l) b' e.symm.toLinearMap hb', ha']
    change e.symm (e (1 ⊗ₜ[R] p)) - (q l 1 ⊗ₜ[R] p) = 0
    rw [e.symm_apply_apply, map_one, sub_self]
  have errNzero (n : N) : μN l (errN n) = 0 := by
    change μN l (U (b' n) - 1 ⊗ₜ[R] n) = 0
    rw [map_sub, tensor_lift_limit (q l) a' e.toLinearMap ha', hb']
    change e (e.symm (1 ⊗ₜ[R] n)) - (q l 1 ⊗ₜ[R] n) = 0
    rw [e.apply_symm_apply, map_one, sub_self]
  obtain ⟨lp, hlp, hp⟩ := eventually_zero_hom DP dP dcP μP
    criterionP.2 l errP errPzero
  obtain ⟨ln, hln, hn⟩ := eventually_zero_hom DN dN dcN μN
    criterionN.2 l errN errNzero
  obtain ⟨m, hpm, hnm⟩ := exists_ge_ge lp ln
  have hlm : l ≤ m := hlp.trans hpm
  let am := (dN hlm).comp a'
  let bm := (dP hlm).comp b'
  let Um := am.liftBaseChange (B m)
  let Vm := bm.liftBaseChange (B m)
  have hp' (p : P) : dP hlm (errP p) = 0 := by
    rw [← dcP hlp hpm]
    have h := LinearMap.congr_fun hp p
    change dP hlp (errP p) = 0 at h
    rw [h, map_zero]
  have hn' (n : N) : dN hlm (errN n) = 0 := by
    have hlm' : hlm = hln.trans hnm := Subsingleton.elim _ _
    rw [hlm', ← dcN hln hnm]
    have h := LinearMap.congr_fun hn n
    change dN hln (errN n) = 0 at h
    rw [h, map_zero]
  have huv : Vm.comp Um = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r p
    have h := hp' p
    change dP hlm (V (a' p) - 1 ⊗ₜ[R] p) = 0 at h
    rw [map_sub, tensor_lift_naturality (t l m hlm) b'] at h
    have h' : Vm (am p) = 1 ⊗ₜ[R] p := by
      change Vm (am p) - (t l m hlm 1 ⊗ₜ[R] p) = 0 at h
      rw [map_one] at h
      exact sub_eq_zero.mp h
    change Vm (Um (r ⊗ₜ[R] p)) = r ⊗ₜ[R] p
    rw [LinearMap.liftBaseChange_tmul, map_smul, h']
    change (r * 1) ⊗ₜ[R] p = r ⊗ₜ[R] p
    rw [mul_one]
  have hvu : Um.comp Vm = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r n
    have h := hn' n
    change dN hlm (U (b' n) - 1 ⊗ₜ[R] n) = 0 at h
    rw [map_sub, tensor_lift_naturality (t l m hlm) a'] at h
    have h' : Um (bm n) = 1 ⊗ₜ[R] n := by
      change Um (bm n) - (t l m hlm 1 ⊗ₜ[R] n) = 0 at h
      rw [map_one] at h
      exact sub_eq_zero.mp h
    change Um (Vm (r ⊗ₜ[R] n)) = r ⊗ₜ[R] n
    rw [LinearMap.liftBaseChange_tmul, map_smul, h']
    change (r * 1) ⊗ₜ[R] n = r ⊗ₜ[R] n
    rw [mul_one]
  exact ⟨m.val, m.property, ⟨LinearEquiv.ofLinearMap Um Vm hvu huv⟩⟩

end AlgebraicGeometry
