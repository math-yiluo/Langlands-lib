/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Scalar quasi-inverses and reduction modulo an ideal

Source: Stacks Project, Cohomology of Schemes, Remark 0888, the commutative algebra
argument and its limit argument
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v v' w w' z z'

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace LinearMap

/-- Source: Stacks Project, Remark 0888, the exact-sequence hypothesis
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

The kernel/cokernel formulation is equivalent to the exact-sequence formulation.
Proof: the inclusion of the kernel, `u`, and the projection to `N / range u` give the
canonical exact sequence (def-weil-pbc-exact-sequence). Conversely, exactness identifies
`T` with `ker u` and `Q` with `N / range u` by linear isomorphisms, which preserve
annihilation by every scalar. Thus the two annihilator conditions are equivalent. -/
theorem ker_coker_annihilated_iff_exists_exact_sequence
    {A : Type u} [CommRing A]
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K : Ideal A) (t : ℕ) (u : M →ₗ[A] N) :
    (K ^ t ≤ Module.annihilator A (ker u) ∧
      K ^ t ≤ Module.annihilator A (N ⧸ range u)) ↔
    ∃ (T Q : ModuleCat.{v} A) (i : T ⟶ ModuleCat.of A M)
      (p : ModuleCat.of A N ⟶ Q),
      (ComposableArrows.mk₅ (0 : (0 : ModuleCat.{v} A) ⟶ T) i
        (ModuleCat.ofHom u) p (0 : Q ⟶ (0 : ModuleCat.{v} A))).Exact ∧
      K ^ t ≤ Module.annihilator A T ∧ K ^ t ≤ Module.annihilator A Q := by
  constructor
  · rintro ⟨hker, hcoker⟩
    refine ⟨ModuleCat.of A (ker u), ModuleCat.of A (N ⧸ range u),
      ModuleCat.ofHom (ker u).subtype, ModuleCat.ofHom (range u).mkQ, ?_, hker, hcoker⟩
    refine ⟨⟨?zero⟩, ?exact⟩
    case zero =>
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simp
      · exact ModuleCat.hom_ext (comp_ker_subtype u)
      · exact ModuleCat.hom_ext (range_mkQ_comp u)
      · change ModuleCat.ofHom (range u).mkQ ≫ (0 : _ ⟶ _) = 0
        simp
    case exact =>
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x hx
        refine ⟨0, ?_⟩
        change 0 = x
        apply Subtype.ext
        exact hx.symm
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x hx
        exact (Submodule.Quotient.mk_eq_zero _).mp hx
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x _
        exact (range u).mkQ_surjective x
  · rintro ⟨T, Q, i, p, hex, hT, hQ⟩
    have atM := (ShortComplex.moduleCat_exact_iff _).mp (hex.exact 1)
    have atN := (ShortComplex.moduleCat_exact_iff _).mp (hex.exact 2)
    change ∀ x : M, u x = 0 → ∃ y : T, i y = x at atM
    change ∀ y : N, p y = 0 → ∃ x : M, u x = y at atN
    constructor
    · intro f hf
      apply Module.mem_annihilator.mpr
      intro x
      obtain ⟨y, hy⟩ := atM (x : M) (LinearMap.mem_ker.mp x.property)
      apply Subtype.ext
      change f • (x : M) = 0
      rw [← hy, ← i.hom.map_smul, Module.mem_annihilator.mp (hT hf) y, map_zero]
    · intro f hf
      apply Module.mem_annihilator.mpr
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ y =>
        change (range u).mkQ (f • y) = 0
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        apply LinearMap.mem_range.mpr
        apply atN
        rw [p.hom.map_smul, Module.mem_annihilator.mp (hQ hf) (p y)]


/-- Source: Stacks Project, Remark 0888, the final scalar-composite argument
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Each product `f * g` kills the kernel by the first composite and kills the quotient
by the range by the second composite. Since `K^(2*t) = K^t * K^t`, ideal multiplication
extends the annihilation of products to the whole ideal. This is clause (d), isolated
as a proved private helper so that it can also be used for the reduced map in (c). -/
private theorem annihilated_of_scalar_composites
    {A : Type u} [CommRing A] (K : Ideal A) (t : ℕ)
    {P : Type z} {R : Type z'} [AddCommGroup P] [Module A P]
    [AddCommGroup R] [Module A R] (v : P →ₗ[A] R)
    (hv : ∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      ∃ k : R →ₗ[A] P,
        k.comp v = (f * g) • LinearMap.id ∧ v.comp k = (f * g) • LinearMap.id) :
    K ^ (2 * t) ≤ Module.annihilator A (ker v) ∧
    K ^ (2 * t) ≤ Module.annihilator A (R ⧸ range v) := by
  rw [two_mul, pow_add]
  constructor
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, hk, _⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    have h := congrArg (fun l : P →ₗ[A] P ↦ l x) hk
    simpa [LinearMap.mem_ker.mp x.property] using h.symm
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, _, hk⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change (range v).mkQ ((f * g) • y) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨k y, ?_⟩
      exact congrArg (fun l : R →ₗ[A] R ↦ l y) hk

/-- Source: Stacks Project, Remark 0888, the maps "fg", reduction modulo `J`, and
compatibility and annihilation used in the limit argument
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof, following the eight elementary steps of the node:
1. The exact-sequence convention is given by def-weil-pbc-exact-sequence, and its
   equivalence with the hypothesis is the preceding statement.
2. Since `f` kills the class of `y` in the cokernel, `f • y` lies in the range of `u`.
3. Two lifts differ by an element of `ker u`, killed by `g`, so `g • x` is independent
   of the lift.
4. Sums and scalar multiples of lifts lift the corresponding sums and scalar multiples;
   independence therefore makes the resulting map `h` linear.
5. Choose `f • m` as the lift of `u m` to obtain `h.comp u = (f*g) • id`.
   Applying `u` to `g • x` gives the other composite.
6. In a commuting square, `a x` lifts `f • b y`; the lifting formula for `h'` then
   gives `a.comp h = h'.comp b`.
7. For any map `v` admitting the stated two scalar composites, each `f*g` kills its
   kernel and its cokernel. Finite sums of these products generate `K^(2*t)`, so that
   ideal kills both modules.
8. Linearity makes `u` and `h` preserve the submodules `J • ⊤`. Their induced maps
   on the quotients retain both scalar composites; step 7 proves clause (c).
The cokernel is the quotient by the range; the reduced map `M/JM → N/JN` is the
induced map `Submodule.mapQ` on the quotients by `J • ⊤`. Naturality is quantified
over every map with the lifting formula, hence over the canonical map of clause (a),
without choosing new definitions. -/
theorem ker_coker_annihilated_mod_ideal
    {A : Type u} [CommRing A]
    {M : Type v} {N : Type v'}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K : Ideal A) (t : ℕ) (ht : 1 ≤ t) (u : M →ₗ[A] N)
    (hker : K ^ t ≤ Module.annihilator A (ker u))
    (hcoker : K ^ t ≤ Module.annihilator A (N ⧸ range u)) :
    (∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      (∀ y : N, ∃ x : M, u x = f • y) ∧
      (∀ (y : N) (x x' : M), u x = f • y → u x' = f • y → g • x = g • x') ∧
      ∃ h : N →ₗ[A] M,
        (∀ (y : N) (x : M), u x = f • y → h y = g • x) ∧
        h.comp u = (f * g) • LinearMap.id ∧
        u.comp h = (f * g) • LinearMap.id ∧
        ∀ (M' : Type w) (N' : Type w') [AddCommGroup M'] [Module A M']
          [AddCommGroup N'] [Module A N'] (u' : M' →ₗ[A] N'),
          K ^ t ≤ Module.annihilator A (ker u') →
          K ^ t ≤ Module.annihilator A (N' ⧸ range u') →
          ∀ (a : M →ₗ[A] M') (b : N →ₗ[A] N') (h' : N' →ₗ[A] M'),
            u'.comp a = b.comp u →
            (∀ (y : N') (x : M'), u' x = f • y → h' y = g • x) →
            a.comp h = h'.comp b) ∧
    (∀ J : Ideal A,
      let ū := (J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
        (Submodule.smul_top_le_comap_smul_top J u)
      K ^ (2 * t) ≤ Module.annihilator A (ker ū) ∧
      K ^ (2 * t) ≤ Module.annihilator A ((N ⧸ (J • ⊤ : Submodule A N)) ⧸ range ū)) ∧
    (∀ (P : Type z) (R : Type z') [AddCommGroup P] [Module A P] [AddCommGroup R] [Module A R]
      (v : P →ₗ[A] R),
      (∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
        ∃ k : R →ₗ[A] P,
          k.comp v = (f * g) • LinearMap.id ∧ v.comp k = (f * g) • LinearMap.id) →
      K ^ (2 * t) ≤ Module.annihilator A (ker v) ∧
      K ^ (2 * t) ≤ Module.annihilator A (R ⧸ range v)) := by
  classical
  -- The scalar argument also works for t = 0; retain the stated hypothesis.
  have _ht := ht
  have maps : ∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      (∀ y : N, ∃ x : M, u x = f • y) ∧
      (∀ (y : N) (x x' : M), u x = f • y → u x' = f • y → g • x = g • x') ∧
      ∃ h : N →ₗ[A] M,
        (∀ (y : N) (x : M), u x = f • y → h y = g • x) ∧
        h.comp u = (f * g) • LinearMap.id ∧
        u.comp h = (f * g) • LinearMap.id ∧
        ∀ (M' : Type w) (N' : Type w') [AddCommGroup M'] [Module A M']
          [AddCommGroup N'] [Module A N'] (u' : M' →ₗ[A] N'),
          K ^ t ≤ Module.annihilator A (ker u') →
          K ^ t ≤ Module.annihilator A (N' ⧸ range u') →
          ∀ (a : M →ₗ[A] M') (b : N →ₗ[A] N') (h' : N' →ₗ[A] M'),
            u'.comp a = b.comp u →
            (∀ (y : N') (x : M'), u' x = f • y → h' y = g • x) →
            a.comp h = h'.comp b := by
    intro f g hf hg
    have lifts (y : N) : ∃ x : M, u x = f • y := by
      apply LinearMap.mem_range.mp
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact Module.mem_annihilator.mp (hcoker hf) ((range u).mkQ y)
    have independent (y : N) (x x' : M)
        (hx : u x = f • y) (hx' : u x' = f • y) : g • x = g • x' := by
      have hxker : x - x' ∈ ker u := by simp [LinearMap.mem_ker, hx, hx']
      have hz := Module.mem_annihilator.mp (hker hg) (⟨x - x', hxker⟩ : ker u)
      have hz' : g • (x - x') = 0 := congrArg Subtype.val hz
      exact sub_eq_zero.mp (by simpa [smul_sub] using hz')
    let lift (y : N) : M := Classical.choose (lifts y)
    have hlift (y : N) : u (lift y) = f • y := Classical.choose_spec (lifts y)
    have formula (y : N) (x : M) (hx : u x = f • y) :
        g • lift y = g • x := independent y (lift y) x (hlift y) hx
    let h : N →ₗ[A] M :=
      { toFun := fun y ↦ g • lift y
        map_add' := fun y y' ↦ by
          rw [formula (y + y') (lift y + lift y') (by simp [hlift, smul_add])]
          exact smul_add g (lift y) (lift y')
        map_smul' := fun c y ↦ by
          rw [formula (c • y) (c • lift y) (by simp [hlift, smul_comm f c])]
          exact smul_comm g c (lift y) }
    refine ⟨lifts, independent, h, formula, ?_, ?_, ?_⟩
    · ext x
      change g • lift (u x) = (f * g) • x
      rw [formula (u x) (f • x) (u.map_smul f x), smul_smul, mul_comm g f]
    · ext y
      change u (g • lift y) = (f * g) • y
      rw [u.map_smul, hlift, smul_smul, mul_comm g f]
    · intro M' N' _ _ _ _ u' _ _ a b h' square formula'
      ext y
      obtain ⟨x, hx⟩ := lifts y
      change a (g • lift y) = h' (b y)
      rw [formula y x hx, a.map_smul]
      symm
      apply formula'
      have hs := congrArg (fun l : M →ₗ[A] N' ↦ l x) square
      simpa [hx] using hs
  refine ⟨maps, ?_, fun P R _ _ _ _ v hv ↦ annihilated_of_scalar_composites K t v hv⟩
  intro J
  apply annihilated_of_scalar_composites K t
  intro f g hf hg
  obtain ⟨h, _, hhu, huh, _⟩ := (maps f g hf hg).2.2
  let hbar := (J • ⊤ : Submodule A N).mapQ (J • ⊤ : Submodule A M) h
    (Submodule.smul_top_le_comap_smul_top J h)
  refine ⟨hbar, ?_, ?_⟩
  · ext x
    change (J • ⊤ : Submodule A M).mkQ (h (u x)) =
      (J • ⊤ : Submodule A M).mkQ ((f * g) • x)
    exact congrArg (fun y ↦ (J • ⊤ : Submodule A M).mkQ y)
      (congrArg (fun l : M →ₗ[A] M ↦ l x) hhu)
  · ext y
    change (J • ⊤ : Submodule A N).mkQ (u (h y)) =
      (J • ⊤ : Submodule A N).mkQ ((f * g) • y)
    exact congrArg (fun x ↦ (J • ⊤ : Submodule A N).mkQ x)
      (congrArg (fun l : N →ₗ[A] N ↦ l y) huh)

end LinearMap
