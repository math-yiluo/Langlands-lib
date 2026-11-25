/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TateResidue.TateIdeals
public import WeilConjectures.RingTheory.Kaehler.Trace
public import Mathlib.Tactic.NoncommRing

/-!
# Tate's abstract residue

Let `k` be a field, `K` a commutative `k`-algebra acting on a `k`-vector space `V`, and `A ⊆ V`
a `k`-subspace which is *admissible*: `f A ≺ A` for every `f ∈ K` (that is, `f A ⊆ A + W` with
`W` finite-dimensional). Following Tate (*Residues of differentials on curves*, Theorem 1),
for `f, g ∈ K` choose *lifts* `φ, ψ` of the multiplications by `f, g` in the sense that
`φ ∈ E₁`, `φ - f ∈ E₂` (e.g. `φ = π ∘ f` for a projection `π : V → A`). Then `[φ, ψ] ∈ E₀` and
`Tr_V [φ, ψ]` only depends on `f` and `g`; it is `k`-bilinear, alternating and satisfies
`res(fg, h) = res(f, gh) + res(g, hf)`, so that `f dg ↦ Tr_V [φ, ψ]` is a well-defined
`k`-linear map `res_{V,A} : Ω[K⁄k] → k`.

## Main definitions

- `TateResidue.Admissible K A`: `f A ≺ A` for every `f ∈ K`.
- `TateResidue.IsLift A f φ`: `φ ∈ E₁` and `φ - f ∈ E₂`.
- `TateResidue.resPair K A f g`: `Tr_V [π f, π g]` for a chosen projection `π` onto `A`.
- `TateResidue.res K A : Ω[K⁄k] →ₗ[k] k`: Tate's residue (`0` if `A` is not admissible).

## Main results

- `TateResidue.res_smul_D`: `res K A (f • D g) = Tr_V [φ, ψ]` for any lifts `φ, ψ` of `f, g`.
- `TateResidue.res_eq_of_almostLE`: `res` only depends on the commensurability class of `A` (R1).
- `TateResidue.res_eq_zero_of_fg`, `TateResidue.res_eq_zero_of_top_almostLE`: `res = 0` if
  `A ~ 0` or `A ~ V` (R1).
- `TateResidue.res_smul_D_eq_zero`: `res (f • D g) = 0` if `f A ⊆ A` and `g A ⊆ A` (R2).
-/

@[expose] public section

open LinearMap Submodule Module.End KaehlerDifferential

namespace KaehlerDifferential

variable {k K : Type*} [CommRing k] [CommRing K] [Algebra k K]

/-- `Ω[K⁄k]` is spanned over `k` by the elements `f • D g`. -/
lemma span_range_smul_D :
    span k (Set.range fun p : K × K ↦ p.1 • D k K p.2) = ⊤ := by
  set S := span k (Set.range fun p : K × K ↦ p.1 • D k K p.2)
  have hsmul : ∀ (a : K), ∀ ω ∈ S, a • ω ∈ S := by
    intro a ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨f, g⟩, rfl⟩ := hx
      exact subset_span ⟨(a * f, g), by simp [mul_smul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact S.smul_mem c hx
  suffices ∀ ω, ω ∈ S from eq_top_iff.2 fun ω _ ↦ this ω
  intro ω
  have : ω ∈ span K (Set.range (D k K)) := by rw [span_range_derivation]; trivial
  induction this using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact subset_span ⟨(1, g), one_smul _ _⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact hsmul a x hx

/-- Two `k`-linear maps out of `Ω[K⁄k]` agreeing on all `f • D g` are equal. -/
lemma linearMap_ext_smul_D {M : Type*} [AddCommGroup M] [Module k M]
    {l l' : Ω[K⁄k] →ₗ[k] M} (h : ∀ f g : K, l (f • D k K g) = l' (f • D k K g)) : l = l' := by
  refine LinearMap.ext_on_range (span_range_smul_D (k := k) (K := K)) ?_
  rintro ⟨f, g⟩
  exact h f g

end KaehlerDifferential

namespace TateResidue

section Projection

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- There is a projection `π` of `V` onto `A` mapping a given subspace `N` into itself. -/
lemma exists_proj (A N : Submodule k V) :
    ∃ π : Module.End k V, (∀ v, π v ∈ A) ∧ (∀ a ∈ A, π a = a) ∧ ∀ n ∈ N, π n ∈ N := by
  obtain ⟨ρ, hρ⟩ := (inclusion (inf_le_right : A ⊓ N ≤ N)).exists_leftInverse_of_injective
    (ker_eq_bot.2 (inclusion_injective _))
  let f₁ : V →ₗ.[k] A := ⟨A, LinearMap.id⟩
  let f₂ : V →ₗ.[k] A := ⟨N, inclusion inf_le_left ∘ₗ ρ⟩
  have hρ' : ∀ (y : N) (hy : (y : V) ∈ A ⊓ N), ρ y = ⟨y, hy⟩ := fun y hy ↦ by
    have := congr($hρ ⟨y, hy⟩)
    simp only [comp_apply, id_apply] at this
    rw [← this]
    rfl
  have H : ∀ (x : f₁.domain) (y : f₂.domain), (x : V) = y → f₁ x = f₂ y := by
    intro x y hxy
    have hy : (y : V) ∈ A ⊓ N := ⟨hxy ▸ x.2, y.2⟩
    change x = inclusion inf_le_left (ρ y)
    rw [hρ' y hy]
    exact Subtype.ext hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (f₁.sup f₂ H).toFun
  have hg' : ∀ (z : V) (hz : z ∈ A ⊔ N), g z = (f₁.sup f₂ H) ⟨z, hz⟩ := fun z hz ↦
    congr($hg ⟨z, hz⟩)
  refine ⟨A.subtype ∘ₗ g, fun v ↦ (g v).2, fun a ha ↦ ?_, fun n hn ↦ ?_⟩
  · rw [comp_apply, hg' a (mem_sup_left ha),
      LinearPMap.sup_apply H (⟨a, ha⟩ : f₁.domain) (0 : f₂.domain) _ (by simp)]
    simp [f₁]
  · rw [comp_apply, hg' n (mem_sup_right hn),
      LinearPMap.sup_apply H (0 : f₁.domain) (⟨n, hn⟩ : f₂.domain) _ (by simp)]
    simpa [f₁, f₂] using (Submodule.mem_inf.1 (ρ ⟨n, hn⟩).2).2

/-- A chosen projection of `V` onto `A`. -/
noncomputable def proj (A : Submodule k V) : Module.End k V := (exists_proj A ⊥).choose

lemma proj_mem (A : Submodule k V) (v : V) : proj A v ∈ A := (exists_proj A ⊥).choose_spec.1 v

lemma proj_apply_of_mem {A : Submodule k V} {a : V} (ha : a ∈ A) : proj A a = a :=
  (exists_proj A ⊥).choose_spec.2.1 a ha

end Projection

section Action

variable (k : Type*) {K V : Type*} [Field k] [CommRing K] [Algebra k K] [AddCommGroup V]
  [Module k V] [Module K V] [IsScalarTower k K V]

/-- Multiplication by `f ∈ K` as a `k`-linear endomorphism of `V`. -/
noncomputable def act (f : K) : Module.End k V := DistribSMul.toLinearMap k V f

variable {k}

@[simp] lemma act_apply (f : K) (v : V) : act k f v = f • v := rfl

lemma act_mul (f g : K) : act k (V := V) (f * g) = act k f * act k g :=
  LinearMap.ext fun v ↦ mul_smul f g v

lemma act_add (f g : K) : act k (V := V) (f + g) = act k f + act k g :=
  LinearMap.ext fun v ↦ add_smul f g v

lemma act_smul (c : k) (f : K) : act k (V := V) (c • f) = c • act k f :=
  LinearMap.ext fun v ↦ smul_assoc c f v

lemma act_comm (f g : K) : act k (V := V) f * act k g = act k g * act k f := by
  rw [← act_mul, mul_comm, act_mul]

end Action

variable {k : Type*} (K : Type*) {V : Type*} [Field k] [CommRing K] [Algebra k K]
  [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]

/-- A `k`-subspace `A ⊆ V` is *admissible* for the action of `K` if `f A ≺ A` for all `f ∈ K`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
def Admissible (A : Submodule k V) : Prop := ∀ f : K, E A (act k (V := V) f)

variable {K}

/-- `φ` *lifts* the multiplication by `f` with respect to `A`: `φ ∈ E₁` and `φ - f ∈ E₂`. -/
def IsLift (A : Submodule k V) (f : K) (φ : Module.End k V) : Prop :=
  E₁ A φ ∧ E₂ A (φ - act k f)

variable {A : Submodule k V} {f g h : K} {φ ψ χ φ' ψ' : Module.End k V}

lemma IsLift.toE (hA : Admissible K A) (hφ : IsLift A f φ) : E A φ := by
  simpa using hφ.2.toE.add (hA f)

lemma isLift_proj_mul (hA : Admissible K A) {π : Module.End k V} (hπ : ∀ v, π v ∈ A)
    (hπA : ∀ a ∈ A, π a = a) (f : K) : IsLift A f (π * act k f) := by
  refine ⟨(E₁.of_le ?_).mul_right _, ?_⟩
  · rintro _ ⟨v, rfl⟩; exact hπ v
  · have h1 : E₂ A (π - 1) := by
      refine (fg_bot (R := k) (M := V)).of_le ?_
      rintro _ ⟨a, ha, rfl⟩
      simp [hπA a ha]
    rw [show π * act k f - act k f = (π - 1) * act k f by rw [sub_mul, one_mul]]
    exact h1.mul_right (hA f)

lemma isLift_mul_proj {π : Module.End k V} (hπ : ∀ v, π v ∈ A) (hπA : ∀ a ∈ A, π a = a)
    (hf : ∀ a ∈ A, f • a ∈ A) : IsLift A f (act k f * π) := by
  refine ⟨E₁.of_le ?_, (fg_bot (R := k) (M := V)).of_le ?_⟩
  · rintro _ ⟨v, rfl⟩; exact hf _ (hπ v)
  · rintro _ ⟨a, ha, rfl⟩
    simp [hπA a ha]

lemma isLift_lift (hA : Admissible K A) (f : K) : IsLift A f (proj A * act k f) :=
  isLift_proj_mul hA (proj_mem A) (fun _ ↦ proj_apply_of_mem) f

lemma IsLift.add (hφ : IsLift A f φ) (hψ : IsLift A g ψ) : IsLift A (f + g) (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, ?_⟩
  rw [act_add, show φ + ψ - (act k f + act k g) = (φ - act k f) + (ψ - act k g) by abel]
  exact hφ.2.add hψ.2

lemma IsLift.smul (c : k) (hφ : IsLift A f φ) : IsLift A (c • f) (c • φ) := by
  refine ⟨hφ.1.smul c, ?_⟩
  rw [act_smul, ← smul_sub]
  exact hφ.2.smul c

lemma IsLift.mul (hA : Admissible K A) (hφ : IsLift A f φ) (hψ : IsLift A g ψ) :
    IsLift A (f * g) (φ * ψ) := by
  refine ⟨hφ.1.mul_right ψ, ?_⟩
  rw [act_mul, show φ * ψ - act k f * act k g =
    (φ - act k f) * ψ + act k f * (ψ - act k g) by noncomm_ring]
  exact (hφ.2.mul_right (hψ.toE hA)).add (hψ.2.mul_left _)

lemma IsLift.commutator_mem (hA : Admissible K A) (hφ : IsLift A f φ) (hψ : IsLift A g ψ) :
    E₁ A (φ * ψ - ψ * φ) ∧ E₂ A (φ * ψ - ψ * φ) := by
  refine ⟨(hφ.1.mul_right ψ).sub (hψ.1.mul_right φ), ?_⟩
  set a := φ - act k f
  set b := ψ - act k g
  have hcomm := act_comm (k := k) (V := V) f g
  have : φ * ψ - ψ * φ = act k f * b + a * act k g + a * b - act k g * a - b * act k f - b * a
      + (act k f * act k g - act k g * act k f) := by
    simp only [a, b]; noncomm_ring
  rw [this, hcomm, sub_self, add_zero]
  exact ((((hψ.2.mul_left _).add (hφ.2.mul_right (hA g))).add (hψ.2.mul_left _)).sub
    (hφ.2.mul_left _)).sub (hψ.2.mul_right (hA f)) |>.sub (hφ.2.mul_left _)

/-- **Tate's Theorem 1 (independence)**: `Tr [φ, ψ]` does not depend on the lifts `φ, ψ`. -/
theorem tateTrace_commutator_eq (hA : Admissible K A) (hφ : IsLift A f φ) (hφ' : IsLift A f φ')
    (hψ : IsLift A g ψ) (hψ' : IsLift A g ψ') :
    (φ * ψ - ψ * φ).tateTrace = (φ' * ψ' - ψ' * φ').tateTrace := by
  -- change the first lift
  have step₁ : ∀ {φ φ' ψ : Module.End k V} {f g : K}, IsLift A f φ → IsLift A f φ' →
      IsLift A g ψ → (φ' * ψ - ψ * φ').tateTrace = (φ * ψ - ψ * φ).tateTrace := by
    intro φ φ' ψ f g hφ hφ' hψ
    set e := φ' - φ
    have he₁ : E₁ A e := hφ'.1.sub hφ.1
    have he₂ : E₂ A e := by
      simpa [e] using hφ'.2.sub hφ.2
    have hc := hφ.commutator_mem hA hψ
    rw [show φ' * ψ - ψ * φ' = (φ * ψ - ψ * φ) + (e * ψ - ψ * e) by simp only [e]; noncomm_ring,
      tateTrace_add_of_mem hc.1 hc.2 ((he₁.mul_right ψ).sub (he₁.mul_left (hψ.toE hA)))
        ((he₂.mul_right (hψ.toE hA)).sub (he₂.mul_left ψ)),
      tateTrace_commutator_eq_zero he₁ he₂ (hψ.toE hA), add_zero]
  rw [← step₁ hφ hφ' hψ]
  have h₁ := step₁ hψ hψ' hφ'
  rw [show φ' * ψ' - ψ' * φ' = -(ψ' * φ' - φ' * ψ') by abel,
    show φ' * ψ - ψ * φ' = -(ψ * φ' - φ' * ψ) by abel, tateTrace_neg, tateTrace_neg, h₁]

variable (K) in
/-- Tate's residue pairing `(f, g) ↦ Tr_V [π f, π g]` for the chosen projection `π` onto `A`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
noncomputable def resPair (A : Submodule k V) (f g : K) : k :=
  (proj A * act k f * (proj A * act k g) - proj A * act k g * (proj A * act k f)).tateTrace

/-- The residue pairing can be computed with any lifts. -/
theorem resPair_eq (hA : Admissible K A) (hφ : IsLift A f φ) (hψ : IsLift A g ψ) :
    resPair K A f g = (φ * ψ - ψ * φ).tateTrace :=
  tateTrace_commutator_eq hA (isLift_lift hA f) hφ (isLift_lift hA g) hψ

lemma resPair_add_left (hA : Admissible K A) (f₁ f₂ g : K) :
    resPair K A (f₁ + f₂) g = resPair K A f₁ g + resPair K A f₂ g := by
  have h₁ := isLift_lift hA f₁
  have h₂ := isLift_lift hA f₂
  have hg := isLift_lift hA g
  rw [resPair_eq hA (h₁.add h₂) hg, resPair_eq hA h₁ hg, resPair_eq hA h₂ hg]
  have c₁ := h₁.commutator_mem hA hg
  have c₂ := h₂.commutator_mem hA hg
  rw [← tateTrace_add_of_mem c₁.1 c₁.2 c₂.1 c₂.2]
  congr 1
  noncomm_ring

lemma resPair_smul_left (hA : Admissible K A) (c : k) (f g : K) :
    resPair K A (c • f) g = c * resPair K A f g := by
  have h₁ := isLift_lift hA f
  have hg := isLift_lift hA g
  rw [resPair_eq hA (h₁.smul c) hg, resPair_eq hA h₁ hg, ← tateTrace_smul, smul_sub,
    smul_mul_assoc, mul_smul_comm]

lemma resPair_swap (hA : Admissible K A) (f g : K) : resPair K A g f = -resPair K A f g := by
  have hf := isLift_lift hA f
  have hg := isLift_lift hA g
  rw [resPair_eq hA hg hf, resPair_eq hA hf hg, ← tateTrace_neg, neg_sub]

lemma resPair_add_right (hA : Admissible K A) (f g₁ g₂ : K) :
    resPair K A f (g₁ + g₂) = resPair K A f g₁ + resPair K A f g₂ := by
  rw [resPair_swap hA, resPair_add_left hA, neg_add, ← resPair_swap hA, ← resPair_swap hA]

lemma resPair_smul_right (hA : Admissible K A) (c : k) (f g : K) :
    resPair K A f (c • g) = c * resPair K A f g := by
  rw [resPair_swap hA, resPair_smul_left hA, ← mul_neg, ← resPair_swap hA]

/-- **Tate's Theorem 1 (Leibniz rule)**: `res(fg, h) = res(f, gh) + res(g, hf)`. -/
lemma resPair_mul_left (hA : Admissible K A) (f g h : K) :
    resPair K A (f * g) h = resPair K A f (g * h) + resPair K A g (h * f) := by
  have hf := isLift_lift hA f
  have hg := isLift_lift hA g
  have hh := isLift_lift hA h
  rw [resPair_eq hA (hf.mul hA hg) hh, resPair_eq hA hf (hg.mul hA hh),
    resPair_eq hA hg (hh.mul hA hf)]
  have c₁ := hf.commutator_mem hA (hg.mul hA hh)
  have c₂ := hg.commutator_mem hA (hh.mul hA hf)
  rw [← tateTrace_add_of_mem c₁.1 c₁.2 c₂.1 c₂.2]
  congr 1
  noncomm_ring

lemma resPair_leibniz (hA : Admissible K A) (a b c : K) :
    resPair K A c (a * b) = resPair K A (a * c) b + resPair K A (b * c) a := by
  rw [resPair_swap hA, resPair_mul_left hA, neg_add, ← resPair_swap hA, ← resPair_swap hA,
    mul_comm c a, add_comm]

section Derivation

attribute [local instance] Algebra.precompModule Algebra.precompModule_isScalarTower

/-- The derivation `g ↦ (f ↦ res(f, g))` of `K` into `Hom_k(K, k)`. -/
noncomputable def resDerivation (hA : Admissible K A) : Derivation k K (K →ₗ[k] k) :=
  Derivation.mk'
    { toFun g :=
        { toFun f := resPair K A f g
          map_add' f₁ f₂ := resPair_add_left hA f₁ f₂ g
          map_smul' c f := resPair_smul_left hA c f g }
      map_add' g₁ g₂ := LinearMap.ext fun f ↦ resPair_add_right hA f g₁ g₂
      map_smul' c g := LinearMap.ext fun f ↦ resPair_smul_right hA c f g }
    fun a b ↦ LinearMap.ext fun c ↦ by
      change resPair K A c (a * b) = resPair K A (a * c) b + resPair K A (b * c) a
      exact resPair_leibniz hA a b c

lemma resDerivation_apply (hA : Admissible K A) (f g : K) :
    resDerivation hA g f = resPair K A f g := rfl

open Classical in
variable (K) in
/-- **Tate's residue** `res_{V,A} : Ω[K⁄k] → k`, characterised by
`res (f • D g) = Tr_V [π f, π g]` (`TateResidue.res_smul_D`); it is `0` when `A` is not
admissible (blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
noncomputable def res (A : Submodule k V) : Ω[K⁄k] →ₗ[k] k :=
  if hA : Admissible K A then
    { toFun ω := (resDerivation hA).liftKaehlerDifferential ω 1
      map_add' ω ω' := by rw [map_add, LinearMap.add_apply]
      map_smul' c ω := by
        rw [← algebraMap_smul K c ω, LinearMap.map_smul, Algebra.precompModule_smul_apply,
          mul_one, Algebra.algebraMap_eq_smul_one, map_smul]
        rfl }
  else 0

lemma res_smul_D_eq_resPair (hA : Admissible K A) (f g : K) :
    res K A (f • D k K g) = resPair K A f g := by
  rw [res, dite_eq_left hA]
  change (resDerivation hA).liftKaehlerDifferential (f • D k K g) 1 = _
  rw [LinearMap.map_smul, Algebra.precompModule_smul_apply, mul_one,
    Derivation.liftKaehlerDifferential_comp_D, resDerivation_apply]

end Derivation

lemma res_of_not_admissible (hA : ¬ Admissible K A) : res K A = 0 := by
  rw [res, dite_eq_right hA]

/-- **Tate's residue, characterisation**: `res (f • D g) = Tr_V [φ, ψ]` for any lifts `φ, ψ` of
`f, g` (e.g. `φ = π ∘ f`, `ψ = π ∘ g` for a projection `π` of `V` onto `A`). -/
theorem res_smul_D (hA : Admissible K A) (hφ : IsLift A f φ) (hψ : IsLift A g ψ) :
    res K A (f • D k K g) = (φ * ψ - ψ * φ).tateTrace := by
  rw [res_smul_D_eq_resPair hA, resPair_eq hA hφ hψ]

/-- `res (f • D g) = Tr_V [π f, π g]` for any projection `π` of `V` onto `A`. -/
theorem res_smul_D_proj (hA : Admissible K A) {π : Module.End k V} (hπ : ∀ v, π v ∈ A)
    (hπA : ∀ a ∈ A, π a = a) (f g : K) :
    res K A (f • D k K g) =
      (π * act k f * (π * act k g) - π * act k g * (π * act k f)).tateTrace :=
  res_smul_D hA (isLift_proj_mul hA hπ hπA f) (isLift_proj_mul hA hπ hπA g)

lemma res_ext {B : Submodule k V} (h : ∀ f g : K, res K A (f • D k K g) = res K B (f • D k K g)) :
    res K A = res K B :=
  linearMap_ext_smul_D h

lemma admissible_of_almostLE (hA : Admissible K A) {B : Submodule k V} (hAB : A.AlmostLE B)
    (hBA : B.AlmostLE A) : Admissible K B :=
  fun f ↦ ((hBA.map _).trans (hA f)).trans hAB

lemma E₂.of_almostLE {B : Submodule k V} (hBA : B.AlmostLE A) (hφ : E₂ A φ) : E₂ B φ := by
  obtain ⟨W, hW, h⟩ := hBA
  exact (hφ.sup (hW.map φ)).of_le ((map_mono h).trans (Submodule.map_sup _ _ _).le)

lemma IsLift.of_almostLE {B : Submodule k V} (hAB : A.AlmostLE B) (hBA : B.AlmostLE A)
    (hφ : IsLift A f φ) : IsLift B f φ :=
  ⟨hφ.1.trans hAB, hφ.2.of_almostLE hBA⟩

/-- **(R1)** Tate's residue only depends on the commensurability class of `A`. -/
theorem res_eq_of_almostLE {B : Submodule k V} (hAB : A.AlmostLE B) (hBA : B.AlmostLE A) :
    res K A = res K B := by
  by_cases hA : Admissible K A
  · have hB := admissible_of_almostLE hA hAB hBA
    refine res_ext fun f g ↦ ?_
    have hf := isLift_lift hA f
    have hg := isLift_lift hA g
    rw [res_smul_D hA hf hg, res_smul_D hB (hf.of_almostLE hAB hBA) (hg.of_almostLE hAB hBA)]
  · have hB : ¬ Admissible K B := fun hB ↦ hA (admissible_of_almostLE hB hBA hAB)
    rw [res_of_not_admissible hA, res_of_not_admissible hB]

/-- **(R1)** `res_{V,A} = 0` if `A` is finite-dimensional. -/
theorem res_eq_zero_of_fg (hA : A.FG) : res K A = 0 := by
  have hadm : Admissible K A := fun f ↦ AlmostLE.of_fg (hA.map _)
  have hl : ∀ f : K, IsLift A f 0 := fun f ↦ ⟨E₁.zero, by rw [zero_sub]; exact (hA.map _)⟩
  refine linearMap_ext_smul_D fun f g ↦ ?_
  rw [res_smul_D hadm (hl f) (hl g)]
  simp

/-- **(R1)** `res_{V,A} = 0` if `V / A` is finite-dimensional. -/
theorem res_eq_zero_of_top_almostLE (hA : (⊤ : Submodule k V).AlmostLE A) : res K A = 0 := by
  have hadm : Admissible K A := fun f ↦ (AlmostLE.of_le le_top).trans hA
  have hl : ∀ f : K, IsLift A f (act k f) := fun f ↦
    ⟨(AlmostLE.of_le le_top).trans hA, by rw [sub_self]; exact E₂.zero⟩
  refine linearMap_ext_smul_D fun f g ↦ ?_
  rw [res_smul_D hadm (hl f) (hl g), act_comm, sub_self]
  simp

/-- **(R2)** `res (f • D g) = 0` if `f A ⊆ A` and `g A ⊆ A`. -/
theorem res_smul_D_eq_zero (hf : ∀ a ∈ A, f • a ∈ A) (hg : ∀ a ∈ A, g • a ∈ A) :
    res K A (f • D k K g) = 0 := by
  by_cases hA : Admissible K A
  · have hπ := proj_mem A
    have hπA : ∀ a ∈ A, proj A a = a := fun _ ↦ proj_apply_of_mem
    rw [res_smul_D hA (isLift_mul_proj hπ hπA hf) (isLift_mul_proj hπ hπA hg)]
    have : act k f * proj A * (act k g * proj A) - act k g * proj A * (act k f * proj A) = 0 := by
      ext v
      simp only [LinearMap.sub_apply, mul_apply, act_apply, LinearMap.zero_apply,
        hπA _ (hg _ (hπ v)),
        hπA _ (hf _ (hπ v)), smul_smul, mul_comm f g, sub_self]
    rw [this, tateTrace_zero]
  · rw [res_of_not_admissible hA, LinearMap.zero_apply]

/-- **(R2)** `res_{V,A} = 0` if `A` is stable under `K`. -/
theorem res_eq_zero_of_forall_smul_mem (hA : ∀ f : K, ∀ a ∈ A, f • a ∈ A) : res K A = 0 :=
  linearMap_ext_smul_D fun f g ↦ by rw [res_smul_D_eq_zero (hA f) (hA g), LinearMap.zero_apply]

end TateResidue
