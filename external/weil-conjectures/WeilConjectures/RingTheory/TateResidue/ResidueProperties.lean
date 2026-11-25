/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TateResidue.Residue

/-!
# Properties of Tate's residue

We prove the remaining basic properties of Tate's abstract residue `res_{V,A}`:

- `TateResidue.res_eq_add_of_exact`: for a short exact sequence `0 → V₁ → V → V₃ → 0` of
  `K`-modules, `res_{V,A} = res_{V₁, A ∩ V₁} + res_{V₃, image of A}`.
- `TateResidue.res_prod` **(R4)**: `res_{V₁ × V₂, A₁ × A₂} = res_{V₁,A₁} + res_{V₂,A₂}`.
- `TateResidue.res_sup_add_res_inf` **(R3)**: `res_{A + B} + res_{A ∩ B} = res_A + res_B`.
- `TateResidue.res_mul_inv_smul_D` **(R5)**: `res(u g⁻¹ dg) = Tr_k(u | A / g A)` when `u, g`
  preserve `A`, `g` is a unit and `A / g A` is finite-dimensional.
-/

@[expose] public section

open LinearMap Submodule Module.End KaehlerDifferential

namespace TateResidue

section Intertwine

variable {k W₁ W : Type*} [Field k] [AddCommGroup W₁] [Module k W₁] [AddCommGroup W]
  [Module k W]

lemma mul_intertwine (j : W₁ →ₗ[k] W) {a b : Module.End k W} {a₁ b₁ : Module.End k W₁}
    (ha : ∀ x, a (j x) = j (a₁ x)) (hb : ∀ x, b (j x) = j (b₁ x)) (x : W₁) :
    (a * b) (j x) = j ((a₁ * b₁) x) := by
  simp [mul_apply, ha, hb]

lemma commutator_intertwine (j : W₁ →ₗ[k] W) {a b : Module.End k W} {a₁ b₁ : Module.End k W₁}
    (ha : ∀ x, a (j x) = j (a₁ x)) (hb : ∀ x, b (j x) = j (b₁ x)) :
    (a * b - b * a) ∘ₗ j = j ∘ₗ (a₁ * b₁ - b₁ * a₁) := by
  ext x
  simp [mul_apply, ha, hb]

end Intertwine

variable {k K V V₁ V₃ : Type*} [Field k] [CommRing K] [Algebra k K]
  [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]
  [AddCommGroup V₁] [Module k V₁] [Module K V₁] [IsScalarTower k K V₁]
  [AddCommGroup V₃] [Module k V₃] [Module K V₃] [IsScalarTower k K V₃]

/-- **Additivity of the residue in exact sequences**: for a short exact sequence
`0 → V₁ → V → V₃ → 0` of `K`-modules and an admissible `A ⊆ V`,
`res_{V,A} = res_{V₁, i⁻¹ A} + res_{V₃, q A}` (blueprint:
`theorem-riemann-roch-coherent-serre-duality--2`). -/
theorem res_eq_add_of_exact (i : V₁ →ₗ[K] V) (q : V →ₗ[K] V₃) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q) {A : Submodule k V}
    (hA : Admissible K A) :
    res K A = res K (A.comap (i.restrictScalars k)) + res K (A.map (q.restrictScalars k)) := by
  set i' := i.restrictScalars k
  set q' := q.restrictScalars k
  set A₁ := A.comap i'
  set A₃ := A.map q'
  have hA₁ : Admissible K A₁ := fun f ↦ by
    refine AlmostLE.mono_left ?_ ((hA f).comap i')
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨i x, hx, (map_smul i f x).symm⟩
  have hA₃ : Admissible K A₃ := fun f ↦ by
    refine AlmostLE.mono_left ?_ ((hA f).map q')
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f • a, ⟨a, ha, rfl⟩, map_smul q f a⟩
  obtain ⟨π, hπ, hπA, hπN⟩ := exists_proj A (range i')
  obtain ⟨r₀, hr₀⟩ := i'.exists_leftInverse_of_injective (ker_eq_bot.2 hi)
  obtain ⟨s, hs⟩ := q'.exists_rightInverse_of_surjective (range_eq_top.2 hq)
  have hr₀i : ∀ x, r₀ (i x) = x := fun x ↦ congr($hr₀ x)
  have hqs : ∀ y, q (s y) = y := fun y ↦ congr($hs y)
  set π₁ := r₀ ∘ₗ π ∘ₗ i'
  set π₃ := q' ∘ₗ π ∘ₗ s
  have hπ₁ : ∀ x, π (i x) = i (π₁ x) := by
    intro x
    obtain ⟨y, hy⟩ := hπN (i x) ⟨x, rfl⟩
    change π (i x) = i (r₀ (π (i x)))
    rw [← hy]
    change i y = i (r₀ (i y))
    rw [hr₀i]
  have hπ₃ : ∀ x, π₃ (q x) = q (π x) := by
    intro x
    obtain ⟨y, hy⟩ := (hex (s (q x) - x)).1 (by rw [map_sub, hqs, sub_self])
    change q (π (s (q x))) = q (π x)
    rw [show s (q x) = x + i y by rw [hy]; abel, map_add, map_add, hπ₁, hex.apply_apply_eq_zero,
      add_zero]
  have hπ₁mem : ∀ x, π₁ x ∈ A₁ := fun x ↦ by
    change i (π₁ x) ∈ A
    rw [← hπ₁]
    exact hπ _
  have hπ₁A : ∀ a ∈ A₁, π₁ a = a := fun a ha ↦ hi (by rw [← hπ₁]; exact hπA _ ha)
  have hπ₃mem : ∀ x, π₃ x ∈ A₃ := fun x ↦ ⟨π (s x), hπ _, rfl⟩
  have hπ₃A : ∀ a ∈ A₃, π₃ a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change π₃ (q a) = q a
    rw [hπ₃, hπA a ha]
  have hact₁ : ∀ (f : K) x, act k f (i' x) = i' (act k f x) := fun f x ↦ (map_smul i f x).symm
  have hact₃ : ∀ (f : K) x, act k f (q' x) = q' (act k f x) := fun f x ↦ (map_smul q f x).symm
  refine linearMap_ext_smul_D fun f g ↦ ?_
  rw [LinearMap.add_apply, res_smul_D_proj hA hπ hπA, res_smul_D_proj hA₁ hπ₁mem hπ₁A,
    res_smul_D_proj hA₃ hπ₃mem hπ₃A]
  have hπ₁' : ∀ x, π (i' x) = i' (π₁ x) := hπ₁
  have hπ₃' : ∀ x, π₃ (q' x) = q' (π x) := hπ₃
  have hf₁ := mul_intertwine i' hπ₁' (hact₁ f)
  have hg₁ := mul_intertwine i' hπ₁' (hact₁ g)
  have hf₃ := mul_intertwine q' (a := π₃) (b := act k f) (a₁ := π) (b₁ := act k f)
    (fun x ↦ hπ₃' x) (hact₃ f)
  have hg₃ := mul_intertwine q' (a := π₃) (b := act k g) (a₁ := π) (b₁ := act k g)
    (fun x ↦ hπ₃' x) (hact₃ g)
  have hc := (isLift_proj_mul hA hπ hπA f).commutator_mem hA (isLift_proj_mul hA hπ hπA g)
  exact tateTrace_eq_add_of_exact i' q' hi hq hex _ _ _ (commutator_intertwine i' hf₁ hg₁)
    (commutator_intertwine q' hf₃ hg₃).symm (isFinitePotent_of_mem hc.1 hc.2)

variable {V₂ : Type*} [AddCommGroup V₂] [Module k V₂] [Module K V₂] [IsScalarTower k K V₂]

lemma Admissible.prod {A : Submodule k V} {B : Submodule k V₂} (hA : Admissible K A)
    (hB : Admissible K B) : Admissible K (A.prod B) := fun f ↦ by
  refine (AlmostLE.prod (hA f) (hB f)).mono_left ?_
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

/-- **(R4)** The residue of a product: `res_{V × V₂, A × B} = res_{V,A} + res_{V₂,B}`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
theorem res_prod {A : Submodule k V} {B : Submodule k V₂} (hA : Admissible K A)
    (hB : Admissible K B) : res K (A.prod B) = res K A + res K B := by
  have hex : Function.Exact (LinearMap.inl K V V₂) (LinearMap.snd K V V₂) := by
    intro y
    exact ⟨fun h ↦ ⟨y.1, Prod.ext rfl h.symm⟩, by rintro ⟨x, rfl⟩; rfl⟩
  rw [res_eq_add_of_exact (LinearMap.inl K V V₂) (LinearMap.snd K V V₂) (inl_injective)
    (snd_surjective) hex (hA.prod hB)]
  congr 2
  · ext x
    simp
  · ext y
    simp only [mem_map, mem_prod, restrictScalars_apply, snd_apply, Prod.exists]
    exact ⟨by rintro ⟨_, _, ⟨_, h⟩, rfl⟩; exact h, fun h ↦ ⟨0, y, ⟨A.zero_mem, h⟩, rfl⟩⟩

/-- **(R3)** `res_{A + B} + res_{A ∩ B} = res_A + res_B` (blueprint:
`theorem-riemann-roch-coherent-serre-duality--2`). -/
theorem res_sup_add_res_inf {A B : Submodule k V} (hA : Admissible K A) (hB : Admissible K B) :
    res K (A ⊔ B) + res K (A ⊓ B) = res K A + res K B := by
  let d : V →ₗ[K] V × V := LinearMap.prod LinearMap.id LinearMap.id
  let q : V × V →ₗ[K] V := LinearMap.fst K V V - LinearMap.snd K V V
  have hd : Function.Injective d := fun x y h ↦ congr(($h).1)
  have hq : Function.Surjective q := fun x ↦ ⟨(x, 0), by simp [q]⟩
  have hex : Function.Exact d q := by
    intro y
    refine ⟨fun h ↦ ⟨y.1, Prod.ext rfl ?_⟩, by rintro ⟨x, rfl⟩; simp [q, d]⟩
    change y.1 = y.2
    simpa [q, sub_eq_zero] using h
  have hc : (A.prod B).comap (d.restrictScalars k) = A ⊓ B := by
    ext x
    simp [d]
  have hm : (A.prod B).map (q.restrictScalars k) = A ⊔ B := by
    ext y
    simp only [mem_map, mem_prod, restrictScalars_apply, Prod.exists, q, LinearMap.sub_apply,
      fst_apply, snd_apply]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact sub_mem_sup ha hb
    · intro h
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 h
      exact ⟨a, -b, ⟨ha, B.neg_mem hb⟩, by abel⟩
  rw [← res_prod hA hB, res_eq_add_of_exact d q hd hq hex (hA.prod hB), hc, hm, add_comm]

section R5

variable {A : Submodule k V}

/-- The subspace `g A ⊆ A`, as a submodule of `A`. -/
noncomputable def smulSub (A : Submodule k V) (g : K) : Submodule k A :=
  (A.map (act k g)).comap A.subtype

lemma smulSub_le_comap {u g : K} (huA : ∀ a ∈ A, u • a ∈ A) :
    smulSub A g ≤ (smulSub A g).comap ((act k u).restrict huA) := by
  rintro x ⟨b, hb, hbx⟩
  refine ⟨u • b, huA b hb, ?_⟩
  change g • u • b = u • (x : V)
  have hbx' : g • b = (x : V) := hbx
  rw [← hbx', smul_smul, smul_smul, mul_comm]

/-- Multiplication by `u` on `A / g A`. -/
noncomputable def quotAct (A : Submodule k V) (g u : K) (huA : ∀ a ∈ A, u • a ∈ A) :
    Module.End k (A ⧸ smulSub A g) :=
  (smulSub A g).mapQ (smulSub A g) ((act k u).restrict huA) (smulSub_le_comap huA)

/-- **(R5) Tate's formula**: if `u, g ∈ K` preserve `A`, `g` is a unit and `A / g A` is
finite-dimensional, then `res (u g⁻¹ dg) = Tr_k (u | A / g A)`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
theorem res_mul_inv_smul_D (hA : Admissible K A) {u g : K} (hg : IsUnit g)
    (hgA : ∀ a ∈ A, g • a ∈ A) (huA : ∀ a ∈ A, u • a ∈ A)
    [FiniteDimensional k (A ⧸ smulSub A g)] :
    res K A ((u * ↑hg.unit⁻¹) • D k K g) = trace k _ (quotAct A g u huA) := by
  set h := u * ↑hg.unit⁻¹
  have hhg : h * g = u := by simp [h, mul_assoc]
  set π := proj A
  have hπ := proj_mem A
  have hπA : ∀ a ∈ A, π a = a := fun _ ↦ proj_apply_of_mem
  have hlh := isLift_lift hA h
  have hlg := isLift_mul_proj hπ hπA hgA
  rw [res_smul_D hA hlh hlg]
  set X := π * act k h * (act k g * π) - act k g * π * (π * act k h)
  have hXapply : ∀ v, X v = π (u • π v) - g • π (π (h • v)) := by
    intro v
    simp only [X, LinearMap.sub_apply, mul_apply, act_apply, smul_smul, hhg]
  have hXA : ∀ v, X v ∈ A := fun v ↦ by
    rw [hXapply]
    exact sub_mem (hπ _) (hgA _ (hπ _))
  have hXg : ∀ b ∈ A, X (g • b) = 0 := by
    intro b hb
    rw [hXapply, hπA _ (hgA b hb), smul_smul, hπA _ (by rw [← smul_smul]; exact huA _ (hgA b hb)),
      smul_smul, hhg, hπA _ (huA b hb), hπA _ (huA b hb), smul_smul, mul_comm, sub_self]
  have hXu : ∀ a ∈ A, X a - u • a = -(g • π (π (h • a))) := by
    intro a ha
    rw [hXapply, hπA a ha, hπA _ (huA a ha)]
    abel
  have hc := hlh.commutator_mem hA hlg
  -- first step: restrict to `A`
  set X₁ : Module.End k A := X.restrict (fun v _ ↦ hXA v)
  have hexA : Function.Exact A.subtype A.mkQ := by
    intro y
    rw [mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
  rw [tateTrace_eq_add_of_exact A.subtype A.mkQ A.injective_subtype A.mkQ_surjective hexA X₁ X 0
    (by ext; rfl) (by ext v; simp [Submodule.Quotient.mk_eq_zero, hXA v])
    (isFinitePotent_of_mem hc.1 hc.2), tateTrace_zero, add_zero]
  -- second step: the quotient `A / g A`
  set S := smulSub A g
  have hexS : Function.Exact S.subtype S.mkQ := by
    intro y
    rw [mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
  have hX₁fp : X₁.IsFinitePotent := by
    refine ⟨1, fg_of_fg_map_injective A.subtype A.injective_subtype (hc.2.of_le ?_)⟩
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, a.2, rfl⟩
  rw [tateTrace_eq_add_of_exact S.subtype S.mkQ S.injective_subtype S.mkQ_surjective hexS 0 X₁
    (quotAct A g u huA) ?_ ?_ hX₁fp, tateTrace_zero, zero_add, tateTrace_eq_trace]
  · refine LinearMap.ext fun y ↦ Subtype.ext ?_
    obtain ⟨⟨x, hxA⟩, b, hb, hbx⟩ := y
    have hbx' : g • b = x := hbx
    change X x = 0
    rw [← hbx', hXg b hb]
  · ext a
    change S.mkQ (X₁ a) = S.mkQ ((act k u).restrict huA a)
    rw [mkQ_apply, mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-(π (π (h • (a : V)))), A.neg_mem (hπ _), ?_⟩
    change g • -(π (π (h • (a : V)))) = X a - u • (a : V)
    rw [hXu a a.2, smul_neg]

/-- **(R5)**, special case `u = 1`: `res (g⁻¹ dg) = dim_k (A / g A)`. -/
theorem res_inv_smul_D (hA : Admissible K A) {g : K} (hg : IsUnit g)
    (hgA : ∀ a ∈ A, g • a ∈ A) [FiniteDimensional k (A ⧸ smulSub A g)] :
    res K A ((↑hg.unit⁻¹ : K) • D k K g) = Module.finrank k (A ⧸ smulSub A g) := by
  have h1 : ∀ a ∈ A, (1 : K) • a ∈ A := fun a ha ↦ by rwa [one_smul]
  have := res_mul_inv_smul_D hA hg hgA h1
  rw [one_mul] at this
  rw [this]
  have : quotAct A g 1 h1 = 1 := by
    ext a
    change Submodule.Quotient.mk ((act k (1 : K)).restrict h1 a) = Submodule.Quotient.mk a
    congr 1
    ext
    simp
  rw [this, trace_one]

end R5

end TateResidue
