/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TateResidue.LocalResidue

/-!
# Tate's abstract residue theorem

Let `k` be a field, `K` a commutative `k`-algebra and `(O x)_{x ∈ P}` a family of
`k`-subalgebras of `K` such that

- `f O_x ~ O_x` for all `f ∈ K` and all `x`;
- every `f ∈ K` lies in `O_x` for all but finitely many `x`;
- `⋂_x O_x` is finite-dimensional over `k`;
- the cokernel of the principal-parts map `K → ⊕_x K / O_x` is finite-dimensional over `k`.

Then for every `η ∈ Ω[K⁄k]`, `res_{O_x}(η) = 0` for almost all `x` and `∑_x res_{O_x}(η) = 0`.

The proof follows Tate (*Residues of differentials on curves*, §2), without completions: on the
restricted product `V = {(a_x) ∈ ∏_x K : a_x ∈ O_x for almost all x}` consider `A = ∏_x O_x` and
the diagonal `B = K`. Then `A ∩ B = ⋂ O_x` is finite-dimensional, `V / (A + B)` is the cokernel
above, and `B` is `K`-stable, so `res_{V,A} = 0` by (R1)–(R3). Computing `res_{V,A}` with
componentwise lifts gives `res_{V,A} (f dg) = ∑_{x ∈ S} res_{O_x} (f dg)` where `S` is the set of
places where `f` or `g` is not integral.

## Main definitions

- `TateResidue.restrictedProduct O hfin`: the restricted product of the `(K, O_x)`.
- `TateResidue.principalParts O hfin : K →ₗ[k] Π₀ x, K ⧸ O_x`.

## Main results

- `TateResidue.residue_theorem`: the abstract residue theorem.
-/

@[expose] public section

open LinearMap Submodule Module.End KaehlerDifferential

namespace TateResidue

variable {k K : Type*} [Field k] [CommRing K] [Algebra k K] {P : Type*} (O : P → Subalgebra k K)

section PrincipalParts

open Classical in
/-- The family of classes of a function `a : P → K` in `K ⧸ O_x`, finitely supported when
`a x ∈ O x` for almost all `x`. -/
noncomputable def toDFinsupp (a : P → K) (ha : {x | a x ∉ O x}.Finite) :
    Π₀ x, K ⧸ Subalgebra.toSubmodule (O x) :=
  DFinsupp.mk ha.toFinset fun x ↦ Submodule.Quotient.mk (a x)

lemma toDFinsupp_apply (a : P → K) (ha : {x | a x ∉ O x}.Finite) (x : P) :
    toDFinsupp O a ha x = Submodule.Quotient.mk (a x) := by
  classical
  rw [toDFinsupp, DFinsupp.mk_apply]
  split_ifs with h
  · rfl
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h
    exact ((Submodule.Quotient.mk_eq_zero _).2 h).symm

variable (hfin : ∀ f : K, {x | f ∉ O x}.Finite)

/-- The principal parts map `K → ⊕_x K / O_x`, `f ↦ (f mod O_x)_x`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
noncomputable def principalParts : K →ₗ[k] Π₀ x, K ⧸ Subalgebra.toSubmodule (O x) where
  toFun f := toDFinsupp O (fun _ ↦ f) (hfin f)
  map_add' f g := by
    ext x
    simp [toDFinsupp_apply]
  map_smul' c f := by
    ext x
    simp [toDFinsupp_apply]

lemma principalParts_apply (f : K) (x : P) :
    principalParts O hfin f x = Submodule.Quotient.mk f :=
  toDFinsupp_apply O _ _ x

end PrincipalParts

variable (hfin : ∀ f : K, {x | f ∉ O x}.Finite)

section RestrictedProduct

/-- The restricted product `{(a_x) ∈ ∏_x K : a_x ∈ O_x for almost all x}`, a `K`-module
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
def restrictedProduct : Submodule K (P → K) where
  carrier := {a | {x | a x ∉ O x}.Finite}
  add_mem' {a b} ha hb := (ha.union hb).subset fun x hx ↦ by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h hx
    exact hx ((O x).add_mem h.1 h.2)
  zero_mem' := by simp [(O _).zero_mem]
  smul_mem' f a ha := ((hfin f).union ha).subset fun x hx ↦ by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Pi.smul_apply,
      smul_eq_mul] at h hx
    exact hx ((O x).mul_mem h.1 h.2)

local notation "𝔸" => restrictedProduct O hfin

lemma mem_restrictedProduct {a : P → K} : a ∈ 𝔸 ↔ {x | a x ∉ O x}.Finite := Iff.rfl

/-- The integral part `∏_x O_x` of the restricted product. -/
def integralPart : Submodule k 𝔸 where
  carrier := {v | ∀ x, (v : P → K) x ∈ O x}
  add_mem' ha hb x := (O x).add_mem (ha x) (hb x)
  zero_mem' x := (O x).zero_mem
  smul_mem' c v hv x := by simpa using (O x).smul_mem (hv x) c

/-- The diagonal embedding `K → 𝔸`. -/
def diag : K →ₗ[k] 𝔸 where
  toFun f := ⟨fun _ ↦ f, hfin f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma diag_smul (f g : K) : f • diag O hfin g = diag O hfin (f * g) := rfl

/-- Evaluation at `x`. -/
def evalAt (x : P) : 𝔸 →ₗ[k] K :=
  (LinearMap.proj x : (P → K) →ₗ[k] K) ∘ₗ ((restrictedProduct O hfin).subtype.restrictScalars k)

@[simp] lemma evalAt_apply (x : P) (v : 𝔸) : evalAt O hfin x v = (v : P → K) x := rfl

/-- The endomorphism of `𝔸` acting by `c x` on the `x`-component, when `c x` takes values in
`O x`. -/
def piEnd (c : P → Module.End k K) (hc : ∀ x y, c x y ∈ O x) : Module.End k 𝔸 :=
  (LinearMap.pi fun x ↦ c x ∘ₗ evalAt O hfin x).codRestrict
    ((restrictedProduct O hfin).restrictScalars k) fun v ↦ by
    refine Set.finite_empty.subset fun x hx ↦ ?_
    exact hx (hc x _)

@[simp] lemma coe_piEnd_apply (c : P → Module.End k K) (hc : ∀ x y, c x y ∈ O x) (v : 𝔸)
    (x : P) : (piEnd O hfin c hc v : P → K) x = c x ((v : P → K) x) := rfl

/-- The projection of `K` onto `O x`. -/
noncomputable abbrev projO (x : P) : Module.End k K := proj (Subalgebra.toSubmodule (O x))

omit hfin in
lemma projO_mem (x : P) (y : K) : projO O x y ∈ O x := proj_mem (Subalgebra.toSubmodule (O x)) y

omit hfin in
lemma projO_apply_of_mem {x : P} {a : K} (ha : a ∈ O x) : projO O x a = a :=
  proj_apply_of_mem (A := Subalgebra.toSubmodule (O x)) ha

section DecidableEq

variable [DecidableEq P]

/-- The element of `𝔸` concentrated at `x`. -/
def single (x : P) : K →ₗ[k] 𝔸 :=
  (LinearMap.single k (fun _ : P ↦ K) x).codRestrict
    ((restrictedProduct O hfin).restrictScalars k) fun c ↦ by
    refine (Set.finite_singleton x).subset fun y hy ↦ ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, LinearMap.coe_single, Pi.single_apply,
      ite_eq_right (show y ≠ x from h)] at hy
    exact hy (O y).zero_mem

@[simp] lemma coe_single (x : P) (c : K) : (single O hfin x c : P → K) = Pi.single x c := rfl

@[simp] lemma evalAt_single_self (x : P) (c : K) : evalAt O hfin x (single O hfin x c) = c := by
  simp

lemma evalAt_single_of_ne {x y : P} (h : x ≠ y) (c : K) :
    evalAt O hfin x (single O hfin y c) = 0 := by
  simp [h]

/-- The componentwise lift of the multiplication by `h`: `π_x ∘ h` at `x ∈ S` and `h ∘ π_x`
elsewhere (where `h ∈ O_x`). -/
noncomputable def piLift (S : Finset P) (h : K) (hh : ∀ x ∉ S, h ∈ O x) : Module.End k 𝔸 :=
  piEnd O hfin (fun x ↦ if x ∈ S then projO O x * act k h else act k h * projO O x) <| by
    intro x y
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx]
      exact projO_mem O x _
    · rw [ite_eq_right hx, mul_apply, act_apply, smul_eq_mul]
      exact (O x).mul_mem (hh x hx) (projO_mem O x _)

lemma piLift_apply (S : Finset P) (h : K) (hh : ∀ x ∉ S, h ∈ O x) (v : 𝔸) (x : P) :
    (piLift O hfin S h hh v : P → K) x =
      if x ∈ S then projO O x (h * (v : P → K) x) else h * projO O x ((v : P → K) x) := by
  rw [piLift, coe_piEnd_apply]
  split_ifs <;> rfl

lemma piLift_mem (S : Finset P) (h : K) (hh : ∀ x ∉ S, h ∈ O x) (v : 𝔸) :
    piLift O hfin S h hh v ∈ integralPart O hfin := fun x ↦ by
  rw [piLift_apply]
  split_ifs with hx
  · exact projO_mem O x _
  · exact (O x).mul_mem (hh x hx) (projO_mem O x _)

variable (hadm : ∀ x, Admissible K (Subalgebra.toSubmodule (O x)))
include hadm

lemma isLift_piLift (S : Finset P) (h : K) (hh : ∀ x ∉ S, h ∈ O x) :
    IsLift (integralPart O hfin) h (piLift O hfin S h hh) := by
  refine ⟨E₁.of_le ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact piLift_mem O hfin S h hh v
  set W : P → Submodule k 𝔸 := fun x ↦
    ((Subalgebra.toSubmodule (O x)).map (projO O x * act k h - act k h)).map (single O hfin x)
  have hW : ∀ x ∈ S, (W x).FG := fun x _ ↦
    ((isLift_proj_mul (hadm x) (proj_mem _) (fun _ ↦ proj_apply_of_mem) h).2).map _
  refine (fg_biSup S W hW).of_le ?_
  rintro _ ⟨a, ha, rfl⟩
  have : (piLift O hfin S h hh - act k (V := 𝔸) h) a =
      ∑ x ∈ S, single O hfin x
        ((projO O x * act k h - act k h : Module.End k K) ((a : P → K) x)) := by
    refine Subtype.ext (funext fun y ↦ ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [coe_single, Finset.sum_pi_single]
    rw [LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, piLift_apply]
    change _ - h * (a : P → K) y = _
    split_ifs with hy
    · rfl
    · rw [projO_apply_of_mem O (ha y), sub_self]
  rw [this]
  exact sum_mem fun x hx ↦ (le_iSup₂_of_le (f := fun x (_ : x ∈ S) ↦ W x) x hx le_rfl)
    ⟨_, ⟨(a : P → K) x, ha x, rfl⟩, rfl⟩

end DecidableEq

variable (hadm : ∀ x, Admissible K (Subalgebra.toSubmodule (O x)))
include hadm

lemma admissible_integralPart : Admissible K (integralPart O hfin) := fun f ↦ by
  classical
  have hl := isLift_piLift O hfin hadm (hfin f).toFinset f (fun x hx ↦ by simpa using hx)
  simpa using hl.1.toE.sub hl.2.toE

/-- The residue of the integral part of the restricted product is the sum of the local
residues. -/
theorem res_integralPart_smul_D (f g : K) (S : Finset P) (hf : ∀ x ∉ S, f ∈ O x)
    (hg : ∀ x ∉ S, g ∈ O x) :
    res K (integralPart O hfin) (f • D k K g) = ∑ x ∈ S, localRes (O x) (f • D k K g) := by
  classical
  have hA := admissible_integralPart O hfin hadm
  rw [res_smul_D hA (isLift_piLift O hfin hadm S f hf) (isLift_piLift O hfin hadm S g hg)]
  set X : P → Module.End k K := fun x ↦
    projO O x * act k f * (projO O x * act k g) - projO O x * act k g * (projO O x * act k f)
  have hX : ∀ x, E₁ (Subalgebra.toSubmodule (O x)) (X x) ∧
      E₂ (Subalgebra.toSubmodule (O x)) (X x) := fun x ↦
    (isLift_proj_mul (hadm x) (proj_mem _) (fun _ ↦ proj_apply_of_mem) f).commutator_mem
      (hadm x) (isLift_proj_mul (hadm x) (proj_mem _) (fun _ ↦ proj_apply_of_mem) g)
  set T : P → Module.End k 𝔸 := fun x ↦ single O hfin x ∘ₗ X x ∘ₗ evalAt O hfin x
  have hcomm : piLift O hfin S f hf * piLift O hfin S g hg -
      piLift O hfin S g hg * piLift O hfin S f hf = ∑ x ∈ S, T x := by
    ext v y
    rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [T, comp_apply, coe_single, evalAt_apply, Finset.sum_pi_single]
    rw [LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, mul_apply, mul_apply,
      piLift_apply, piLift_apply, piLift_apply, piLift_apply]
    split_ifs with hy
    · rfl
    · have h1 : projO O y (g * projO O y ((v : P → K) y)) = g * projO O y ((v : P → K) y) :=
        projO_apply_of_mem O ((O y).mul_mem (hg y hy) (projO_mem O y _))
      have h2 : projO O y (f * projO O y ((v : P → K) y)) = f * projO O y ((v : P → K) y) :=
        projO_apply_of_mem O ((O y).mul_mem (hf y hy) (projO_mem O y _))
      rw [h1, h2, mul_left_comm, sub_self]
  have hTself : ∀ x (v : 𝔸), (T x * T x) v = single O hfin x ((X x * X x) ((v : P → K) x)) := by
    intro x v
    simp only [T, mul_apply, comp_apply, evalAt_single_self]
    rfl
  have hTT : ∀ x y, (range (T x * T y)).FG := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      refine ((fg_range_mul (hX x).2 (hX x).1).map (single O hfin x)).of_le ?_
      rintro _ ⟨v, rfl⟩
      exact ⟨(X x * X x) ((v : P → K) x), ⟨(v : P → K) x, rfl⟩, (hTself x v).symm⟩
    · have : T x * T y = 0 := by
        ext v
        simp [T, mul_apply, evalAt_single_of_ne O hfin hxy]
      rw [this, range_zero]
      exact fg_bot
  rw [hcomm, tateTrace_sum S T fun x _ y _ ↦ hTT x y]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [localRes, res_smul_D_proj (hadm x) (proj_mem _) (fun _ ↦ proj_apply_of_mem)]
  change tateTrace (single O hfin x ∘ₗ (X x ∘ₗ evalAt O hfin x)) = (X x).tateTrace
  have hes : evalAt O hfin x ∘ₗ single O hfin x = LinearMap.id := by
    ext c
    simp
  rw [tateTrace_comp_comm _ _ ⟨2, by rw [sq]; exact hTT x x⟩, comp_assoc, hes, comp_id]


/-- The residue of the integral part of the restricted product vanishes. -/
theorem res_integralPart_eq_zero (hH0 : Module.Finite k (⨅ x, O x : Subalgebra k K))
    (hH1 : Module.Finite k
      ((Π₀ x, K ⧸ Subalgebra.toSubmodule (O x)) ⧸ range (principalParts O hfin))) :
    res K (integralPart O hfin) = 0 := by
  classical
  set A := integralPart O hfin
  set B := range (diag O hfin)
  have hBst : ∀ f : K, ∀ b ∈ B, f • b ∈ B := by
    rintro f _ ⟨g, rfl⟩
    exact ⟨f * g, (diag_smul O hfin f g).symm⟩
  have hB : Admissible K B := fun f ↦ AlmostLE.of_le (by
    rintro _ ⟨b, hb, rfl⟩
    exact hBst f b hb)
  have hA := admissible_integralPart O hfin hadm
  -- `A ∩ B` is finite-dimensional
  have hinf : (A ⊓ B).FG := by
    have : (Subalgebra.toSubmodule (⨅ x, O x)).FG :=
      Module.Finite.iff_fg.mp (Module.Finite.equiv (Subalgebra.toSubmoduleEquiv _).symm)
    refine (this.map (diag O hfin)).of_le ?_
    rintro v ⟨hvA, f, rfl⟩
    exact ⟨f, Algebra.mem_iInf.2 fun x ↦ hvA x, rfl⟩
  -- `V / (A + B)` is finite-dimensional
  have hsup : (⊤ : Submodule k 𝔸).AlmostLE (A ⊔ B) := by
    let ppV : 𝔸 →ₗ[k] Π₀ x, K ⧸ Subalgebra.toSubmodule (O x) :=
      { toFun v := toDFinsupp O (v : P → K) v.2
        map_add' v w := by ext x; simp [toDFinsupp_apply]
        map_smul' c v := by ext x; simp [toDFinsupp_apply] }
    have hppV : ∀ v x, ppV v x = Submodule.Quotient.mk ((v : P → K) x) := fun v x ↦
      toDFinsupp_apply O _ _ x
    set comp := (range (principalParts O hfin)).mkQ ∘ₗ ppV
    have hfg : ((⊤ : Submodule k 𝔸).map comp).FG := (Module.Finite.fg_top).of_le le_top
    obtain ⟨W, hW, hle⟩ := exists_fg_le_ker_sup comp hfg
    refine ⟨W, hW, hle.trans (sup_le_sup_right ?_ W)⟩
    intro v hv
    rw [mem_ker, comp_apply, mkQ_apply, Submodule.Quotient.mk_eq_zero] at hv
    obtain ⟨f, hf⟩ := hv
    have hvf : v - diag O hfin f ∈ A := by
      intro x
      have := congr($hf x)
      rw [principalParts_apply, hppV, eq_comm, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
    rw [show v = (v - diag O hfin f) + diag O hfin f by abel]
    exact add_mem_sup hvf ⟨f, rfl⟩
  have h3 := res_sup_add_res_inf hA hB
  rw [res_eq_zero_of_top_almostLE hsup, res_eq_zero_of_fg hinf,
    res_eq_zero_of_forall_smul_mem hBst, add_zero, add_zero] at h3
  exact h3.symm

end RestrictedProduct

/-- **Tate's abstract residue theorem.** Let `(O x)_{x ∈ P}` be `k`-subalgebras of `K` with
`f O_x ~ O_x` for all `f, x`, such that every `f ∈ K` lies in almost all `O_x`, `⋂_x O_x` is
finite-dimensional and the cokernel of `K → ⊕_x K / O_x` is finite-dimensional. Then for every
`η ∈ Ω[K⁄k]`, `res_{O_x} η = 0` for almost all `x` and `∑_x res_{O_x} η = 0`
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
theorem residue_theorem (hadm : ∀ x, Admissible K (Subalgebra.toSubmodule (O x)))
    (hH0 : Module.Finite k (⨅ x, O x : Subalgebra k K))
    (hH1 : Module.Finite k
      ((Π₀ x, K ⧸ Subalgebra.toSubmodule (O x)) ⧸ range (principalParts O hfin)))
    (η : Ω[K⁄k]) :
    (Function.support fun x ↦ localRes (O x) η).Finite ∧ ∑ᶠ x, localRes (O x) η = 0 := by
  classical
  have key : ∀ f g : K, (Function.support fun x ↦ localRes (O x) (f • D k K g)).Finite ∧
      ∑ᶠ x, localRes (O x) (f • D k K g) = 0 := by
    intro f g
    set S := ((hfin f).union (hfin g)).toFinset
    have hf : ∀ x ∉ S, f ∈ O x := fun x hx ↦ by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or,
        not_not] at hx
      exact hx.1
    have hg : ∀ x ∉ S, g ∈ O x := fun x hx ↦ by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or,
        not_not] at hx
      exact hx.2
    have hsupp : (Function.support fun x ↦ localRes (O x) (f • D k K g)) ⊆ S := by
      intro x hx
      by_contra h
      exact hx (localRes_smul_D_eq_zero (hf x h) (hg x h))
    refine ⟨S.finite_toSet.subset hsupp, ?_⟩
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      ← res_integralPart_smul_D O hfin hadm f g S hf hg,
      res_integralPart_eq_zero O hfin hadm hH0 hH1, LinearMap.zero_apply]
  have hη : η ∈ span k (Set.range fun p : K × K ↦ p.1 • D k K p.2) := by
    rw [span_range_smul_D]; trivial
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨f, g⟩, rfl⟩ := hx
    exact key f g
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨(hx.1.union hy.1).subset ?_, ?_⟩
    · intro z hz
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hz (by change localRes (O z) (x + y) = 0; rw [map_add, h.1, h.2, add_zero])
    · simp only [map_add]
      rw [finsum_add_distrib hx.1 hy.1, hx.2, hy.2, add_zero]
  | smul c x _ hx =>
    refine ⟨hx.1.subset ?_, ?_⟩
    · intro z hz h
      exact hz (by
        change localRes (O z) (c • x) = 0
        rw [map_smul, show localRes (O z) x = 0 from h, smul_zero])
    · simp only [map_smul, smul_eq_mul]
      rw [← mul_finsum' _ c hx.1, hx.2, mul_zero]

end TateResidue
