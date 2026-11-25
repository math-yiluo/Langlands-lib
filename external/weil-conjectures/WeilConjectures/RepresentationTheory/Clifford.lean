/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Geometric constituents after a finite-index extension

Let `ρ` be a finite-dimensional representation over an algebraically closed field `k` of a group
`W`, let `Π ⊴ W` be a normal subgroup and `F ∈ W`. In the application `W` is the Weil group of
a geometrically connected scheme `X₀` over a finite field, `Π = π₁(X̄)` is the geometric
fundamental group and `F` is a Frobenius lift, so that `Π` and `Fᵐ` generate the Weil group of
`X₀` after a constant extension of degree `m`.

After passing from `F` to a power `Fᵐ`, the representation has a finite filtration by subspaces
stable under `Π` and `Fᵐ` whose successive quotients are irreducible under `Π` alone. This is
Clifford theory: `Fᵐ` eventually fixes the `Π`-isotypic components of a quotient, and an
eigenvector of the operator induced by `Fᵐ` on the multiplicity space of an isotypic component
gives a `Π`-irreducible subspace stable under `Fᵐ`.

## Main statements

- `Representation.exists_filtration_isIrreducible_restrict`: blueprint
  `lemma-geometric-constituents-after-constant-extension--1`.
-/

@[expose] public section

section Twisted

/-! ### Operators twisting a module structure

Throughout, `Θ` is a `k`-linear operator on an `R`-module `M` which twists the `R`-action:
`Θ (a • m) = b • Θ m` for some `b` depending only on `a` (and conversely). -/

variable {k R M : Type*} [Field k] [Ring R] [AddCommGroup M] [Module R M] [Module k M]

/-- The image of an `R`-submodule under a `k`-linear map `Θ` such that every `a • Θ m` is of
the form `Θ (b • m)` for some `b` depending only on `a`. -/
def Submodule.twistedMap (Θ : M →ₗ[k] M) (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m)
    (N : Submodule R M) : Submodule R M where
  carrier := Θ '' N
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, N.add_mem hx hy, map_add ..⟩
  zero_mem' := ⟨0, N.zero_mem, map_zero _⟩
  smul_mem' a := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := h a
    exact ⟨b • x, N.smul_mem b hx, hb x⟩

theorem Submodule.mem_twistedMap {Θ : M →ₗ[k] M}
    {h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m} {N : Submodule R M} {x : M} :
    x ∈ N.twistedMap Θ h ↔ ∃ y ∈ N, Θ y = x :=
  Iff.rfl

/-- The preimage of an `R`-submodule under a `k`-linear map `Θ` such that every `Θ (a • m)` is
of the form `b • Θ m` for some `b` depending only on `a`. -/
def Submodule.twistedComap (Θ : M →ₗ[k] M) (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (N : Submodule R M) : Submodule R M where
  carrier := Θ ⁻¹' N
  add_mem' {x y} hx hy := by
    simpa using N.add_mem hx hy
  zero_mem' := by simp
  smul_mem' a x hx := by
    obtain ⟨b, hb⟩ := h a
    simpa [hb] using N.smul_mem b hx

/-- Powers of an operator twisting the `R`-action again twist the `R`-action. -/
theorem Module.End.exists_pow_smul_eq (Θ : Module.End k M)
    (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m) (n : ℕ) :
    ∀ a : R, ∃ b : R, ∀ m : M, (Θ ^ n) (a • m) = b • (Θ ^ n) m := by
  induction n with
  | zero => exact fun a ↦ ⟨a, fun m ↦ rfl⟩
  | succ n ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, fun m ↦ by rw [pow_succ', Module.End.mul_apply, hb, hc, Module.End.mul_apply]⟩

/-- Powers of an operator twisting the `R`-action again twist the `R`-action. -/
theorem Module.End.exists_pow_smul_eq' (Θ : Module.End k M)
    (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) (n : ℕ) :
    ∀ a : R, ∃ b : R, ∀ m : M, (Θ ^ n) (b • m) = a • (Θ ^ n) m := by
  induction n with
  | zero => exact fun a ↦ ⟨a, fun m ↦ rfl⟩
  | succ n ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, fun m ↦ by rw [pow_succ, Module.End.mul_apply, hc, hb, Module.End.mul_apply]⟩

/-- A bijective operator twisting the `R`-action maps simple submodules to simple submodules. -/
theorem Submodule.isSimpleModule_twistedMap {Θ : M →ₗ[k] M} (hΘ : Function.Bijective Θ)
    (h₁ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (h₂ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) (N : Submodule R M)
    [IsSimpleModule R N] : IsSimpleModule R (N.twistedMap Θ h₂) := by
  rw [isSimpleModule_iff_isAtom] at *
  refine ⟨fun hbot ↦ ?_, fun U hU ↦ ?_⟩
  · obtain ⟨x, hx, hx0⟩ := N.exists_mem_ne_zero_of_ne_bot ‹IsAtom N›.1
    have : Θ x ∈ N.twistedMap Θ h₂ := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot, map_eq_zero_iff Θ hΘ.1] at this
    exact hx0 this
  · have hle : U.twistedComap Θ h₁ ≤ N := fun x hx ↦ by
      obtain ⟨y, hy, hxy⟩ := hU.le hx
      rwa [← hΘ.1 hxy]
    have hne : U.twistedComap Θ h₁ ≠ N := fun heq ↦ hU.not_ge fun x hx ↦ by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← heq] at hy
      exact hy
    have hbot := ‹IsAtom N›.2 _ (lt_of_le_of_ne hle hne)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hΘ.2 x
    have : y ∈ U.twistedComap Θ h₁ := hx
    rw [hbot, Submodule.mem_bot] at this
    simp [this]

variable [Algebra k R] [IsScalarTower k R M]

/-- Eigenvector step of Clifford theory: if an injective operator `Ψ` twisting the `R`-action
maps a simple submodule `S` onto a submodule isomorphic to `S`, then some simple submodule is
stable under `Ψ`. -/
theorem Submodule.exists_isSimpleModule_apply_mem [IsAlgClosed k] [FiniteDimensional k M]
    {Ψ : M →ₗ[k] M} (hΨ : Function.Injective Ψ)
    (h : ∀ a : R, ∃ b : R, ∀ m : M, Ψ (b • m) = a • Ψ m) (S : Submodule R M)
    [IsSimpleModule R S] (e : S ≃ₗ[R] S.twistedMap Ψ h) :
    ∃ C : Submodule R M, IsSimpleModule R C ∧ ∀ x ∈ C, Ψ x ∈ C := by
  have hex (s : S) : ∃ y ∈ S, Ψ y = e s := (e s).2
  choose ψ hψS hψ using hex
  have hadd (s t : S) : (⟨ψ (s + t), hψS _⟩ : S) = ⟨ψ s, hψS s⟩ + ⟨ψ t, hψS t⟩ :=
    Subtype.ext (hΨ (by simp [hψ]))
  have hsmul (a b : R) (hb : ∀ m : M, Ψ (b • m) = a • Ψ m) (s : S) :
      (⟨ψ (a • s), hψS _⟩ : S) = b • ⟨ψ s, hψS s⟩ :=
    Subtype.ext (hΨ (by simp [hψ, hb]))
  -- The operator `f ↦ Ψ ∘ f ∘ Ψ⁻¹ ∘ e` on `Hom_R(S, M)`.
  let 𝒯 : (S →ₗ[R] M) →ₗ[k] (S →ₗ[R] M) :=
    { toFun f :=
        { toFun s := Ψ (f ⟨ψ s, hψS s⟩)
          map_add' s t := by rw [hadd, map_add, map_add]
          map_smul' a s := by
            obtain ⟨b, hb⟩ := h a
            rw [hsmul a b hb, map_smul, hb, RingHom.id_apply] }
      map_add' f g := by
        ext s
        simp
      map_smul' c f := by
        ext s
        simp }
  have : FiniteDimensional k S :=
    Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  let ι : (S →ₗ[R] M) →ₗ[k] (S →ₗ[k] M) :=
    { toFun f := f.restrictScalars k
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : FiniteDimensional k (S →ₗ[R] M) :=
    Module.Finite.of_injective ι (LinearMap.restrictScalars_injective k)
  have : Nontrivial (S →ₗ[R] M) := by
    have := IsSimpleModule.nontrivial R S
    refine nontrivial_of_ne S.subtype 0 fun h0 ↦ ?_
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    exact hx (Subtype.ext (LinearMap.congr_fun h0 x))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue 𝒯
  obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
  have hinj : Function.Injective f := f.injective_or_eq_zero.resolve_right hf.2
  refine ⟨LinearMap.range f, IsSimpleModule.congr (LinearEquiv.ofInjective f hinj).symm, ?_⟩
  rintro _ ⟨s', rfl⟩
  obtain ⟨s, hs⟩ := e.surjective ⟨Ψ s', s', s'.2, rfl⟩
  have hs' : (⟨ψ s, hψS s⟩ : S) = s' := Subtype.ext (hΨ (by rw [hψ, hs]))
  have h1 : Ψ (f ⟨ψ s, hψS s⟩) = c • f s := LinearMap.congr_fun hf.apply_eq_smul s
  rw [hs'] at h1
  rw [h1]
  exact (LinearMap.range f).smul_of_tower_mem c (LinearMap.mem_range_self f s)

/-- **Clifford theory, key step.** If a bijective `k`-linear operator `Θ` on a nonzero
finite-dimensional module twists the `R`-action in both directions, then some simple
submodule is stable under a positive power of `Θ`. -/
theorem Submodule.exists_isSimpleModule_pow_apply_mem [IsAlgClosed k] [FiniteDimensional k M]
    [Nontrivial M] {Θ : Module.End k M} (hΘ : Function.Bijective Θ)
    (h₁ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (h₂ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) :
    ∃ j, 0 < j ∧ ∃ C : Submodule R M, IsSimpleModule R C ∧ ∀ x ∈ C, (Θ ^ j) x ∈ C := by
  have : IsArtinian R M := isArtinian_of_tower k inferInstance
  have : IsNoetherian R M := isNoetherian_of_tower k inferInstance
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
  have : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  have hbij (n : ℕ) : Function.Bijective ⇑(Θ ^ n) := by
    rw [Module.End.coe_pow]
    exact hΘ.iterate n
  let T (n : ℕ) := S.twistedMap (Θ ^ n) (Θ.exists_pow_smul_eq' h₂ n)
  have hT (n : ℕ) : IsSimpleModule R (T n) :=
    S.isSimpleModule_twistedMap (hbij n) (Θ.exists_pow_smul_eq h₁ n) _
  -- Pigeonhole: `Θ` permutes the finitely many isotypic components.
  let g (n : ℕ) : isotypicComponents R M := ⟨isotypicComponent R M (T n), T n, hT n, rfl⟩
  obtain ⟨a, b, hab, hg⟩ : ∃ a b, a < b ∧ g a = g b := by
    obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite g
    rcases hne.lt_or_gt with h' | h'
    · exact ⟨a, b, h', h⟩
    · exact ⟨b, a, h', h.symm⟩
  have hle : T b ≤ isotypicComponent R M (T a) := by
    have hg' : isotypicComponent R M (T a) = isotypicComponent R M (T b) :=
      congrArg Subtype.val hg
    rw [hg']
    exact (T b).le_isotypicComponent
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M (T a)) (T b) hle
  have hTb : T b = (T a).twistedMap (Θ ^ (b - a)) (Θ.exists_pow_smul_eq' h₂ _) := by
    ext x
    simp only [T, Submodule.mem_twistedMap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(Θ ^ a) y, ⟨y, hy, rfl⟩, by rw [← Module.End.mul_apply, pow_sub_mul_pow Θ hab.le]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by rw [← Module.End.mul_apply, pow_sub_mul_pow Θ hab.le]⟩
  obtain ⟨C, hC, hCΘ⟩ := (T a).exists_isSimpleModule_apply_mem (hbij _).1 _
    (e.symm.trans (LinearEquiv.ofEq _ _ hTb))
  exact ⟨b - a, Nat.sub_pos_of_lt hab, C, hC, hCΘ⟩

/-- **Clifford theory, relative step.** Let `Θ` be a bijective `k`-linear operator on a
finite-dimensional module twisting the `R`-action in both directions, and `A ≠ ⊤` a
`Θ`-stable submodule. Then there is a submodule `C` covering `A` which is stable under a
positive power of `Θ`. -/
theorem Submodule.exists_covBy_pow_apply_mem [IsAlgClosed k] [FiniteDimensional k M]
    {Θ : Module.End k M} (hΘ : Function.Bijective Θ)
    (h₁ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (h₂ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) {A : Submodule R M} (hA : A ≠ ⊤)
    (hAΘ : ∀ x ∈ A, Θ x ∈ A) :
    ∃ j, 0 < j ∧ ∃ C : Submodule R M, A < C ∧
      (∀ D : Submodule R M, A ≤ D → D ≤ C → D = A ∨ D = C) ∧ ∀ x ∈ C, (Θ ^ j) x ∈ C := by
  have : FiniteDimensional k (M ⧸ A) :=
    Module.Finite.of_surjective (A.mkQ.restrictScalars k) A.mkQ_surjective
  have : Nontrivial (M ⧸ A) := Submodule.Quotient.nontrivial_iff.mpr hA
  let e := Submodule.Quotient.restrictScalarsEquiv k A
  -- The operator induced by `Θ` on `M ⧸ A`.
  let ΘQ : Module.End k (M ⧸ A) := e.toLinearMap ∘ₗ
    (A.restrictScalars k).mapQ (A.restrictScalars k) Θ hAΘ ∘ₗ e.symm.toLinearMap
  have hmk (x : M) : ΘQ (A.mkQ x) = A.mkQ (Θ x) := rfl
  have hmkpow (n : ℕ) (x : M) : (ΘQ ^ n) (A.mkQ x) = A.mkQ ((Θ ^ n) x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hmk, ← Module.End.mul_apply, pow_succ']
  have hsurj : Function.Surjective ΘQ := by
    intro q
    obtain ⟨x, rfl⟩ := A.mkQ_surjective q
    obtain ⟨y, rfl⟩ := hΘ.2 x
    exact ⟨A.mkQ y, hmk y⟩
  have hbij : Function.Bijective ΘQ := ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩
  have h₁Q (a : R) : ∃ b : R, ∀ q : M ⧸ A, ΘQ (a • q) = b • ΘQ q := by
    obtain ⟨b, hb⟩ := h₁ a
    refine ⟨b, fun q ↦ ?_⟩
    obtain ⟨x, rfl⟩ := A.mkQ_surjective q
    rw [← map_smul, hmk, hmk, hb, map_smul]
  have h₂Q (a : R) : ∃ b : R, ∀ q : M ⧸ A, ΘQ (b • q) = a • ΘQ q := by
    obtain ⟨b, hb⟩ := h₂ a
    refine ⟨b, fun q ↦ ?_⟩
    obtain ⟨x, rfl⟩ := A.mkQ_surjective q
    rw [← map_smul, hmk, hmk, hb, map_smul]
  obtain ⟨j, hj, C, hC, hCΘ⟩ := Submodule.exists_isSimpleModule_pow_apply_mem hbij h₁Q h₂Q
  have hCat := isSimpleModule_iff_isAtom.mp hC
  refine ⟨j, hj, C.comap A.mkQ, lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ hCat.1 ?_,
    fun D hAD hDC ↦ ?_, fun x hx ↦ ?_⟩
  · rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).mpr hx]
    exact C.zero_mem
  · rw [← Submodule.map_comap_eq_of_surjective A.mkQ_surjective C, ← h, Submodule.mkQ_map_self]
  · have hD : D = (D.map A.mkQ).comap A.mkQ := by
      rw [Submodule.comap_map_mkQ, sup_of_le_right hAD]
    rcases (hCat.le_iff.mp (Submodule.map_le_iff_le_comap.mpr hDC)) with h | h
    · rw [h, Submodule.comap_bot, Submodule.ker_mkQ] at hD
      exact Or.inl hD
    · rw [h] at hD
      exact Or.inr hD
  · rw [Submodule.mem_comap, ← hmkpow]
    exact hCΘ _ hx

/-- **Clifford theory, filtration.** Let `Θ` be a bijective `k`-linear operator on a
finite-dimensional module twisting the `R`-action in both directions, and `A` a submodule
stable under `Θ ^ m₀`. Then for some positive multiple `m` of `m₀` there is a chain of
submodules from `A` to `⊤` with covering steps, all stable under `Θ ^ m`. -/
theorem Submodule.exists_chain_covBy_pow_apply_mem [IsAlgClosed k] [FiniteDimensional k M]
    {Θ : Module.End k M} (hΘ : Function.Bijective Θ)
    (h₁ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (h₂ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) (A : Submodule R M) {m₀ : ℕ}
    (hm₀ : 0 < m₀) (hA : ∀ x ∈ A, (Θ ^ m₀) x ∈ A) :
    ∃ m, 0 < m ∧ m₀ ∣ m ∧ ∃ (n : ℕ) (U : Fin (n + 1) → Submodule R M),
      U 0 = A ∧ U (Fin.last n) = ⊤ ∧ (∀ i, ∀ x ∈ U i, (Θ ^ m) x ∈ U i) ∧
      ∀ i : Fin n, U i.castSucc < U i.succ ∧
        ∀ D : Submodule R M, U i.castSucc ≤ D → D ≤ U i.succ →
          D = U i.castSucc ∨ D = U i.succ := by
  have : IsNoetherian R M := isNoetherian_of_tower k inferInstance
  induction A using WellFoundedGT.induction generalizing m₀ with
  | ind A ih =>
  by_cases hAtop : A = ⊤
  · exact ⟨m₀, hm₀, dvd_rfl, 0, fun _ ↦ A, rfl, hAtop, fun _ ↦ hA, fun i ↦ i.elim0⟩
  have hbij : Function.Bijective ⇑(Θ ^ m₀) := by
    rw [Module.End.coe_pow]
    exact hΘ.iterate m₀
  obtain ⟨j, hj, C, hAC, hcov, hC⟩ := Submodule.exists_covBy_pow_apply_mem hbij
    (Θ.exists_pow_smul_eq h₁ m₀) (Θ.exists_pow_smul_eq' h₂ m₀) hAtop hA
  rw [← pow_mul] at hC
  obtain ⟨m, hm, hdvd, n, U, hU0, hUlast, hUΘ, hUstep⟩ := ih C hAC (Nat.mul_pos hm₀ hj) hC
  obtain ⟨c, rfl⟩ := (dvd_mul_right m₀ j).trans hdvd
  refine ⟨m₀ * c, hm, dvd_mul_right m₀ c, n + 1, Fin.cons A U, rfl, ?_, fun i ↦ ?_,
    fun i ↦ ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ, hUlast]
  · refine Fin.cases ?_ (fun i ↦ ?_) i
    · rw [Fin.cons_zero, pow_mul]
      exact Module.End.pow_apply_mem_of_forall_mem (p := A.restrictScalars k) c hA
    · rw [Fin.cons_succ]
      exact hUΘ i
  · refine Fin.cases ?_ (fun i ↦ ?_) i
    · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hU0]
      exact ⟨hAC, hcov⟩
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hUstep i


end Twisted

namespace Representation

section Adjoin

variable {k W V : Type*} [Field k] [Group W] [AddCommGroup V] [Module k V]

/-- Conjugation by `ρ w` preserves the subalgebra generated by the image of a normal
subgroup. -/
theorem conj_mem_adjoin_image (ρ : Representation k W V) (P : Subgroup W) [P.Normal] (w : W)
    {a : Module.End k V} (ha : a ∈ Algebra.adjoin k (ρ '' P)) :
    ρ w * a * ρ w⁻¹ ∈ Algebra.adjoin k (ρ '' P) := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← map_mul, ← map_mul]
    exact Algebra.subset_adjoin ⟨_, ‹P.Normal›.conj_mem g hg w, rfl⟩
  | algebraMap c =>
    rw [← Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    exact Subalgebra.algebraMap_mem _ c
  | add x y _ _ hx hy =>
    rw [mul_add, add_mul]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have : ρ w * (x * y) * ρ w⁻¹ = ρ w * x * ρ w⁻¹ * (ρ w * y * ρ w⁻¹) := by
      simp only [mul_assoc]
      rw [← mul_assoc (ρ w⁻¹) (ρ w), ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [this]
    exact mul_mem hx hy

/-- A subspace stable under `ρ g` for all `g ∈ P` is stable under every element of the
subalgebra generated by `ρ '' P`. -/
theorem le_comap_of_mem_adjoin_image (ρ : Representation k W V) (P : Subgroup W)
    {Q : Submodule k V} (hQ : ∀ g ∈ P, Q ≤ Q.comap (ρ g)) {a : Module.End k V}
    (ha : a ∈ Algebra.adjoin k (ρ '' P)) : Q ≤ Q.comap a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hQ g hg
  | algebraMap c =>
    intro x hx
    rw [Submodule.mem_comap, Module.algebraMap_end_apply]
    exact Q.smul_mem c hx
  | add x y _ _ hx hy => exact fun v hv ↦ Q.add_mem (hx hv) (hy hv)
  | mul x y _ _ hx hy => exact fun v hv ↦ hx (hy hv)

/-- `ρ w` twists the action of the subalgebra generated by the image of a normal subgroup. -/
theorem exists_smul_eq_adjoin_image (ρ : Representation k W V) (P : Subgroup W) [P.Normal]
    (w : W) (a : Algebra.adjoin k (ρ '' P)) :
    ∃ b : Algebra.adjoin k (ρ '' P), ∀ v : V, ρ w (a • v) = b • ρ w v :=
  ⟨⟨ρ w * a * ρ w⁻¹, ρ.conj_mem_adjoin_image P w a.2⟩, fun v ↦ by
    simp [Subalgebra.smul_def]⟩


/-- `ρ w` twists the action of the subalgebra generated by the image of a normal subgroup. -/
theorem exists_smul_eq_adjoin_image' (ρ : Representation k W V) (P : Subgroup W) [P.Normal]
    (w : W) (a : Algebra.adjoin k (ρ '' P)) :
    ∃ b : Algebra.adjoin k (ρ '' P), ∀ v : V, ρ w (b • v) = a • ρ w v :=
  ⟨⟨ρ w⁻¹ * a * ρ w⁻¹⁻¹, ρ.conj_mem_adjoin_image P w⁻¹ a.2⟩, fun v ↦ by
    simp [Subalgebra.smul_def]⟩

end Adjoin

variable {k W V : Type*} [Field k] [IsAlgClosed k] [Group W] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **Geometric constituents after a constant extension**
(blueprint: `lemma-geometric-constituents-after-constant-extension--1`). Let `ρ` be a
finite-dimensional representation of `W` over an algebraically closed field, `P` a normal subgroup
of `W` and `F ∈ W`. There are `m ≥ 1` and a finite chain of subspaces `0 = U₀ < U₁ < ⋯ < Uₙ = V`,
each stable under `P` and under `ρ (F ^ m)`, such that every successive quotient `Uᵢ₊₁ / Uᵢ` is
irreducible under `P`: no `P`-stable subspace lies strictly between `Uᵢ` and `Uᵢ₊₁`. -/
theorem exists_filtration_isIrreducible_restrict (ρ : Representation k W V) (P : Subgroup W)
    [P.Normal] (F : W) :
    ∃ m : ℕ, 0 < m ∧ ∃ (n : ℕ) (U : Fin (n + 1) → Submodule k V),
      U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      (∀ i, ∀ g ∈ P, U i ≤ (U i).comap (ρ g)) ∧ (∀ i, U i ≤ (U i).comap (ρ (F ^ m))) ∧
      ∀ i : Fin n, U i.castSucc < U i.succ ∧
        ∀ Q : Submodule k V, (∀ g ∈ P, Q ≤ Q.comap (ρ g)) → U i.castSucc ≤ Q → Q ≤ U i.succ →
          Q = U i.castSucc ∨ Q = U i.succ := by
  have hbij : Function.Bijective (ρ F) :=
    Function.bijective_iff_has_inverse.mpr ⟨ρ F⁻¹, ρ.inv_self_apply F, ρ.self_inv_apply F⟩
  obtain ⟨m, hm, -, n, U, hU0, hUlast, hUF, hUstep⟩ :=
    Submodule.exists_chain_covBy_pow_apply_mem hbij (ρ.exists_smul_eq_adjoin_image P F)
      (ρ.exists_smul_eq_adjoin_image' P F) ⊥ one_pos (by simp)
  let ι := Submodule.restrictScalarsEmbedding k (Algebra.adjoin k (ρ '' P)) V
  refine ⟨m, hm, n, fun i ↦ ι (U i), by simp [ι, hU0], by simp [ι, hUlast],
    fun i g hg x hx ↦ (U i).smul_mem ⟨ρ g, Algebra.subset_adjoin ⟨g, hg, rfl⟩⟩ hx,
    fun i x hx ↦ ?_, fun i ↦ ⟨ι.lt_iff_lt.mpr (hUstep i).1, fun Q hQ hQ₁ hQ₂ ↦ ?_⟩⟩
  · rw [Submodule.mem_comap, map_pow]
    exact hUF i x hx
  · let Q' : Submodule (Algebra.adjoin k (ρ '' P)) V :=
      { Q.toAddSubmonoid with
        smul_mem' a _ hx := ρ.le_comap_of_mem_adjoin_image P hQ a.2 hx }
    have hQQ' : Q = ι Q' := rfl
    rw [hQQ'] at hQ₁ hQ₂ ⊢
    rcases (hUstep i).2 Q' (ι.le_iff_le.mp hQ₁) (ι.le_iff_le.mp hQ₂) with h | h
    · exact Or.inl (congrArg ι h)
    · exact Or.inr (congrArg ι h)


end Representation
