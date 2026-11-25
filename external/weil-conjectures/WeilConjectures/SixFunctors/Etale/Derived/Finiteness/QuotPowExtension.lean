/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowHigherDirectImage

/-!
# Extensions of finite locally constant sheaves killed by an ideal of finite index

This file collects the ingredients of the uniform finite local constancy of the tower
`n ↦ Hᵏ(Rg_* (Λ ⧸ Iⁿ)_T)` over a ring `Λ` which need not be finite (the case `Λ = 𝒪_E`):

- `CategoryTheory.ObjectProperty.prop_of_exact_five_of_mid`: a variant of
  `CategoryTheory.ObjectProperty.prop_of_exact_five` where the extension property is only known
  for extensions whose middle term satisfies an auxiliary condition, satisfied by the middle
  term of the five-term exact sequence;
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact_of_smul_eq_zero`: for
  `Λ ⧸ J` finite, an extension of finite locally constant sheaves of `Λ`-modules which is killed
  by `J` is finite locally constant;
- `DerivedCategory.quotPowSuccShortComplex_shortExact`: for `I = (ϖ)` with `ϖ` a nonzerodivisor,
  the short exact sequence `0 ⟶ Λ ⧸ I ⟶ Λ ⧸ Iⁿ⁺¹ ⟶ Λ ⧸ Iⁿ ⟶ 0`, the first map being the
  multiplication by `ϖⁿ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)

/-- **The middle term of a five-term exact sequence**, with a restricted extension property. Let
`P` be a property of objects of an abelian category closed under kernels and cokernels, and
closed under extensions whose middle term satisfies `Q`. For an exact sequence
`C₀ ⟶ A ⟶ B ⟶ C ⟶ A₁` whose outer four terms satisfy `P` and with `Q B`, the middle term `B`
satisfies `P`. -/
lemma prop_of_exact_five_of_mid (Q : C → Prop)
    (hker : ∀ {X Y : C} (φ : X ⟶ Y), P X → P Y → P (kernel φ))
    (hcoker : ∀ {X Y : C} (φ : X ⟶ Y), P X → P Y → P (cokernel φ))
    (hext : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₁ → P S.X₃ → Q S.X₂ → P S.X₂)
    {C₀ A B C' A₁ : C} (δ₀ : C₀ ⟶ A) (f : A ⟶ B) (g : B ⟶ C') (δ : C' ⟶ A₁)
    (w₀ : δ₀ ≫ f = 0) (w₁ : f ≫ g = 0) (w₂ : g ≫ δ = 0)
    (h₀ : (ShortComplex.mk δ₀ f w₀).Exact) (h₁ : (ShortComplex.mk f g w₁).Exact)
    (h₂ : (ShortComplex.mk g δ w₂).Exact)
    (hC₀ : P C₀) (hA : P A) (hC : P C') (hA₁ : P A₁) (hB : Q B) : P B := by
  let i : cokernel δ₀ ⟶ B := cokernel.desc δ₀ f w₀
  let p : B ⟶ kernel δ := kernel.lift δ g w₂
  have hip : i ≫ p = 0 := by
    ext
    simp [i, p, w₁]
  have : Mono i := h₀.mono_cokernelDesc
  have : Epi p := h₂.epi_kernelLift
  let S₁ := ShortComplex.mk f p (by ext; simp [p, w₁])
  have hS₁ : S₁.Exact := by
    let φ : S₁ ⟶ ShortComplex.mk f g w₁ :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι δ, comm₂₃ := by simp [S₁, p] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h₁
  let S := ShortComplex.mk i p hip
  have hS : S.ShortExact := by
    refine ⟨?_⟩
    let φ : S₁ ⟶ S :=
      { τ₁ := cokernel.π δ₀, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [S₁, S, i] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS₁
  exact hext hS (hcoker δ₀ hC₀ hA) (hker δ hC hA₁) hB

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ) {X : Scheme.{u}}

/-- **Extensions of finite locally constant sheaves killed by an ideal of finite index.** Let `J`
be an ideal of `Λ` with `Λ ⧸ J` finite and `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of
sheaves of `Λ`-modules with `F₁`, `F₃` finite locally constant and `F₂` killed by `J`. Then `F₂`
is finite locally constant: the sequence is the restriction of scalars of a short exact sequence
of sheaves of `Λ ⧸ J`-modules, and the extension property holds over the finite ring `Λ ⧸ J`
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact`). -/
theorem IsFiniteLocallyConstantSheaf.of_shortExact_of_smul_eq_zero [Finite (Λ ⧸ J)]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (hJ : ∀ r ∈ J, r • 𝟙 S.X₂ = 0)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ := by
  have h₁ : ∀ r ∈ J, r • 𝟙 S.X₁ = 0 := fun r hr ↦ by
    have := hS.mono_f
    rw [← cancel_mono S.f, zero_comp]
    calc (r • 𝟙 S.X₁) ≫ S.f = S.f ≫ (r • 𝟙 S.X₂) := by simp
      _ = 0 := by rw [hJ r hr, comp_zero]
  have h₃ : ∀ r ∈ J, r • 𝟙 S.X₃ = 0 := fun r hr ↦ by
    have := hS.epi_g
    rw [← cancel_epi S.g, comp_zero]
    calc S.g ≫ (r • 𝟙 S.X₃) = (r • 𝟙 S.X₂) ≫ S.g := by simp
      _ = 0 := by rw [hJ r hr, zero_comp]
  let res := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)
  let S' := S.map (Sheaf.coextendScalars X.smallEtaleTopology J)
  let e : S'.map res ≅ S := ShortComplex.isoMk
    (Sheaf.restrictScalarsCoextendScalarsIso _ h₁) (Sheaf.restrictScalarsCoextendScalarsIso _ hJ)
    (Sheaf.restrictScalarsCoextendScalarsIso _ h₃)
    (Sheaf.restrictScalarsCoextendScalarsIso_hom_naturality S.f h₁ hJ)
    (Sheaf.restrictScalarsCoextendScalarsIso_hom_naturality S.g hJ h₃)
  have hS' : S'.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff res).1 (ShortComplex.shortExact_of_iso e.symm hS)
  have : IsFiniteLocallyConstantSheaf (res.obj S'.X₁) :=
    IsFiniteLocallyConstantSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso _ h₁).symm
  have : IsFiniteLocallyConstantSheaf (res.obj S'.X₃) :=
    IsFiniteLocallyConstantSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso _ h₃).symm
  have : IsFiniteLocallyConstantSheaf S'.X₁ := IsFiniteLocallyConstantSheaf.of_restrictScalars J _
  have : IsFiniteLocallyConstantSheaf S'.X₃ := IsFiniteLocallyConstantSheaf.of_restrictScalars J _
  have : IsFiniteLocallyConstantSheaf ((Sheaf.coextendScalars _ J).obj S.X₂) :=
    IsFiniteLocallyConstantSheaf.of_shortExact hS'
  have : IsFiniteLocallyConstantSheaf (res.obj ((Sheaf.coextendScalars _ J).obj S.X₂)) :=
    IsFiniteLocallyConstantSheaf.restrictScalars J _
  exact IsFiniteLocallyConstantSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso _ hJ)

end AlgebraicGeometry.Scheme

namespace DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ}

variable (I ϖ) in
/-- The short complex `Λ ⧸ I ⟶ Λ ⧸ Iⁿ⁺¹ ⟶ Λ ⧸ Iⁿ` of `Λ`-modules, the first map being the
multiplication by `ϖⁿ` (for `ϖ ∈ I`) and the second the projection. -/
noncomputable def quotPowSuccShortComplex (hϖ : ϖ ∈ I) (n : ℕ) :
    ShortComplex (ModuleCat.{u + 1} Λ) :=
  ShortComplex.mk (X₁ := (Ideal.quotPowFunctor I).obj (op 1))
    (ModuleCat.ofHom (Submodule.mapQ (I ^ 1) (I ^ (n + 1)) (ϖ ^ n • LinearMap.id) (by
      intro x hx
      rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖ n) (by simpa using hx))))
    ((Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op) (by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (ϖ ^ n • y) = 0
      rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ n))

/-- The sequence `0 ⟶ Λ ⧸ I ⟶ Λ ⧸ Iⁿ⁺¹ ⟶ Λ ⧸ Iⁿ ⟶ 0` is short exact for `I = (ϖ)`, `ϖ` a
nonzerodivisor. -/
lemma quotPowSuccShortComplex_shortExact (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (hI : I = Ideal.span {ϖ}) (n : ℕ) :
    (quotPowSuccShortComplex I ϖ (mem_of_eq_span hI) n).ShortExact := by
  subst hI
  refine ModuleCat.shortComplex_shortExact _ (fun y ↦ ?_) (fun x y h ↦ ?_) (fun y ↦ ?_)
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (p := Ideal.span {ϖ} ^ n) y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (ϖ ^ n • a) = _
      rw [smul_eq_mul, mul_comm]
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (ϖ ^ n • x) = Submodule.Quotient.mk y at hx
      rw [Submodule.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton',
        smul_eq_mul] at hx
      obtain ⟨z, hz⟩ := hx
      exact ⟨x - z * ϖ, by linear_combination -hz⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (ϖ ^ n • x) = Submodule.Quotient.mk (ϖ ^ n • y) at h
    rw [Submodule.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton',
      smul_eq_mul, smul_eq_mul] at h
    obtain ⟨z, hz⟩ := h
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, pow_one, Ideal.mem_span_singleton']
    refine ⟨z, ?_⟩
    have hp : ϖ ^ n ∈ nonZeroDivisors Λ := pow_mem hϖ n
    rw [← sub_eq_zero]
    refine (mem_nonZeroDivisors_iff.1 hp).2 _ ?_
    linear_combination hz
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end DerivedCategory
