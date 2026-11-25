/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Consecutive-quotient Tor and split universal coefficients

`levelTor I n M` is the degree `-1` homology of a projective resolution of an
`A/I^{n+2}`-module `M`, reduced to `A/I^{n+1}`. Over a principal ideal domain, a direct summand
of `H^q(P)` killed by `I^m` is a retract of `H^q(P ⊗ A/I^m)` for a complex `P` of finite
projective modules.

Source: Bhatt--Scholze, Proposition 6.6.11; step 5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Extension of scalars between rings of the same universe is additive. -/
instance extendScalars_additive_succ {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (extendScalars.{u + 1, u + 1, u + 1} f).Additive :=
  (extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).left_adjoint_additive

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ)

/-- The module-level consecutive-quotient Tor: the degree `-1` homology of a projective
resolution of an `A/I^{n+2}`-module, reduced to `A/I^{n+1}`. -/
def levelTor (M : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1 + 1))) :
    ModuleCat.{u + 1} (A ⧸ I ^ (n + 1)) :=
  (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.factorPowSucc I (n + 1))).mapHomologicalComplex (.up ℤ)).obj
      (projectiveResolution M).cochainComplex).homology (-1)


/-- If `I^m` kills `N₀`, the unit `N₀ → A/I^m ⊗ N₀` has a retraction. -/
theorem exists_unit_retraction (m : ℕ) (N₀ : ModuleCat.{u + 1} A)
    (hk : ∀ a ∈ I ^ m, ∀ x : N₀, a • x = 0) :
    ∃ μ : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk (I ^ m))).obj N₀) ⟶ N₀,
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (I ^ m))).unit.app N₀ ≫ μ = 𝟙 N₀ := by
  let f := Ideal.Quotient.mk (I ^ m)
  let L : A ⧸ I ^ m →+* Module.End A N₀ :=
    Ideal.Quotient.lift (I ^ m) (algebraMap A (Module.End A N₀)) (fun a ha ↦ by
      ext x
      simp [hk a ha x])
  let L' : (ModuleCat.restrictScalars f).obj (ModuleCat.of (A ⧸ I ^ m) (A ⧸ I ^ m)) →ₗ[A]
      Module.End A N₀ :=
    { toFun := fun s ↦ L s
      map_add' := fun s t ↦ L.map_add s t
      map_smul' := fun a s ↦ by
        change L (f a * (show A ⧸ I ^ m from s)) = algebraMap A (Module.End A N₀) a * L s
        rw [map_mul]
        rfl }
  let T := TensorProduct.lift L'
  let E := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj N₀
  have key (s : A ⧸ I ^ m) (t : E) : T (s • t) = L s (T t) := by
    refine TensorProduct.inductionOn t ?_ ?_
    · intro s' x
      rw [TensorProduct.smul_tmul']
      simp only [T, TensorProduct.lift.tmul]
      change L (s * (show A ⧸ I ^ m from s')) x = L s (L s' x)
      rw [map_mul]
      rfl
    · intro t₁ t₂ h₁ h₂
      rw [smul_add, map_add, map_add, h₁, h₂, map_add]
  refine ⟨ModuleCat.ofHom (X := (ModuleCat.restrictScalars f).obj E) (Y := N₀)
    { toFun := fun t ↦ T t
      map_add' := fun s t ↦ map_add T s t
      map_smul' := fun a t ↦ key (f a) t }, ?_⟩
  ext x
  change T ((1 : A ⧸ I ^ m) ⊗ₜ x) = x
  simp [T, L', L]

/-- Over a principal ideal domain, the cycles of a complex of finite projective modules are a
direct summand of each term. -/
theorem exists_cycles_retraction [IsDomain A] [IsPrincipalIdealRing A]
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) (q : ℤ) :
    ∃ ρ : P.X q ⟶ P.cycles q, P.iCycles q ≫ ρ = 𝟙 _ := by
  let d := (P.d q (q + 1)).hom
  have := (hP (q + 1)).1
  have := (hP (q + 1)).2
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  let τ : P.X q ⟶ P.X q := ModuleCat.ofHom (LinearMap.id - σ.comp d.rangeRestrict)
  have hdσ (y : LinearMap.range d) : d (σ y) = y := by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  have hτ : τ ≫ P.d q (q + 1) = 0 := by
    ext x
    change d (x - σ (d.rangeRestrict x)) = 0
    rw [map_sub, hdσ]
    simp
  refine ⟨P.liftCycles τ (q + 1) (by simp) hτ, ?_⟩
  rw [← cancel_mono (P.iCycles q), Category.assoc, HomologicalComplex.liftCycles_i,
    Category.id_comp]
  ext x
  change P.iCycles q x - σ (d.rangeRestrict (P.iCycles q x)) = P.iCycles q x
  have h0 : d.rangeRestrict (P.iCycles q x) = 0 := by
    apply Subtype.ext
    change (P.iCycles q ≫ P.d q (q + 1)) x = 0
    simp
  rw [h0, map_zero, sub_zero]


/-- Universal coefficients over a principal ideal domain, split form: a direct summand `N₀`
of `H^q(P)` killed by `I^m` is a retract of `H^q(P ⊗ A/I^m)`, for a bounded complex of
finite projective modules `P`. -/
theorem exists_homology_reduction_retraction [IsDomain A] [IsPrincipalIdealRing A] (m : ℕ)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) (q : ℤ)
    (F N₀ : ModuleCat.{u + 1} A) (ε : P.homology q ≅ F ⊞ N₀)
    (hk : ∀ a ∈ I ^ m, ∀ x : N₀, a • x = 0) :
    ∃ (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk (I ^ m))).mapHomologicalComplex (.up ℤ)).obj P).homology q))
      (r : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk (I ^ m))).mapHomologicalComplex (.up ℤ)).obj P).homology q) →ₗ[A]
          N₀), ∀ x, r (s x) = x := by
  let f := Ideal.Quotient.mk (I ^ m)
  let Ext := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f
  let Res := ModuleCat.restrictScalars.{u + 1} f
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f
  have : Ext.Additive := adj.left_adjoint_additive
  have : Res.Additive := adj.right_adjoint_additive
  have : PreservesLimitsOfSize.{0, 0} Res := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits Res := PreservesLimitsOfSize.preservesFiniteLimits Res
  have : PreservesColimitsOfSize.{0, 0} Res :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits Res := PreservesColimitsOfSize.preservesFiniteColimits Res
  let Pb := (Ext.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨ρ, hρ⟩ := exists_cycles_retraction P hP q
  obtain ⟨μ, hμ⟩ := exists_unit_retraction I m N₀ hk
  let ψ : P.X q ⟶ N₀ := ρ ≫ P.homologyπ q ≫ ε.hom ≫ biprod.snd
  let u : P ⟶ (Res.mapHomologicalComplex (.up ℤ)).obj Pb :=
    { f i := adj.unit.app (P.X i)
      comm' i j _ := (adj.unit.naturality (P.d i j)) }
  let g : Pb ⟶ (HomologicalComplex.single _ (.up ℤ) q).obj (Ext.obj N₀) :=
    HomologicalComplex.mkHomToSingle (Ext.map ψ) (by
      intro i _
      change Ext.map (P.d i q) ≫ Ext.map ψ = 0
      rw [← Ext.map_comp]
      have : P.d i q ≫ ρ = P.toCycles i q := by
        rw [← P.toCycles_i i q, Category.assoc, hρ, Category.comp_id]
      simp only [ψ, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
        zero_comp, Ext.map_zero])
  let g' : (Res.mapHomologicalComplex (.up ℤ)).obj Pb ⟶
      (HomologicalComplex.single _ (.up ℤ) q).obj (Res.obj (Ext.obj N₀)) :=
    (Res.mapHomologicalComplex (.up ℤ)).map g ≫
    (HomologicalComplex.singleMapHomologicalComplex Res (.up ℤ) q).hom.app (Ext.obj N₀)
  let eH := (Res.mapHomologicalComplexHomologyIso (.up ℤ) q).app Pb
  let s : N₀ ⟶ Res.obj (Pb.homology q) :=
    biprod.inr ≫ ε.inv ≫ HomologicalComplex.homologyMap u q ≫ eH.hom
  let r : Res.obj (Pb.homology q) ⟶ N₀ := eH.inv ≫ HomologicalComplex.homologyMap g' q ≫
    (HomologicalComplex.singleObjHomologySelfIso _ q _).hom ≫ μ
  have hug : u ≫ g' = HomologicalComplex.mkHomToSingle (ψ ≫ adj.unit.app N₀) (by
      intro i _
      have : P.d i q ≫ ρ = P.toCycles i q := by
        rw [← P.toCycles_i i q, Category.assoc, hρ, Category.comp_id]
      simp only [ψ, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
        zero_comp]) := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.mkHomToSingle_f, Functor.map_comp,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
      Iso.inv_hom_id_map_assoc, Functor.comp_obj, u, g', g]
    exact adj.unit_naturality_assoc ψ _
  have hπ : HomologicalComplex.homologyMap (u ≫ g') q ≫
      (HomologicalComplex.singleObjHomologySelfIso _ q _).hom =
        ε.hom ≫ biprod.snd ≫ adj.unit.app N₀ := by
    rw [← cancel_epi (P.homologyπ q), hug, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
      HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc,
      HomologicalComplex.mkHomToSingle_f]
    simp [ψ, reassoc_of% hρ, Res, Ext]
  have key : s ≫ r = 𝟙 N₀ := by
    simp only [s, r, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← HomologicalComplex.homologyMap_comp_assoc, reassoc_of% hπ, ε.inv_hom_id_assoc,
      biprod.inr_snd_assoc, hμ]
  exact ⟨s.hom, r.hom, fun x ↦ congrArg (fun φ ↦ φ.hom x) key⟩

section

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (f : R →+* S)

/-- Along a surjective ring map, every element of an extension of scalars is a pure tensor
`1 ⊗ m`. -/
theorem exists_extendRestrictScalarsAdj_unit_app_eq (hf : Function.Surjective f)
    {N : ModuleCat.{u + 1} R} (t : (extendScalars.{u + 1, u + 1, u + 1} f).obj N) :
    ∃ m : N, (extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).unit.app N m = t := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro s m
    obtain ⟨a, ha⟩ := hf (show S from s)
    refine ⟨a • m, ?_⟩
    change (show (restrictScalars.{u + 1} f).obj (of S S) from (1 : S)) ⊗ₜ[R] (a • m) = s ⊗ₜ[R] m
    rw [← TensorProduct.smul_tmul]
    congr 1
    change f a * 1 = (show S from s)
    rw [mul_one, ha]
  · intro t₁ t₂ h₁ h₂
    obtain ⟨m₁, rfl⟩ := h₁
    obtain ⟨m₂, rfl⟩ := h₂
    exact ⟨m₁ + m₂, map_add _ _ _⟩

/-- Along a surjective ring map `f`, the kernel of `N → S ⊗_R N` is `(ker f) • N`. -/
theorem mem_of_extendRestrictScalarsAdj_unit_app_eq_zero (hf : Function.Surjective f)
    {N : ModuleCat.{u + 1} R} (m : N)
    (h : (extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).unit.app N m = 0) :
    m ∈ (RingHom.ker f) • (⊤ : Submodule R N) := by
  let J := (RingHom.ker f) • (⊤ : Submodule R N)
  have hQ (a b : R) (hab : f a = f b) (q : N ⧸ J) : a • q = b • q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J q
    rw [← sub_eq_zero, ← sub_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (by simp [RingHom.mem_ker, hab]) trivial
  let g : S → R := Function.surjInv hf
  have hg (s : S) : f (g s) = s := Function.surjInv_eq hf s
  let L : (restrictScalars.{u + 1} f).obj (of S S) →ₗ[R] N →ₗ[R] N ⧸ J :=
    LinearMap.mk₂ R (fun s x ↦ g (show S from s) • J.mkQ x)
      (fun s₁ s₂ x ↦ by
        rw [← add_smul]
        refine hQ _ _ ?_ _
        rw [map_add, hg, hg, hg])
      (fun c s x ↦ by
        rw [smul_smul]
        refine hQ _ _ ?_ _
        rw [map_mul, hg, hg]
        rfl)
      (fun s x₁ x₂ ↦ by rw [map_add, smul_add])
      (fun c s x ↦ by rw [map_smul, smul_comm])
  change (show (restrictScalars.{u + 1} f).obj (of S S) from (1 : S)) ⊗ₜ[R] m =
    (0 : TensorProduct R ((restrictScalars.{u + 1} f).obj (of S S)) N) at h
  have h1 := congrArg (TensorProduct.lift L) h
  rw [map_zero, TensorProduct.lift.tmul] at h1
  change g 1 • J.mkQ m = 0 at h1
  rw [hQ (g 1) 1 (by rw [hg, map_one]), one_smul] at h1
  exact (Submodule.Quotient.mk_eq_zero J).1 h1

end

/-- In `A/π^{n+2}` over a domain, an element killed by `π^{n+1}` is a multiple of `π`. -/
theorem mem_span_of_pow_mul_eq_zero [IsDomain A] (π : A) (hπ : π ≠ 0)
    (c : A ⧸ Ideal.span {π} ^ (n + 1 + 1))
    (h : Ideal.Quotient.mk _ π ^ (n + 1) * c = 0) :
    c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)) π} := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have : a = b * π := by
    apply mul_left_cancel₀ (pow_ne_zero (n + 1) hπ)
    rw [← hb]
    ring
  rw [Ideal.mem_span_singleton']
  exact ⟨Ideal.Quotient.mk _ b, by rw [this, map_mul]⟩

/-- In a projective `A/π^{n+2}`-module over a domain, an element killed by `π^{n+1}` lies in
`πP`. -/
theorem mem_span_smul_top_of_pow_smul_eq_zero [IsDomain A] (π : A) (hπ : π ≠ 0)
    {P : Type*} [AddCommGroup P] [Module (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) P]
    [Module.Projective (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) P] (w : P)
    (h : Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)) π ^ (n + 1) • w = 0) :
    w ∈ (Ideal.span {Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)) π}) •
      (⊤ : Submodule (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) P) := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := A ⧸ Ideal.span {π} ^ (n + 1 + 1)) (P := P)
  rw [← hs w, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul ?_ Submodule.mem_top
  apply mem_span_of_pow_mul_eq_zero n π hπ
  have := congrArg (fun φ ↦ φ i) (map_smul s (Ideal.Quotient.mk _ π ^ (n + 1)) w)
  simpa [h] using this.symm

/-- The kernel of `A/π^{n+2} → A/π^{n+1}` is generated by `π^{n+1}`. -/
theorem exists_eq_pow_smul_of_mem_ker_smul (π : A)
    {N : Type*} [AddCommGroup N] [Module (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) N] (x : N)
    (hx : x ∈ (RingHom.ker (Ideal.Quotient.factorPowSucc (Ideal.span {π}) (n + 1))) •
      (⊤ : Submodule (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) N)) :
    ∃ v : N, x = Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)) π ^ (n + 1) • v := by
  have hle : RingHom.ker (Ideal.Quotient.factorPowSucc (Ideal.span {π}) (n + 1)) ≤
      Ideal.span {Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)) π ^ (n + 1)} := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [Ideal.mem_span_singleton']
    exact ⟨Ideal.Quotient.mk _ c, by rw [map_mul, map_pow]⟩
  have := Submodule.smul_mono_left (N := (⊤ : Submodule _ N)) hle hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨v, -, hv⟩ := this
  exact ⟨v, hv.symm⟩

/-- `exists_levelTor_epi` for an arbitrary complex `K` with an augmentation `ε : K^0 → M` that
is surjective with kernel the image of `K^{-1}`, and with `K^0` projective. The map sends the
class of `1 ⊗ y` with `dy = π^{n+1} z` to the class of `r (ε z)`. -/
theorem exists_levelTor_epi_of_complex [IsDomain A] (π : A) (hπ : π ≠ 0)
    (M : ModuleCat.{u + 1} (A ⧸ Ideal.span {π} ^ (n + 1 + 1))) (N₀ : ModuleCat.{u + 1} A)
    (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)))).obj M)
    (r : (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1)))).obj M →ₗ[A] N₀)
    (hrs : ∀ x, r (s x) = x) (hk : ∀ x : N₀, π ^ (n + 1) • x = 0)
    (K : CochainComplex (ModuleCat.{u + 1} (A ⧸ Ideal.span {π} ^ (n + 1 + 1))) ℤ)
    [Module.Projective (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) (K.X 0)]
    (ε : K.X 0 ⟶ M) (hε : Function.Surjective ε) (hεd : ∀ y, ε (K.d (-1) 0 y) = 0)
    (hex : ∀ z, ε z = 0 → ∃ y, K.d (-1) 0 y = z) :
    ∃ t : (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.factorPowSucc (Ideal.span {π}) (n + 1))).mapHomologicalComplex
          (.up ℤ)).obj K).homology (-1) ⟶ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1)))).obj
          (cokernel (ModuleCat.ofHom (π • LinearMap.id : N₀ →ₗ[A] N₀))), Epi t := by
  classical
  let g := Ideal.Quotient.factorPowSucc (Ideal.span {π}) (n + 1)
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective _
  let p : A ⧸ Ideal.span {π} ^ (n + 1 + 1) := Ideal.Quotient.mk _ π ^ (n + 1)
  let adj := extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} g
  let C := ((extendScalars.{u + 1, u + 1, u + 1} g).mapHomologicalComplex (.up ℤ)).obj K
  let φ := ModuleCat.ofHom (π • LinearMap.id : N₀ →ₗ[A] N₀)
  let Q := cokernel φ
  let mk' := Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1))
  let adjT := extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} mk'
  have hQ (x : N₀) : cokernel.π φ (π • x) = 0 := by
    have := congrArg (fun f ↦ f.hom x) (cokernel.condition φ)
    exact this
  let mkB := Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1 + 1))
  let θ' := (restrictScalars.{u + 1} mkB).map ε ≫
    ModuleCat.ofHom (X := (restrictScalars.{u + 1} mkB).obj M) (Y := N₀) r ≫ cokernel.π φ ≫
    adjT.unit.app Q
  let θ : K.X 0 → (extendScalars.{u + 1, u + 1, u + 1} mk').obj Q := fun z ↦
    θ'.hom (show (restrictScalars.{u + 1} mkB).obj (K.X 0) from z)
  have θ_add (z z' : K.X 0) : θ (z + z') = θ z + θ z' := θ'.hom.map_add _ _
  have θ_zero : θ 0 = 0 := θ'.hom.map_zero
  have θ_sub (z z' : K.X 0) : θ (z - z') = θ z - θ z' := θ'.hom.map_sub _ _
  have θ_smul (b : A ⧸ Ideal.span {π} ^ (n + 1 + 1)) (z : K.X 0) :
      θ (b • z) = g b • θ z := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact θ'.hom.map_smul a z
  have θ_d (y : K.X (-1)) : θ (K.d (-1) 0 y) = 0 := by
    change adjT.unit.app Q (cokernel.π φ (r (ε (K.d (-1) 0 y)))) = 0
    rw [hεd]
    erw [map_zero r]
    rw [map_zero, map_zero]
  have θ_pi (z : K.X 0) : θ (mkB π • z) = 0 := by
    change adjT.unit.app Q (cokernel.π φ (r (ε (mkB π • z)))) = 0
    rw [map_smul]
    have : r (mkB π • ε z) = π • r (ε z) := r.map_smul π (ε z)
    rw [this, hQ, map_zero]
  have θ_span (z : K.X 0) (hz : z ∈ (Ideal.span {mkB π}) •
      (⊤ : Submodule (A ⧸ Ideal.span {π} ^ (n + 1 + 1)) (K.X 0))) : θ z = 0 := by
    refine Submodule.smul_induction_on hz (fun b hb w _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [mul_smul, θ_smul, θ_pi, smul_zero]
    · rw [θ_add, hx, hy, add_zero]
  let IsLift (c : C.X (-1)) (y : K.X (-1)) (z : K.X 0) : Prop :=
    adj.unit.app (K.X (-1)) y = c ∧ K.d (-1) 0 y = p • z
  have wd (c : C.X (-1)) (y : K.X (-1)) (z : K.X 0) (y' : K.X (-1)) (z' : K.X 0)
      (h : IsLift c y z) (h' : IsLift c y' z') : θ z = θ z' := by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', h2'⟩ := h'
    have hyy : adj.unit.app _ (y - y') = 0 := by rw [map_sub, h1, h1']; exact sub_self _
    obtain ⟨v, hv⟩ := exists_eq_pow_smul_of_mem_ker_smul n π (y - y')
      (mem_of_extendRestrictScalarsAdj_unit_app_eq_zero g hg _ hyy)
    have hz : mkB π ^ (n + 1) • (z - z' - K.d (-1) 0 v) = 0 := by
      rw [smul_sub, smul_sub, ← map_smul, ← hv, map_sub]
      change p • z - p • z' - _ = 0
      rw [← h2, ← h2', sub_self]
    have := θ_span _ (mem_span_smul_top_of_pow_smul_eq_zero n π hπ _ hz)
    rw [θ_sub, θ_sub, θ_d, sub_zero, sub_eq_zero] at this
    exact this
  have hlift (c : C.X (-1)) (hc : C.d (-1) 0 c = 0) : ∃ y z, IsLift c y z := by
    obtain ⟨y, rfl⟩ := exists_extendRestrictScalarsAdj_unit_app_eq g hg c
    have : adj.unit.app _ (K.d (-1) 0 y) = 0 := hc
    obtain ⟨v, hv⟩ := exists_eq_pow_smul_of_mem_ker_smul n π _
      (mem_of_extendRestrictScalarsAdj_unit_app_eq_zero g hg _ this)
    exact ⟨y, v, rfl, hv⟩
  let S := C.sc' (-2) (-1) 0
  have hl' (c : LinearMap.ker S.g.hom) : ∃ yz : K.X (-1) × K.X 0, IsLift c.1 yz.1 yz.2 := by
    obtain ⟨y, z, h⟩ := hlift c.1 c.2
    exact ⟨(y, z), h⟩
  have key (c : LinearMap.ker S.g.hom) (y : K.X (-1)) (z : K.X 0) (h : IsLift c.1 y z) :
      θ (hl' c).choose.2 = θ z :=
    wd _ _ _ _ _ (hl' c).choose_spec h
  have lift_add (a b : S.X₂) (y y' : K.X (-1)) (z z' : K.X 0) (h : IsLift a y z)
      (h' : IsLift b y' z') : IsLift (a + b) (y + y') (z + z') := by
    refine ⟨?_, by rw [map_add, h.2, h'.2, smul_add]⟩
    rw [map_add, h.1, h'.1]
  have lift_smul (a : S.X₂) (b : A ⧸ Ideal.span {π} ^ (n + 1 + 1)) (y : K.X (-1)) (z : K.X 0)
      (h : IsLift a y z) : IsLift (g b • a) (b • y) (b • z) := by
    refine ⟨?_, by rw [map_smul, h.2, smul_comm]⟩
    refine ((adj.unit.app _).hom.map_smul b y).trans ?_
    rw [h.1]
    rfl
  let t₀ : LinearMap.ker S.g.hom →ₗ[A ⧸ Ideal.span {π} ^ (n + 1)]
      (extendScalars.{u + 1, u + 1, u + 1} mk').obj Q :=
    { toFun c := θ (hl' c).choose.2
      map_add' c c' := by
        rw [key (c + c') _ _ (lift_add _ _ _ _ _ _ (hl' c).choose_spec (hl' c').choose_spec),
          θ_add]
      map_smul' b c := by
        obtain ⟨b, rfl⟩ := hg b
        rw [key (g b • c) _ _ (lift_smul _ b _ _ (hl' c).choose_spec), θ_smul]
        rfl }
  have ht₀ (c : LinearMap.ker S.g.hom) (y : K.X (-1)) (z : K.X 0) (h : IsLift c.1 y z) :
      t₀ c = θ z := key c y z h
  have hle : LinearMap.range S.moduleCatToCycles ≤ LinearMap.ker t₀ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := exists_extendRestrictScalarsAdj_unit_app_eq g hg x
    rw [LinearMap.mem_ker, ht₀ _ (K.d (-2) (-1) v) 0 ⟨rfl, ?_⟩, θ_zero]
    rw [smul_zero]
    exact congrArg (fun f ↦ f.hom v) (K.d_comp_d (-2) (-1) 0)
  have hsurj : Function.Surjective t₀ := by
    intro w
    obtain ⟨q, rfl⟩ := exists_extendRestrictScalarsAdj_unit_app_eq mk'
      Ideal.Quotient.mk_surjective w
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π φ)).1 inferInstance q
    obtain ⟨z, hz⟩ := hε (s x)
    have hpz : ε (p • z) = 0 := by
      rw [map_smul, hz]
      have := s.map_smul (π ^ (n + 1)) x
      rw [hk, map_zero] at this
      rw [show p = mkB (π ^ (n + 1)) from (map_pow _ _ _).symm]
      exact this.symm
    obtain ⟨y, hy⟩ := hex _ hpz
    have hgp : g p = 0 := by
      change g (mkB π ^ (n + 1)) = 0
      rw [map_pow, show g (mkB π) = mk' π from Ideal.Quotient.factor_mk _ _, ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) _
    have hc : S.g.hom (adj.unit.app _ y) = 0 := by
      change adj.unit.app _ (K.d (-1) 0 y) = 0
      rw [hy, (adj.unit.app _).hom.map_smul]
      rw [restrictScalars.smul_def, hgp, zero_smul]
    refine ⟨⟨adj.unit.app _ y, hc⟩, ?_⟩
    have hrz : r (ε z) = x := by rw [hz]; exact hrs x
    rw [ht₀ _ y z ⟨rfl, hy⟩]
    exact congrArg (fun q ↦ adjT.unit.app Q (cokernel.π φ q)) hrz
  let ψ : S.moduleCatLeftHomologyData.H ⟶ (extendScalars.{u + 1, u + 1, u + 1} mk').obj Q :=
    ModuleCat.ofHom (X := S.moduleCatLeftHomologyData.H)
      (Y := (extendScalars.{u + 1, u + 1, u + 1} mk').obj Q)
      ((LinearMap.range S.moduleCatToCycles).liftQ t₀ hle)
  have : Epi ψ := by
    rw [ModuleCat.epi_iff_surjective]
    intro w
    obtain ⟨c, rfl⟩ := hsurj w
    exact ⟨Submodule.Quotient.mk c, rfl⟩
  exact ⟨(C.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp)).hom ≫
    S.moduleCatHomologyIso.hom ≫ ψ, inferInstance⟩

/-- The augmentation of the chosen projective resolution, read on the `ℤ`-indexed complex:
it is surjective and its kernel is the image of the differential. -/
theorem exists_projectiveResolution_augmentation {B : Type (u + 1)} [Ring B]
    (M : ModuleCat.{u + 1} B) :
    ∃ ε : (projectiveResolution M).cochainComplex.X 0 ⟶ M, Function.Surjective ε ∧
      (∀ y, ε ((projectiveResolution M).cochainComplex.d (-1) 0 y) = 0) ∧
      ∀ z, ε z = 0 → ∃ y, (projectiveResolution M).cochainComplex.d (-1) 0 y = z := by
  let R := projectiveResolution M
  let K := R.cochainComplex
  let i₀ := R.cochainComplexXIso 0 0
  let i₁ := R.cochainComplexXIso (-1) 1
  let j := HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M
  let ε : K.X 0 ⟶ M := i₀.hom ≫ R.π.f 0 ≫ j.hom
  have hdε : K.d (-1) 0 ≫ ε = 0 := by
    rw [R.cochainComplex_d (-1) 0 1 0]
    simp only [ε, Category.assoc]
    rw [Iso.inv_hom_id_assoc, reassoc_of% R.complex_d_comp_π_f_zero, zero_comp, comp_zero]
  refine ⟨ε, (ModuleCat.epi_iff_surjective ε).1 (epi_comp _ _),
    fun y ↦ congrArg (fun f ↦ f.hom y) hdε, fun z hz ↦ ?_⟩
  have h0 : R.π.f 0 (i₀.hom z) = 0 := by
    have h := congrArg j.inv hz
    rw [map_zero, ← ConcreteCategory.comp_apply] at h
    have h' : (i₀.hom ≫ R.π.f 0) z = 0 := by
      simpa only [ε, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
    rwa [ConcreteCategory.comp_apply] at h'
  obtain ⟨y', hy'⟩ := (ShortComplex.moduleCat_exact_iff _).1 R.exact₀ _ h0
  refine ⟨i₁.inv y', ?_⟩
  have e1 : i₁.inv ≫ K.d (-1) 0 = R.complex.d 1 0 ≫ i₀.inv := by
    rw [R.cochainComplex_d (-1) 0 1 0, Iso.inv_hom_id_assoc]
  have e2 := congrArg (fun f ↦ f.hom y') e1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2
  rw [e2]
  change i₀.inv (R.complex.d 1 0 y') = z
  rw [hy']
  exact i₀.hom_inv_id_apply z

/-- The terms of the chosen projective resolution are projective modules. -/
theorem projective_projectiveResolution_X {B : Type (u + 1)} [Ring B]
    (M : ModuleCat.{u + 1} B) (i : ℤ) :
    Module.Projective B ((projectiveResolution M).cochainComplex.X i) :=
  (IsProjective.iff_projective _).2
    (inferInstanceAs (Projective ((projectiveResolution M).cochainComplex.X i)))

/-- The module-level consecutive-quotient Tor of a module containing a retract `N₀` killed
by `π^{n+1}` surjects onto `N₀/πN₀`.

Proof sketch: tensor `0 → A/π --π^{n+1}--> A/π^{n+2} → A/π^{n+1} → 0` with the projective
resolution `R → M`; the connecting map sends `H^{-1}(R ⊗ A/π^{n+1})` onto the kernel of
`π^{n+1} : M/πM → M`. For `x : N₀`, `s x` is killed by `π^{n+1}`, so its class lies in that
kernel, and `r` sends it to `x` modulo `π`. -/
theorem exists_levelTor_epi [IsDomain A] (π : A) (hπ : π ≠ 0) (hI : I = Ideal.span {π})
    (M : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1 + 1))) (N₀ : ModuleCat.{u + 1} A)
    (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).obj M)
    (r : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).obj M →ₗ[A] N₀)
    (hrs : ∀ x, r (s x) = x) (hk : ∀ x : N₀, π ^ (n + 1) • x = 0) :
    ∃ t : levelTor I n M ⟶ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (I ^ (n + 1)))).obj
          (cokernel (ModuleCat.ofHom (π • LinearMap.id : N₀ →ₗ[A] N₀))), Epi t := by
  subst hI
  have := projective_projectiveResolution_X M 0
  obtain ⟨ε, hε, hεd, hex⟩ := exists_projectiveResolution_augmentation M
  exact exists_levelTor_epi_of_complex n π hπ M N₀ s r hrs hk _ ε hε hεd hex

end ModuleCat
