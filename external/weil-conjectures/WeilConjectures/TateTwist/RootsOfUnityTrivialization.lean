/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.RootsOfUnityPullback
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The trivialization of `μ_N` over a field containing a primitive root of unity

Let `U` be a scheme over a field `K` and `ζ ∈ K` with `ζ ^ N = 1`. The map `a ↦ ζ ^ a` defines a
morphism `ℤ ⟶ μ_N` of pro-étale sheaves on `U` from the unit `ℤ` of the monoidal structure to
the sheaf `μ_N` of `N`-th roots of unity. It kills `N`, and when `ζ` is a primitive `N`-th root
of unity it exhibits `μ_N` as the cokernel of `N : ℤ ⟶ ℤ`, i.e. `ℤ/N ≅ μ_N`.

The map is the sheafification of the map of presheaves `a ↦ ζ ^ a`. The induced map from the
presheaf cokernel `ℤ/N` to `U ↦ μ_N(Γ(U, 𝒪_U))` is locally injective (a nonzero `ζ ^ a - 1` is a
unit of `K`, which only vanishes on the empty scheme) and locally surjective (an `N`-th root of
unity `x` agrees with `r` on the open set where `∏_{s ≠ r} (x - s)` is invertible, and these
open sets cover by Lagrange interpolation), hence becomes an isomorphism after sheafification.

## Main definitions

- `AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf`: the map `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`.
- `AlgebraicGeometry.ProEtale.isColimitUnitToRootsOfUnitySheaf`: for `ζ` a primitive `N`-th
  root of unity, `ℤ ⟶ μ_N` is a cokernel of `N : ℤ ⟶ ℤ`.

## Main statements

- `AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf_comp_rootsOfUnitySheafPow`: compatibility
  with the power maps `μ_{m N} ⟶ μ_N`.
- `AlgebraicGeometry.ProEtale.zsmul_unitToRootsOfUnitySheaf`: `ℤ ⟶ μ_N` kills `N`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {K : Type u} [Field K] {U : Scheme.{u}}

/-- Restriction in `U ↦ μ_N(Γ(U, 𝒪_U))` along `h` is induced by `h^♯` on global sections. -/
lemma rootsOfUnityPresheaf_map (X : Scheme.{u}) (N : ℕ) {V W : X.ProEtᵒᵖ} (h : V ⟶ W) :
    (rootsOfUnityPresheaf X N).map h =
      (CommRingCat.rootsOfUnityFunctor N).map h.unop.left.appTop :=
  rfl

/-- For `U` over `Spec K` and `V` in the small pro-étale site of `U`, the ring map
`K ⟶ Γ(V, 𝒪_V)`. -/
noncomputable def fieldToSections (f : U ⟶ Spec (.of K)) (V : U.ProEt) :
    CommRingCat.of K ⟶ Γ(V.left, ⊤) :=
  (ΓSpecIso (.of K)).inv ≫ (V.hom ≫ f).appTop

/-- The ring maps `K ⟶ Γ(V, 𝒪_V)` are compatible with restriction. -/
@[reassoc]
lemma fieldToSections_comp_appTop (f : U ⟶ Spec (.of K)) {V W : U.ProEt} (h : W ⟶ V) :
    fieldToSections f V ≫ h.left.appTop = fieldToSections f W := by
  rw [fieldToSections, fieldToSections, Category.assoc, ← Scheme.Hom.comp_appTop,
    ← Category.assoc, MorphismProperty.Over.w h]

/-- The homomorphism `ℤ ⟶ μ_N(K)`, `a ↦ z ^ a`, for an `N`-th root of unity `z` of `K`. -/
noncomputable def unitToRootsOfUnity {N : ℕ} (z : rootsOfUnity N K) :
    𝟙_ Ab.{u + 1} ⟶ (CommRingCat.rootsOfUnityFunctor N).obj (.of K) :=
  AddCommGrpCat.ofHom ((zmultiplesHom _ (ULift.up (Additive.ofMul z) :
    (CommRingCat.rootsOfUnityFunctor N).obj (.of K))).comp AddEquiv.ulift.toAddMonoidHom)

/-- The map of presheaves `ℤ ⟶ μ_N` on `U_proét`, `a ↦ z ^ a`, for an `N`-th root of unity `z`
of `K`. -/
noncomputable def unitToRootsOfUnityPresheaf (f : U ⟶ Spec (.of K)) {N : ℕ}
    (z : rootsOfUnity N K) : 𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⟶ rootsOfUnityPresheaf U N where
  app V := unitToRootsOfUnity z ≫ (CommRingCat.rootsOfUnityFunctor N).map
    (fieldToSections f V.unop)
  naturality V W h := by
    rw [rootsOfUnityPresheaf_map, Category.assoc, ← Functor.map_comp, fieldToSections_comp_appTop]
    exact Category.id_comp _

/-- `AlgebraicGeometry.ProEtale.unitToRootsOfUnity z` sends `a` to `z ^ a`. -/
lemma unitToRootsOfUnity_apply {N : ℕ} (z : rootsOfUnity N K) (a : 𝟙_ Ab.{u + 1}) :
    unitToRootsOfUnity z a = ULift.up (a.down • Additive.ofMul z) :=
  rfl

/-- An `N`-th root of unity, as an element of `rootsOfUnity N K`, has `N`-th power `1`. -/
lemma rootsOfUnity_pow_eq_one {M : Type*} [CommMonoid M] {N : ℕ} (z : rootsOfUnity N M) :
    z ^ N = 1 :=
  Subtype.ext (by simpa using (mem_rootsOfUnity _ _).1 z.2)

/-- `a ↦ z ^ a` kills `N`. -/
lemma zsmul_comp_unitToRootsOfUnity {N : ℕ} (z : rootsOfUnity N K) :
    ((N : ℤ) • 𝟙 (𝟙_ Ab.{u + 1})) ≫ unitToRootsOfUnity z = 0 := by
  ext a
  apply ULift.ext
  simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_zsmul, AddCommGrpCat.hom_id,
    AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply,
    AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply, unitToRootsOfUnity_apply]
  refine (congrArg (· • Additive.ofMul z) (mul_comm (N : ℤ) a.down)).trans ?_
  rw [mul_smul, natCast_zsmul, ← ofMul_pow, rootsOfUnity_pow_eq_one, ofMul_one, smul_zero]
  rfl

/-- `a ↦ 1 ^ a` is zero. -/
lemma unitToRootsOfUnity_one {N : ℕ} : unitToRootsOfUnity (1 : rootsOfUnity N K) = 0 := by
  ext a
  apply ULift.ext
  simp [unitToRootsOfUnity_apply]

/-- `a ↦ z ^ a` is compatible with the `m`-th power maps `μ_{m N}(K) ⟶ μ_N(K)`. -/
lemma unitToRootsOfUnity_comp_rootsOfUnityPow {N m : ℕ} (z : rootsOfUnity (m * N) K) :
    unitToRootsOfUnity z ≫ (CommRingCat.rootsOfUnityPow N m).app (.of K) =
      unitToRootsOfUnity (CommRingCat.rootsOfUnityPowHom N m K z) := by
  ext a
  apply ULift.ext
  exact map_zsmul (MonoidHom.toAdditive (CommRingCat.rootsOfUnityPowHom N m K)) a.down
    (Additive.ofMul z)

/-- The value of `AlgebraicGeometry.ProEtale.unitToRootsOfUnityPresheaf` at `a` over `V` is the
image of `z ^ a` in `μ_N(Γ(V, 𝒪_V))`. -/
lemma unitToRootsOfUnityPresheaf_app_apply (f : U ⟶ Spec (.of K)) {N : ℕ}
    (z : rootsOfUnity N K) (V : U.ProEtᵒᵖ) (a : (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1})).obj V) :
    (unitToRootsOfUnityPresheaf f z).app V a = ULift.up (Additive.ofMul
      (restrictRootsOfUnity (fieldToSections f V.unop).hom N (z ^ a.down))) :=
  rfl

/-- The value of `AlgebraicGeometry.ProEtale.unitToRootsOfUnityPresheaf` at `i ∈ ℕ` over `V` is
`z ^ i`, as a function on `V`. -/
lemma unitToRootsOfUnityPresheaf_app_natCast_val (f : U ⟶ Spec (.of K)) {N : ℕ}
    (z : rootsOfUnity N K) (V : U.ProEtᵒᵖ) (i : ℕ) :
    (((Additive.toMul ((unitToRootsOfUnityPresheaf f z).app V (ULift.up (i : ℤ))).down :
      rootsOfUnity N Γ(V.unop.left, ⊤)) : Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤)) =
      fieldToSections f V.unop ((z : Kˣ) : K) ^ i := by
  calc _ = (((restrictRootsOfUnity (fieldToSections f V.unop).hom N (z ^ i) :
        rootsOfUnity N Γ(V.unop.left, ⊤)) : Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤)) := by
        rw [← zpow_natCast]
        rfl
    _ = _ := by simp

/-- `a ↦ z ^ a` kills `N`, on presheaves. -/
lemma zsmul_comp_unitToRootsOfUnityPresheaf (f : U ⟶ Spec (.of K)) {N : ℕ}
    (z : rootsOfUnity N K) :
    ((N : ℤ) • 𝟙 (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1}))) ≫ unitToRootsOfUnityPresheaf f z = 0 := by
  ext V : 2
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (zsmul_comp_unitToRootsOfUnity z)).trans zero_comp)

/-- `a ↦ 1 ^ a` is zero, on presheaves. -/
lemma unitToRootsOfUnityPresheaf_one (f : U ⟶ Spec (.of K)) {N : ℕ} :
    unitToRootsOfUnityPresheaf f (1 : rootsOfUnity N K) = 0 := by
  ext V : 2
  exact (congrArg (· ≫ _) unitToRootsOfUnity_one).trans zero_comp

/-- `a ↦ z ^ a` is compatible with the `m`-th power maps `μ_{m N} ⟶ μ_N`, on presheaves. -/
lemma unitToRootsOfUnityPresheaf_comp_rootsOfUnityPresheafPow (f : U ⟶ Spec (.of K)) {N m : ℕ}
    (z : rootsOfUnity (m * N) K) :
    unitToRootsOfUnityPresheaf f z ≫ rootsOfUnityPresheafPow U N m =
      unitToRootsOfUnityPresheaf f (CommRingCat.rootsOfUnityPowHom N m K z) := by
  ext V : 2
  simp only [NatTrans.comp_app, unitToRootsOfUnityPresheaf, rootsOfUnityPresheafPow,
    Functor.whiskerLeft_app, Category.assoc]
  refine (congrArg (unitToRootsOfUnity z ≫ ·)
    ((CommRingCat.rootsOfUnityPow N m).naturality (fieldToSections f V.unop))).trans ?_
  rw [← Category.assoc, unitToRootsOfUnity_comp_rootsOfUnityPow]

/-- The map of pro-étale sheaves `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`, for `U` over a field `K` and `ζ ∈ K`
with `ζ ^ N = 1`: the sheafification of `AlgebraicGeometry.ProEtale.unitToRootsOfUnityPresheaf`.
(For `N = 0` it is defined to be zero, as `ζ` need not be a unit.) -/
noncomputable def unitToRootsOfUnitySheaf (f : U ⟶ Spec (.of K)) {N : ℕ} {ζ : K}
    (hζ : ζ ^ N = 1) :
    𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1}) ⟶ rootsOfUnitySheaf U N :=
  if hN : N = 0 then 0 else
    have : NeZero N := ⟨hN⟩
    (presheafToSheaf (ProEt.topology U) Ab.{u + 1}).map
      (unitToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ))

/-- For `N ≠ 0`, `AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf` is the sheafification of
`AlgebraicGeometry.ProEtale.unitToRootsOfUnityPresheaf`. -/
lemma unitToRootsOfUnitySheaf_eq (f : U ⟶ Spec (.of K)) {N : ℕ} [NeZero N] {ζ : K}
    (hζ : ζ ^ N = 1) :
    unitToRootsOfUnitySheaf f hζ = (presheafToSheaf (ProEt.topology U) Ab.{u + 1}).map
      (unitToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ)) :=
  dite_eq_right (NeZero.ne N)

/-- For `N = 0`, `AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf` is zero by definition. -/
lemma unitToRootsOfUnitySheaf_of_eq_zero (f : U ⟶ Spec (.of K)) {ζ : K} (hζ : ζ ^ 0 = 1) :
    unitToRootsOfUnitySheaf f hζ = 0 :=
  dite_eq_left rfl

/-- The map `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`, is compatible with the power maps `μ_{m N} ⟶ μ_N`. -/
lemma unitToRootsOfUnitySheaf_comp_rootsOfUnitySheafPow (f : U ⟶ Spec (.of K)) {N m : ℕ}
    {ζ ζ' : K} (hζ : ζ ^ N = 1) (hζ' : ζ' ^ (m * N) = 1) (h : ζ' ^ m = ζ) :
    unitToRootsOfUnitySheaf f hζ' ≫ rootsOfUnitySheafPow U N m =
      unitToRootsOfUnitySheaf f hζ := by
  rcases Nat.eq_zero_or_pos (m * N) with hmN | hmN
  · rw [unitToRootsOfUnitySheaf, dite_eq_left hmN, zero_comp]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact (unitToRootsOfUnitySheaf_of_eq_zero f hζ).symm
    · obtain rfl : m = 0 := by
        rcases Nat.mul_eq_zero.1 hmN with h' | h'
        · exact h'
        · omega
      have : NeZero N := ⟨hN.ne'⟩
      obtain rfl : ζ = 1 := by rw [← h, pow_zero]
      have e : rootsOfUnity.mkOfPowEq (1 : K) hζ = 1 := by
        ext
        simp
      rw [unitToRootsOfUnitySheaf_eq, e, unitToRootsOfUnityPresheaf_one, Functor.map_zero]
  · have : NeZero (m * N) := ⟨hmN.ne'⟩
    have : NeZero N := ⟨(Nat.pos_of_mul_pos_left hmN).ne'⟩
    rw [unitToRootsOfUnitySheaf_eq, unitToRootsOfUnitySheaf_eq, rootsOfUnitySheafPow_eq,
      ← Functor.map_comp, unitToRootsOfUnityPresheaf_comp_rootsOfUnityPresheafPow]
    congr 2
    ext
    simp [CommRingCat.rootsOfUnityPowHom, h]

/-- `N • 𝟙` on the unit pro-étale sheaf is the sheafification of `N • 𝟙` on the unit
presheaf. -/
lemma zsmul_id_tensorUnit_eq (n : ℤ) :
    n • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})) =
      (presheafToSheaf (ProEt.topology U) Ab.{u + 1}).map
        (n • 𝟙 (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1}))) := by
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rfl

/-- The map `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`, kills `N`. -/
lemma zsmul_unitToRootsOfUnitySheaf (f : U ⟶ Spec (.of K)) {N : ℕ} {ζ : K} (hζ : ζ ^ N = 1) :
    (((N : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1}))) ≫
      unitToRootsOfUnitySheaf f hζ = 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [unitToRootsOfUnitySheaf_of_eq_zero, comp_zero]
  · have : NeZero N := ⟨hN⟩
    rw [unitToRootsOfUnitySheaf_eq, zsmul_id_tensorUnit_eq, ← Functor.map_comp,
      zsmul_comp_unitToRootsOfUnityPresheaf, Functor.map_zero]

/-- **Local surjectivity of `a ↦ ζ ^ a` onto `μ_N`.** Let `U` be a scheme over a field `K` and
`ζ ∈ K` a primitive `N`-th root of unity. Every `N`-th root of unity `x` of `Γ(V, 𝒪_V)` is,
Zariski locally on `V`, of the form `ζ ^ a`: with `y_r = ∏_{s ≠ r} (x - s)` for the `N`-th roots
of unity `r ∈ K`, `x = r` on the basic open set `D(y_r)`, as `y_r (x - r) = xᴺ - 1 = 0`, and these
open sets cover `V`, as the `y_r` generate the unit ideal by Lagrange interpolation. -/
lemma imageSieve_unitToRootsOfUnityPresheaf_mem (f : U ⟶ Spec (.of K)) {N : ℕ} [NeZero N]
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) {V : U.ProEt} (s : (rootsOfUnityPresheaf U N).obj (op V)) :
    Presheaf.imageSieve (unitToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one))
      s ∈ ProEt.topology U V := by
  classical
  have hn : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  let ρ : K →+* Γ(V.left, ⊤) := (fieldToSections f V).hom
  let u : Γ(V.left, ⊤) :=
    (((Additive.toMul s.down : rootsOfUnity N Γ(V.left, ⊤)) : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤))
  have hu : u ^ N = 1 := by
    simp only [u, ← Units.val_pow_eq_pow_val, ← SubmonoidClass.coe_pow, rootsOfUnity_pow_eq_one]
    rfl
  let R := Polynomial.nthRootsFinset N (1 : K)
  let y : R → Γ(V.left, ⊤) := fun r ↦ ∏ t ∈ R.erase r, (u - ρ t)
  let D : R → V.left.Opens := fun r ↦ V.left.basicOpen (y r)
  refine ProEt.mem_topology_of_openImmersion _ (fun r ↦ (D r).ι) (fun p ↦ ?_) (fun r ↦ ?_)
  · have hspan : Ideal.span (Set.range y) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← Polynomial.sum_mul_prod_erase_sub_eq_one ρ hn u]
      exact Ideal.sum_mem _ fun r hr ↦
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    have hp : p ∈ (⨆ i ∈ Set.range y, V.left.basicOpen i) := by
      rw [iSup_basicOpen_of_span_eq_top (X := V.left) ⊤ _ hspan]
      exact TopologicalSpace.Opens.mem_top p
    simp only [TopologicalSpace.Opens.mem_iSup] at hp
    obtain ⟨_, ⟨r, rfl⟩, hpr⟩ := hp
    refine ⟨r, ?_⟩
    rw [Scheme.Opens.range_ι]
    exact hpr
  · obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn _).1 r.2)
    refine ⟨ULift.up (i : ℤ), ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    have h0 := congrArg (D r).ι.appTop (Polynomial.prod_erase_mul_sub_eq_zero ρ hζ hn hu r.1 r.2)
    rw [map_mul, map_zero, (V.left.isUnit_ι_appTop_basicOpen (y r)).mul_right_eq_zero, map_sub,
      sub_eq_zero] at h0
    refine Eq.trans ?_ h0.symm
    refine (unitToRootsOfUnityPresheaf_app_natCast_val f _ _ i).trans ?_
    rw [rootsOfUnity.coe_mkOfPowEq, ← map_pow, hi]
    exact ConcreteCategory.congr_hom
      (fieldToSections_comp_appTop f (V.ofOpenImmersionHom (D r).ι)).symm r

/-- The map `ℤ/N ⟶ μ_N` of presheaves on `U_proét` from the presheaf cokernel of `N` on the
unit presheaf `ℤ`, induced by `a ↦ z ^ a`. -/
noncomputable def cokernelToRootsOfUnityPresheaf (f : U ⟶ Spec (.of K)) {N : ℕ}
    (z : rootsOfUnity N K) :
    cokernel ((N : ℤ) • 𝟙 (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1}))) ⟶ rootsOfUnityPresheaf U N :=
  cokernel.desc _ (unitToRootsOfUnityPresheaf f z) (zsmul_comp_unitToRootsOfUnityPresheaf f z)

/-- **Local injectivity of `ℤ/N ⟶ μ_N`.** If `ζ ∈ K` is a primitive `N`-th root of unity, then
`ζ ^ a = ζ ^ b` on `V` with `a ≢ b (mod N)` forces `V` to be empty, since `ζ ^ (a - b) - 1` is a
unit of `K` vanishing on `V`; and the empty scheme is covered by the empty family. -/
lemma isLocallyInjective_cokernelToRootsOfUnityPresheaf (f : U ⟶ Spec (.of K)) {N : ℕ}
    [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Presheaf.IsLocallyInjective (ProEt.topology U)
      (cokernelToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one)) where
  equalizerSieve_mem {V} x y hxy := by
    set z := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
    let π := cokernel.π ((N : ℤ) • 𝟙 (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1})))
    have hπ : Function.Surjective (π.app V) :=
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨b, rfl⟩ := hπ y
    by_cases hab : π.app V a = π.app V b
    · rw [hab]
      simp
    refine (ProEt.topology U).superset_covering bot_le ?_
    have e (c) : (cokernelToRootsOfUnityPresheaf f z).app V (π.app V c) =
        (unitToRootsOfUnityPresheaf f z).app V c := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cokernelToRootsOfUnityPresheaf,
        cokernel.π_desc]
    have hxy' := (e a).symm.trans (hxy.trans (e b))
    rw [unitToRootsOfUnityPresheaf_app_apply, unitToRootsOfUnityPresheaf_app_apply] at hxy'
    have h1 := Additive.ofMul.injective (ULift.up.inj hxy')
    have hdiv : ¬ (N : ℤ) ∣ a.down - b.down := by
      rintro ⟨c, hc⟩
      apply hab
      have hac : a = b + ((N : ℤ) • 𝟙 (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1}))).app V (ULift.up c) := by
        refine ULift.ext ?_
        exact sub_eq_iff_eq_add'.1 hc
      rw [hac, map_add, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cokernel.condition]
      simp
    have hz : IsPrimitiveRoot z N := by
      rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff,
        rootsOfUnity.coe_mkOfPowEq]
      exact hζ
    have hw : z ^ (a.down - b.down) ≠ 1 := fun h ↦ hdiv ((hz.zpow_eq_one_iff_dvd _).1 h)
    have h2 :
        restrictRootsOfUnity (fieldToSections f V.unop).hom N (z ^ (a.down - b.down)) = 1 := by
      simp [zpow_sub, h1]
    set w := z ^ (a.down - b.down)
    have hc : ((w : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.2 fun h ↦ hw (Subtype.ext (Units.ext h))
    have h3 : (fieldToSections f V.unop) (((w : Kˣ) : K) - 1) = 0 := by
      have := Units.ext_iff.1 (Subtype.ext_iff.1 h2)
      simp only [restrictRootsOfUnity_coe_apply] at this
      rw [map_sub, this, map_one]
      simp
    have : Subsingleton Γ(V.unop.left, ⊤) := by
      refine subsingleton_of_zero_eq_one ?_
      calc (0 : Γ(V.unop.left, ⊤)) = (fieldToSections f V.unop) (((w : Kˣ) : K) - 1) *
          (fieldToSections f V.unop) (((w : Kˣ) : K) - 1)⁻¹ := by rw [h3, zero_mul]
        _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    have := Scheme.isEmpty_of_subsingleton_Γ this
    exact ProEt.bot_mem_topology _

/-- The map `ℤ/N ⟶ μ_N` becomes an isomorphism after sheafification when `ζ` is a primitive
`N`-th root of unity: it is locally injective and locally surjective. -/
lemma isIso_presheafToSheaf_map_cokernelToRootsOfUnityPresheaf (f : U ⟶ Spec (.of K)) {N : ℕ}
    [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    IsIso ((presheafToSheaf (ProEt.topology U) Ab.{u + 1}).map
      (cokernelToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one))) := by
  have := isLocallyInjective_cokernelToRootsOfUnityPresheaf f hζ
  have : Presheaf.IsLocallySurjective (ProEt.topology U)
      (cokernelToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one)) := by
    have : Presheaf.IsLocallySurjective (ProEt.topology U)
        (cokernel.π _ ≫ cokernelToRootsOfUnityPresheaf f
          (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one)) := by
      rw [cokernelToRootsOfUnityPresheaf, cokernel.π_desc]
      exact ⟨fun s ↦ imageSieve_unitToRootsOfUnityPresheaf_mem f hζ s⟩
    exact Presheaf.isLocallySurjective_of_isLocallySurjective _ (cokernel.π _) _
  exact (GrothendieckTopology.W_iff _ _).1 (GrothendieckTopology.W_of_isLocallyBijective _ _)

/-- **`ℤ/N ≅ μ_N`.** Let `U` be a scheme over a field `K` and `ζ ∈ K` a primitive `N`-th root of
unity. Then `a ↦ ζ ^ a` exhibits the sheaf `μ_N` on `U_proét` as the cokernel of
`N : ℤ ⟶ ℤ` on the unit sheaf `ℤ`. Indeed sheafification preserves cokernels, and the induced
map from the presheaf cokernel `ℤ/N` to `μ_N` becomes an isomorphism after sheafification
(`AlgebraicGeometry.ProEtale.isIso_presheafToSheaf_map_cokernelToRootsOfUnityPresheaf`). -/
noncomputable def isColimitUnitToRootsOfUnitySheaf (f : U ⟶ Spec (.of K)) {N : ℕ} [NeZero N]
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    IsColimit (CokernelCofork.ofπ _ (zsmul_unitToRootsOfUnitySheaf f hζ.pow_eq_one)) :=
  have := isIso_presheafToSheaf_map_cokernelToRootsOfUnityPresheaf f hζ
  Cofork.isColimitOfIsos _ (isColimitOfHasCokernelOfPreservesColimit
      (presheafToSheaf (ProEt.topology U) Ab.{u + 1})
      ((N : ℤ) • 𝟙 (𝟙_ (U.ProEtᵒᵖ ⥤ Ab.{u + 1})))) _ (Iso.refl _) (Iso.refl _)
    (asIso ((presheafToSheaf (ProEt.topology U) Ab.{u + 1}).map
      (cokernelToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one))))
    (by rw [zsmul_id_tensorUnit_eq]; simp) (by simp) (by
      simp only [Iso.refl_inv, Cofork.π_ofπ, asIso_hom]
      exact (Category.id_comp _).trans ((Functor.map_comp _ _ _).symm.trans
        ((congrArg _ (cokernel.π_desc _ _ _)).trans
          (unitToRootsOfUnitySheaf_eq f hζ.pow_eq_one).symm)))

end AlgebraicGeometry.ProEtale
