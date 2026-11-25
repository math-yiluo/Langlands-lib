/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.TraceFormula.LocalTermLocality

/-!

# The ideal conditions of a contracting correspondence

Let `c = (c₁, c₂) : C ⟶ X × X` be a correspondence contracting at the rational point `y` of `C`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt`), and write `x = c₁(y) = c₂(y)`. Let
`I` be the ideal sheaf of the closed point `x` of `X` and `J` the ideal sheaf of the closed
point `y` of `C` (the kernels of the closed immersions `x, y : Spec k ⟶ X, C`). The
specialization to the normal cone
(`WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap`)
takes as input inclusions of ideals on pairs of affine opens `U' ⊆ c_i⁻¹ U`:

1. `(c_i^* I)(U') ⊆ J(U')` for `i = 1, 2`, since functions vanishing at `x` pull back to functions
   vanishing at `y`
   (`ProEtale.CondensedRing.Correspondence.IsContractingAt.ker_map_le_c₁`,
   `ProEtale.CondensedRing.Correspondence.IsContractingAt.ker_map_le_c₂`);
2. `(c₂^* I)(U')^n ⊆ J(U')^{n+1}` for the `n ≥ 1` of the contraction condition
   (`ProEtale.CondensedRing.Correspondence.IsContractingAt.ker_map_pow_le`).

For the second, `J(U')` is either `Γ(U')` (if `y ∉ U'`) or the maximal ideal `𝔭` of `y` in
`Γ(U')`. The power `𝔭^{n+1}` is `𝔭`-primary, hence the contraction of its extension
`𝔪_y^{n+1}` to the stalk `𝒪_{C,y} = Γ(U')_𝔭`, and in the stalk
`(c₂^* I)(U')^n 𝒪_{C,y} ⊆ (c₂^♯ 𝔪_x)^n ⊆ (c₁^♯ 𝔪_x)^{n+1} ⊆ 𝔪_y^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory IsLocalRing

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace Scheme

/-- The ideal of the closure of the image of a morphism from a reduced scheme with image a closed
point `c`, over an affine open `U`: the vanishing ideal of the points of `Spec Γ(U)` lying over
`c`. -/
lemma Hom.ker_ideal_of_range_eq_singleton {T C : Scheme.{u}} (y : T ⟶ C) [IsReduced T] {c : C}
    (hy : Set.range y = {c}) (hc : IsClosed ({c} : Set C)) {U : C.Opens} (hU : IsAffineOpen U) :
    y.ker.ideal ⟨U, hU⟩ = PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' {c}) := by
  rw [y.ker_eq_vanishingIdeal, IdealSheafData.vanishingIdeal_ideal]
  congr 2
  change closure (Set.range y) = _
  rw [hy, hc.closure_eq]

/-- The ideal of a morphism from a reduced scheme with image a closed point `c`, over an affine
open `U` containing `c`, is the prime ideal of `c` in `Γ(U)`. -/
lemma Hom.ker_ideal_eq_primeIdealOf {T C : Scheme.{u}} (y : T ⟶ C) [IsReduced T] {c : C}
    (hy : Set.range y = {c}) (hc : IsClosed ({c} : Set C)) {U : C.Opens} (hU : IsAffineOpen U)
    (hcU : c ∈ U) : y.ker.ideal ⟨U, hU⟩ = (hU.primeIdealOf ⟨c, hcU⟩).asIdeal := by
  rw [y.ker_ideal_of_range_eq_singleton hy hc hU]
  have : hU.fromSpec ⁻¹' {c} = {hU.primeIdealOf ⟨c, hcU⟩} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun h ↦ hU.fromSpec.isOpenEmbedding.injective ?_, fun h ↦ h ▸ ?_⟩
    · exact h.trans (hU.fromSpec_primeIdealOf ⟨c, hcU⟩).symm
    · exact hU.fromSpec_primeIdealOf ⟨c, hcU⟩
  rw [this, PrimeSpectrum.vanishingIdeal_singleton]

/-- The ideal of a morphism from a reduced scheme with image a closed point `c`, over an affine
open `U` not containing `c`, is the unit ideal. -/
lemma Hom.ker_ideal_eq_top {T C : Scheme.{u}} (y : T ⟶ C) [IsReduced T] {c : C}
    (hy : Set.range y = {c}) (hc : IsClosed ({c} : Set C)) {U : C.Opens} (hU : IsAffineOpen U)
    (hcU : c ∉ U) : y.ker.ideal ⟨U, hU⟩ = ⊤ := by
  rw [y.ker_ideal_of_range_eq_singleton hy hc hU]
  have : hU.fromSpec ⁻¹' {c} = ∅ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro hq
    exact hcU (hq ▸ (IsAffineOpen.range_fromSpec hU).le ⟨q, rfl⟩)
  rw [this, PrimeSpectrum.vanishingIdeal_empty]

/-- A section in the kernel of `φ.app U` has its germ at `φ t` in the maximal ideal. -/
lemma Hom.germ_mem_maximalIdeal_of_mem_ker {T X : Scheme.{u}} (φ : T ⟶ X) (t : T) (U : X.Opens)
    (ht : φ t ∈ U) {a : Γ(X, U)} (ha : a ∈ RingHom.ker (φ.app U).hom) :
    X.presheaf.germ U (φ t) ht a ∈ maximalIdeal (X.presheaf.stalk (φ t)) := by
  intro hu
  have := hu.map (φ.stalkMap t).hom
  rw [Scheme.Hom.germ_stalkMap_apply, RingHom.mem_ker.mp ha, map_zero] at this
  exact not_isUnit_zero this

/-- The germ at `x` of the restriction `h.appLE U U' a` is the image of the germ of `a` under the
stalk map. -/
lemma Hom.germ_appLE_apply {X X' : Scheme.{u}} (h : X' ⟶ X) {U : X.Opens} {U' : X'.Opens}
    (hU : U' ≤ h ⁻¹ᵁ U) (x : X') (hx : x ∈ U') (a : Γ(X, U)) :
    X'.presheaf.germ U' x hx (h.appLE U U' hU a) =
      h.stalkMap x (X.presheaf.germ U (h x) (hU hx) a) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_res_apply]

end Scheme

namespace ProEtale.CondensedRing

open Scheme

section RationalPoint

variable {k : Type u} [Field k]

/-- The image of a rational point is a single point. -/
lemma RationalPoint.range_left_eq_singleton {Y : Over (Spec (.of k))} (y : RationalPoint Y) :
    Set.range y.left = {y.left (default : Spec (.of k))} := by
  have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  ext z
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨p, hp⟩ ↦ hp ▸ congrArg _ (Subsingleton.elim p _), fun hz ↦ ⟨_, hz.symm⟩⟩

/-- The image of a rational point is a closed point. -/
lemma RationalPoint.isClosed_singleton {Y : Over (Spec (.of k))}
    (y : RationalPoint Y) : IsClosed ({y.left (default : Spec (.of k))} : Set Y.left) := by
  have := isClosedImmersion_of_comp_eq_id Y.hom y.left (Over.w y)
  rw [← RationalPoint.range_left_eq_singleton]
  exact y.left.isClosedEmbedding.isClosed_range

end RationalPoint

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable {c : Correspondence ℓ K} {y : RationalPoint c.C}

/-- Functions vanishing at `x = c₁(y)` pull back along the leg `c` (`c₁` or `c₂`) to functions
vanishing at `y`, as soon as `y ≫ c = x`. -/
lemma ker_map_le_of_comp_eq (h : c.C ⟶ X) (x : RationalPoint X) (hx : y ≫ h = x)
    ⦃U' : c.C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ h.left ⁻¹ᵁ U.1) :
    (x.left.ker.siteIdeal U).map (h.left.appLE U.1 U'.1 hU).hom ≤ y.left.ker.siteIdeal U' := by
  refine (IdealSheafData.ideal_map_appLE_le_ideal_comap x.left.ker h.left ⟨U.1, U.2⟩
    ⟨U'.1, U'.2⟩ hU).trans ?_
  refine (IdealSheafData.comap_le_ker_iff x.left.ker h.left y.left).2 ?_ _
  rw [← Over.comp_left, hx]

namespace IsContractingAt

/-- **The first ideal condition for `c₁`** (blueprint `lemma-normal-cones-contracting-ideals`): for
`c` contracting at `y` and `x = c₁(y)`, functions vanishing at `x` pull back along `c₁` to functions
vanishing at `y`. -/
lemma ker_map_le_c₁ (_hc : c.IsContractingAt y) ⦃U' : c.C.left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄ (hU : U'.1 ≤ c.c₁.left ⁻¹ᵁ U.1) :
    ((y ≫ c.c₁).left.ker.siteIdeal U).map (c.c₁.left.appLE U.1 U'.1 hU).hom ≤
      y.left.ker.siteIdeal U' :=
  ker_map_le_of_comp_eq c.c₁ _ rfl hU

/-- **The first ideal condition for `c₂`** (blueprint `lemma-normal-cones-contracting-ideals`): for
`c` contracting at `y` and `x = c₁(y) = c₂(y)`, functions vanishing at `x` pull back along `c₂` to
functions vanishing at `y`. -/
lemma ker_map_le_c₂ (hc : c.IsContractingAt y) ⦃U' : c.C.left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄ (hU : U'.1 ≤ c.c₂.left ⁻¹ᵁ U.1) :
    ((y ≫ c.c₁).left.ker.siteIdeal U).map (c.c₂.left.appLE U.1 U'.1 hU).hom ≤
      y.left.ker.siteIdeal U' :=
  ker_map_le_of_comp_eq c.c₂ _ hc.comp_c₁_eq_comp_c₂.symm hU

/-- The contraction condition on the ideals of sections over a pair of affine opens
`U' ⊆ c₂⁻¹ U`, for an `n` satisfying the contraction condition on stalks at `y`. -/
lemma ker_map_pow_le_of_le_pow (hc : c.IsContractingAt y) {n : ℕ}
    (hle : ((maximalIdeal
        (X.left.presheaf.stalk (c.c₂.left (y.left (default : Spec (.of k)))))).map
        (c.c₂.left.stalkMap (y.left (default : Spec (.of k)))).hom) ^ n ≤
      ((maximalIdeal
        (X.left.presheaf.stalk (c.c₁.left (y.left (default : Spec (.of k)))))).map
        (c.c₁.left.stalkMap (y.left (default : Spec (.of k)))).hom) ^ (n + 1))
    {U' : c.C.left.Opens} (hU' : IsAffineOpen U') {U : X.left.Opens} (hUa : IsAffineOpen U)
    (hU : U' ≤ c.c₂.left ⁻¹ᵁ U) :
    ((y ≫ c.c₁).left.ker.ideal ⟨U, hUa⟩).map (c.c₂.left.appLE U U' hU).hom ^ n ≤
      y.left.ker.ideal ⟨U', hU'⟩ ^ (n + 1) := by
  set y₀ : c.C.left := y.left (default : Spec (.of k))
  have hy := RationalPoint.range_left_eq_singleton y
  have hy₀ := RationalPoint.isClosed_singleton y
  have : IsReduced (point k).left := inferInstanceAs (IsReduced (Spec (.of k)))
  by_cases hyU : y₀ ∈ U'
  swap
  · rw [y.left.ker_ideal_eq_top hy hy₀ hU' hyU, Ideal.top_pow]
    exact le_top
  set p := hU'.primeIdealOf ⟨y₀, hyU⟩
  rw [y.left.ker_ideal_eq_primeIdealOf hy hy₀ hU' hyU]
  have hp : p.asIdeal.IsMaximal := hU'.primeIdealOf_isMaximal_of_isClosed _ hy₀
  let := c.C.left.presheaf.algebra_section_stalk ⟨y₀, hyU⟩
  have := hU'.isLocalization_stalk ⟨y₀, hyU⟩
  -- `p ^ (n + 1)` is `p`-primary, hence contracted from the stalk.
  have hprim : (p.asIdeal ^ (n + 1)).IsPrimary := by
    refine Ideal.isPrimary_of_isMaximal_radical ?_
    rwa [Ideal.radical_pow p.asIdeal (n := n + 1) (by omega), hp.isPrime.radical]
  have hdisj : Disjoint (p.asIdeal.primeCompl : Set Γ(c.C.left, U'))
      (p.asIdeal ^ (n + 1) : Ideal _) :=
    Set.disjoint_left.mpr fun a ha ha' ↦ ha (Ideal.pow_le_self n.succ_ne_zero ha')
  rw [← IsLocalization.under_map_of_isPrimary_disjoint p.asIdeal.primeCompl
    (c.C.left.presheaf.stalk y₀)
    hprim hdisj, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal,
    ← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  -- In the stalk: `(c₂^* I) 𝒪_{C,y} ⊆ c₂^♯ 𝔪_x`.
  have h₂ : Ideal.map (algebraMap Γ(c.C.left, U') (c.C.left.presheaf.stalk y₀))
      (((y ≫ c.c₁).left.ker.ideal ⟨U, hUa⟩).map (c.c₂.left.appLE U U' hU).hom) ≤
      (maximalIdeal (X.left.presheaf.stalk (c.c₂.left y₀))).map (c.c₂.left.stalkMap y₀).hom := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.comp_apply]
    change c.C.left.presheaf.germ U' y₀ hyU (c.c₂.left.appLE U U' hU a) ∈ _
    rw [Scheme.Hom.germ_appLE_apply]
    refine Ideal.mem_map_of_mem _ ?_
    replace ha : a ∈ (y ≫ c.c₂).left.ker.ideal ⟨U, hUa⟩ := hc.comp_c₁_eq_comp_c₂ ▸ ha
    have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have := isClosedImmersion_of_comp_eq_id X.hom (y ≫ c.c₂).left (Over.w (y ≫ c.c₂))
    rw [Scheme.Hom.ker_apply] at ha
    exact Scheme.Hom.germ_mem_maximalIdeal_of_mem_ker (y ≫ c.c₂).left
      (default : Spec (.of k)) U _ ha
  calc _ ≤ ((maximalIdeal (X.left.presheaf.stalk (c.c₂.left y₀))).map
          (c.c₂.left.stalkMap y₀).hom) ^ n := Ideal.pow_right_mono h₂ n
    _ ≤ ((maximalIdeal (X.left.presheaf.stalk (c.c₁.left y₀))).map
          (c.c₁.left.stalkMap y₀).hom) ^ (n + 1) := hle
    _ ≤ _ := Ideal.pow_right_mono (map_maximalIdeal_le _) _

/-- **The contraction condition on ideals** (blueprint `lemma-normal-cones-contracting-ideals`): for
`c` contracting at `y`, `x = c₁(y)`, `I` the ideal of `x` and `J` the ideal of `y`, there is `n ≥ 1`
with `(c₂^* I)(U')^n ⊆ J(U')^{n+1}` for all affine opens `U' ⊆ c₂⁻¹ U`. -/
lemma ker_map_pow_le (hc : c.IsContractingAt y) : ∃ n : ℕ, 0 < n ∧
    ∀ ⦃U' : c.C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ c.c₂.left ⁻¹ᵁ U.1),
      ((y ≫ c.c₁).left.ker.siteIdeal U).map (c.c₂.left.appLE U.1 U'.1 hU).hom ^ n ≤
        y.left.ker.siteIdeal U' ^ (n + 1) := by
  obtain ⟨n, hn, hle⟩ := hc.exists_le_pow
  exact ⟨n, hn, fun U' U hU ↦ hc.ker_map_pow_le_of_le_pow hle U'.2 U.2 hU⟩

end IsContractingAt

end Correspondence

end ProEtale.CondensedRing

end AlgebraicGeometry
