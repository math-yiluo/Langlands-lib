/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Algebras as unions of finite type subalgebras, and fraction fields as colimits

* `Algebra.directed_adjoin_finset_and_iSup_eq_top` (blueprint `lem-kun-algebra-union`): an
  `R`-algebra is the directed union of its finitely generated subalgebras.
* `Subalgebra.isColimitCocone`: a directed family of subalgebras covering the whole algebra
  is a filtered colimit in `CommRingCat`.
* `Subalgebra.localizationSubalgebra`: for a subalgebra `S` of a domain `B` and a nonzero
  `g ∈ S`, the copy of `S_g` inside `Frac B`.
* `Subalgebra.isFiltered_and_isColimit_localizationSubalgebras` (blueprint
  `lemma-kunneth-finite-direct-image--1`): `Frac B` is the filtered colimit of the `(B_i)_g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- Blueprint `lem-kun-algebra-union`: every `R`-algebra `B` is the filtered union of its
finitely generated `R`-subalgebras `R[s]`, `s` a finite subset of `B`: these are of finite
type, they form a directed family, and their union is `B`.

Proof: `R[s] ∪ R[t] ⊆ R[s ∪ t]`, and each `b ∈ B` lies in `R[{b}]`. -/
theorem directed_adjoin_finset_and_iSup_eq_top :
    (∀ s : Finset B, FiniteType R (adjoin R (s : Set B))) ∧
      Directed (· ≤ ·) (fun s : Finset B ↦ adjoin R (s : Set B)) ∧
      ⨆ s : Finset B, adjoin R (s : Set B) = ⊤ := by
  classical
  refine ⟨fun s ↦ .adjoin_of_finite s.finite_toSet, fun s t ↦ ⟨s ∪ t, ?_, ?_⟩, ?_⟩
  · exact adjoin_mono (by simp)
  · exact adjoin_mono (by simp)
  · refine Algebra.eq_top_iff.2 fun x ↦ ?_
    exact le_iSup (fun s : Finset B ↦ adjoin R (s : Set B)) {x}
      (subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self x)))


end Algebra

namespace Subalgebra

variable {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The diagram in `CommRingCat` given by a set of subalgebras ordered by inclusion. -/
@[simps]
def diagram (D : Set (Subalgebra R A)) : D ⥤ CommRingCat.{u} where
  obj S := CommRingCat.of S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

/-- The cocone with vertex `A` over the diagram of a set of subalgebras. -/
@[simps]
def cocone (D : Set (Subalgebra R A)) : Cocone (diagram D) where
  pt := CommRingCat.of A
  ι := { app S := CommRingCat.ofHom S.1.val.toRingHom }

/-- A directed set of subalgebras ordered by inclusion is a filtered category. -/
theorem isFiltered_of_directedOn {D : Set (Subalgebra R A)} (hD : DirectedOn (· ≤ ·) D)
    (hne : D.Nonempty) : IsFiltered D := by
  have : IsDirectedOrder D := ⟨fun S T ↦ by
    obtain ⟨U, hU, hSU, hTU⟩ := hD S.1 S.2 T.1 T.2
    exact ⟨⟨U, hU⟩, hSU, hTU⟩⟩
  have : Nonempty D := hne.to_subtype
  infer_instance

/-- A directed set `D` of subalgebras of `A` whose union is `A` exhibits `A` as the filtered
colimit of the members of `D` in `CommRingCat`. -/
noncomputable def isColimitCocone {D : Set (Subalgebra R A)} (hD : DirectedOn (· ≤ ·) D)
    (hcov : ∀ x : A, ∃ S ∈ D, x ∈ S) : IsColimit (cocone D) := by
  have := isFiltered_of_directedOn hD (by obtain ⟨S, hS, -⟩ := hcov 0; exact ⟨S, hS⟩)
  have := reflectsColimit_of_reflectsIsomorphisms (diagram D) (forget CommRingCat.{u})
  refine isColimitOfReflects (forget CommRingCat.{u}) (Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ ?_) (fun i x y h ↦ ⟨i, 𝟙 i, ?_⟩))
  · obtain ⟨S, hS, hx⟩ := hcov x
    exact ⟨⟨S, hS⟩, ⟨x, hx⟩, rfl⟩
  · exact Subtype.ext h

section Localization

variable {K : Type*} {B : Type u} [CommRing K] [CommRing B] [IsDomain B] [Algebra K B]

theorem isUnit_algebraMap_fractionRing_powers (S : Subalgebra K B) {g : S} (hg : g ≠ 0)
    (y : Submonoid.powers g) :
    IsUnit (((IsScalarTower.toAlgHom K B (FractionRing B)).comp S.val) y) := by
  obtain ⟨_, n, rfl⟩ := y
  refine IsUnit.mk0 _ ?_
  have hg' : (g : B) ≠ 0 := by simpa using hg
  simp [hg']

/-- For a subalgebra `S` of a domain `B` and a nonzero `g ∈ S`, the `K`-algebra map
`S_g → Frac B`. -/
noncomputable def awayToFractionRing (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Localization.Away g →ₐ[K] FractionRing B :=
  IsLocalization.liftAlgHom (isUnit_algebraMap_fractionRing_powers S hg)

theorem awayToFractionRing_mk' (S : Subalgebra K B) {g : S} (hg : g ≠ 0) (a : S) (n : ℕ) :
    awayToFractionRing S hg (IsLocalization.mk' _ a (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)) =
      algebraMap B (FractionRing B) a / algebraMap B (FractionRing B) g ^ n := by
  have hg' : algebraMap B (FractionRing B) g ≠ 0 := by simpa using hg
  rw [awayToFractionRing, IsLocalization.coe_liftAlgHom, IsLocalization.lift_mk'_spec]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply,
    Subalgebra.coe_val, IsScalarTower.coe_toAlgHom', map_pow]
  exact (mul_div_cancel₀ _ (pow_ne_zero n hg')).symm


/-- `S_g → Frac B` is compatible with the inclusion `S ⊆ B ⊆ Frac B`. -/
@[simp]
theorem awayToFractionRing_algebraMap (S : Subalgebra K B) {g : S} (hg : g ≠ 0) (a : S) :
    awayToFractionRing S hg (algebraMap S (Localization.Away g) a) =
      algebraMap B (FractionRing B) a := by
  rw [awayToFractionRing, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  rfl

theorem awayToFractionRing_injective (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Function.Injective (awayToFractionRing S hg) := by
  rw [awayToFractionRing, IsLocalization.coe_liftAlgHom, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)).eq_iff]
  simp [(IsFractionRing.injective B (FractionRing B)).eq_iff]

/-- The copy of `S_g` inside `Frac B`, for a subalgebra `S` of a domain `B` and a nonzero
`g ∈ S`: the image of `awayToFractionRing`. -/
noncomputable def localizationSubalgebra (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Subalgebra K (FractionRing B) :=
  (awayToFractionRing S hg).range

/-- `localizationSubalgebra S hg` is isomorphic to `S_g`. -/
noncomputable def localizationSubalgebraEquiv (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Localization.Away g ≃ₐ[K] localizationSubalgebra S hg :=
  AlgEquiv.ofInjective _ (awayToFractionRing_injective S hg)

theorem mem_localizationSubalgebra (S : Subalgebra K B) {g : S} (hg : g ≠ 0)
    (x : FractionRing B) : x ∈ localizationSubalgebra S hg ↔
      ∃ (a : S) (n : ℕ),
        x = algebraMap B (FractionRing B) a / algebraMap B (FractionRing B) g ^ n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨a, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) y
    exact ⟨a, n, awayToFractionRing_mk' S hg a n⟩
  · rintro ⟨a, n, rfl⟩
    exact ⟨_, awayToFractionRing_mk' S hg a n⟩


/-- The set of subalgebras `(B_i)_g ⊆ Frac B`, for `B_i` in a set `F` of subalgebras of `B` and
`g ∈ B_i` nonzero. -/
def localizationSubalgebras (F : Set (Subalgebra K B)) : Set (Subalgebra K (FractionRing B)) :=
  {T | ∃ S ∈ F, ∃ (g : S) (hg : g ≠ 0), T = localizationSubalgebra S hg}

theorem directedOn_localizationSubalgebras {F : Set (Subalgebra K B)}
    (hF : DirectedOn (· ≤ ·) F) : DirectedOn (· ≤ ·) (localizationSubalgebras F) := by
  rintro _ ⟨S₁, hS₁, g₁, hg₁, rfl⟩ _ ⟨S₂, hS₂, g₂, hg₂, rfl⟩
  obtain ⟨S, hS, h₁, h₂⟩ := hF S₁ hS₁ S₂ hS₂
  have hg₁' : algebraMap B (FractionRing B) g₁ ≠ 0 := by simpa using hg₁
  have hg₂' : algebraMap B (FractionRing B) g₂ ≠ 0 := by simpa using hg₂
  let g : S := ⟨g₁ * g₂, S.mul_mem (h₁ g₁.2) (h₂ g₂.2)⟩
  have hg : g ≠ 0 := by
    intro h
    have : (g₁ : B) * g₂ = 0 := congrArg Subtype.val h
    simp_all
  refine ⟨localizationSubalgebra S hg, ⟨S, hS, g, hg, rfl⟩, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨a, n, rfl⟩ := (mem_localizationSubalgebra S₁ hg₁ x).1 hx
    refine (mem_localizationSubalgebra S hg _).2
      ⟨⟨a * g₂ ^ n, S.mul_mem (h₁ a.2) (S.pow_mem (h₂ g₂.2) n)⟩, n, ?_⟩
    simp only [g, map_mul, map_pow, mul_pow]
    rw [mul_div_mul_right _ _ (pow_ne_zero n hg₂')]
  · obtain ⟨a, n, rfl⟩ := (mem_localizationSubalgebra S₂ hg₂ x).1 hx
    refine (mem_localizationSubalgebra S hg _).2
      ⟨⟨a * g₁ ^ n, S.mul_mem (h₂ a.2) (S.pow_mem (h₁ g₁.2) n)⟩, n, ?_⟩
    simp only [g, map_mul, map_pow, mul_pow]
    rw [mul_comm (_ ^ n) (_ ^ n), mul_div_mul_right _ _ (pow_ne_zero n hg₁')]

theorem exists_mem_localizationSubalgebras {F : Set (Subalgebra K B)}
    (hF : DirectedOn (· ≤ ·) F) (hcov : ∀ b : B, ∃ S ∈ F, b ∈ S) (x : FractionRing B) :
    ∃ T ∈ localizationSubalgebras F, x ∈ T := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  obtain ⟨Sa, hSa, ha⟩ := hcov a
  obtain ⟨Sb, hSb, hb'⟩ := hcov b
  obtain ⟨S, hS, hSaS, hSbS⟩ := hF Sa hSa Sb hSb
  have hg : (⟨b, hSbS hb'⟩ : S) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb (congrArg Subtype.val h)
  refine ⟨_, ⟨S, hS, _, hg, rfl⟩, (mem_localizationSubalgebra S hg _).2 ⟨⟨a, hSaS ha⟩, 1, ?_⟩⟩
  simp

/-- Blueprint `lemma-kunneth-finite-direct-image--1`: let `B` be a domain which is the directed
union of a set `F` of (finite type) `K`-subalgebras `B_i`. Then `Frac B` is the filtered
colimit in `CommRingCat` of the subrings `(B_i)_g ⊆ Frac B` (`g ∈ B_i` nonzero), ordered by
inclusion; each of them is isomorphic to the localization `(B_i)_g`
(`localizationSubalgebraEquiv`). The index category is small, in the universe of `B`.

Proof: given `(B_i)_g` and `(B_j)_h`, choose `B_k ⊇ B_i, B_j`; then both are contained in
`(B_k)_{gh}`. Each `(B_i)_g` injects into `Frac B`, and every `a / b ∈ Frac B` lies in
`(B_i)_b` for `B_i ∋ a, b`. -/
theorem isFiltered_and_isColimit_localizationSubalgebras {F : Set (Subalgebra K B)}
    (hF : DirectedOn (· ≤ ·) F) (hcov : ∀ b : B, ∃ S ∈ F, b ∈ S) :
    IsFiltered (localizationSubalgebras F) ∧
      Nonempty (IsColimit (Subalgebra.cocone (localizationSubalgebras F))) := by
  have hD := directedOn_localizationSubalgebras hF
  have hcov' := exists_mem_localizationSubalgebras hF hcov
  refine ⟨Subalgebra.isFiltered_of_directedOn hD ?_, ⟨Subalgebra.isColimitCocone hD hcov'⟩⟩
  obtain ⟨T, hT, -⟩ := hcov' 0
  exact ⟨T, hT⟩


end Localization

end Subalgebra

end
