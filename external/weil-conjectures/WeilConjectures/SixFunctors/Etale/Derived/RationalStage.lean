/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralIdempotentComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import WeilConjectures.SixFunctors.ClosedImmersionStages

/-!
# The rational coefficient stage `Dᵇc(X, E)`

This file formalises *rationalization and coefficient-field extension*:
`Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ]` has the same objects as the integral category and morphisms
`Hom_{𝒪_E}(-, -) ⊗_{𝒪_E} E`; it is idempotent complete, so that the canonical functor to its Karoubi
envelope is an equivalence; `𝒪_E`-linear triangulated functors and natural transformations between
integral categories transport to the rational ones; every object of `Dᵇc(X, E)` is the
rationalization of an integral object (a lattice), and every morphism is `ϖ⁻ᴺ u` for an integral
morphism `u`.

## Modelling choices

* The integral category `Dᵇc(X, 𝒪_E)` is the full subcategory of the category
  `D_comp(X_ét, 𝒪_E)` of derived complete objects (`DerivedCategoryDerivedCompleteIntegral`) cut
  out by `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`. Its `Hom` groups
  are those of `D_comp(X_ét, 𝒪_E)`.
* The rational category `Dᵇc(X, E)` is the full subcategory
  `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational` of the rationalization
  `D_comp(X_ét, E)` of `D_comp(X_ét, 𝒪_E)` (`DerivedCategoryDerivedCompleteRational`, the
  Verdier quotient by the objects killed by a nonzero element of `𝒪_E`), consisting of the
  objects isomorphic to the image of an object of `Dᵇc(X, 𝒪_E)`. Since the functor induced on
  rationalizations by the fully faithful inclusion `Dᵇc(X, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` is fully
  faithful (`CategoryTheory.Rationalization.full_map`,
  `CategoryTheory.Rationalization.faithful_map`), this is the rationalization
  `Dᵇc(X, 𝒪_E)[1/ϖ]` of the integral category, and its `Hom` groups are those of the
  rationalization of `D_comp(X_ét, 𝒪_E)`.
* The descent of objects to lattices is then the definition of `boundedConstructibleRational`,
  and the description of the morphisms is the general computation of the `Hom` groups of a
  rationalization (`CategoryTheory.Rationalization.tensorHomEquiv`,
  `CategoryTheory.Rationalization.exists_eq_inv_pow_smul_map`), using that `𝒪_E` is a discrete
  valuation ring (`PadicAlgCl.isDiscreteValuationRing_integers`).
* Idempotent completeness belongs to another part of the blueprint and is only stated here
  (`AlgebraicGeometry.Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational`).
  The Karoubi envelope carries no triangulated structure in this repository, so the equivalence
  with the Karoubi envelope is stated as an equivalence of categories.

## Main results

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` : the morphisms
  of `Dᵇc(X, E)` between rationalizations of integral objects are `Hom_{𝒪_E} ⊗_{𝒪_E} E`.
- `AlgebraicGeometry.Etale.DerivedCategory.exists_iso_of_boundedConstructibleRational` : every
  object of `Dᵇc(X, E)` is the rationalization of an object of `Dᵇc(X, 𝒪_E)`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational_exists_eq_inv_pow_smul` :
  every morphism of `Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism `u`.
- `AlgebraicGeometry.Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational` :
  `Dᵇc(X, E)` is equivalent to its Karoubi envelope.
- `AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` : `𝒪_E`-linear triangulated
  functors and natural transformations transport to `E`-linear ones on rationalizations.
-/

@[expose] public section

universe w u

open CategoryTheory Limits TensorProduct

/-- In a discrete valuation ring every nonzero element divides a power of a uniformizer. -/
lemma IsDiscreteValuationRing.exists_mul_eq_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (N : ℕ) (a : R), x * a = ϖ ^ N := by
  obtain ⟨N, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  exact ⟨N, ↑v⁻¹, by rw [mul_right_comm, Units.mul_inv, one_mul]⟩

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- The ring of integers `𝒪_E` of a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` is a discrete
valuation ring. -/
instance isDiscreteValuationRing_integers : IsDiscreteValuationRing (integers l E) where
  not_a_field' := maximalIdeal_integers_ne_bot l E

/-- The universe `u + 1` copy `Shrink 𝒪_E` of the ring of integers of a finite extension `E` of
`ℚ_ℓ` inside `ℚ̄_ℓ` is a discrete valuation ring. -/
instance isDiscreteValuationRing_shrink [Small.{u + 1} E] :
    IsDiscreteValuationRing (Shrink.{u + 1} (integers l E)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (shrinkRingEquiv.{w, u} l E)

end PadicAlgCl

namespace AlgebraicGeometry

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

namespace Etale.DerivedCategory

variable (X : Scheme.{u})

/-- Morphisms: the morphisms of `Dᵇc(X, E)` between the rationalizations of two objects `L`, `L'` of
`Dᵇc(X, 𝒪_E)` are `Hom(L, L') ⊗_{𝒪_E} E`, through `a ⊗ f ↦ a • f`. -/
noncomputable def boundedConstructibleRationalHomEquiv
    (L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    E ⊗[Shrink.{u + 1} (PadicAlgCl.integers l E)] (L ⟶ L') ≃ₗ[E]
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ⟶
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L') :=
  Rationalization.tensorHomEquiv _ E L L'

/-- Morphisms: the identification of
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` sends `a ⊗ f` to
`a • f`. -/
@[simp]
lemma boundedConstructibleRationalHomEquiv_tmul
    {L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E} (a : E)
    (f : L ⟶ L') :
    boundedConstructibleRationalHomEquiv l E X L L' (a ⊗ₜ f) =
      a • (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map f :=
  Rationalization.tensorHomEquiv_tmul _ E a f

/-- Objects: the rationalization of an object of `Dᵇc(X, 𝒪_E)` is an object of `Dᵇc(X, E)`. -/
lemma boundedConstructibleRational_obj
    {L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (hL : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L)) :
    boundedConstructibleRational l E X
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L) :=
  ⟨L, hL, ⟨Iso.refl _⟩⟩

/-- Descent of objects: every object of `Dᵇc(X, E)` is the rationalization of an object of
`Dᵇc(X, 𝒪_E)` (a lattice). -/
theorem exists_iso_of_boundedConstructibleRational
    (K : (boundedConstructibleRational l E X).FullSubcategory) :
    ∃ L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E,
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
      Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K.obj) :=
  K.property

/-- Clearing denominators: for a uniformizer `ϖ` of `𝒪_E`, every morphism `φ : K ⟶ K'` of
`Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism `u : L ⟶ L'` between lattices `L`, `L'` of `K`, `K'`
in `Dᵇc(X, 𝒪_E)`. -/
theorem boundedConstructibleRational_exists_eq_inv_pow_smul
    {ϖ : Shrink.{u + 1} (PadicAlgCl.integers l E)} (hϖ : Irreducible ϖ)
    {K K' : (boundedConstructibleRational l E X).FullSubcategory} (φ : K ⟶ K') :
    ∃ (L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E)
      (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K.obj)
      (e' : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L' ≅ K'.obj)
      (N : ℕ) (u : L ⟶ L'),
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L') ∧
      φ.hom = e.inv ≫ ((algebraMap _ E ϖ)⁻¹ ^ N •
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map u) ≫ e'.hom := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.property
  obtain ⟨L', hL', ⟨e'⟩⟩ := K'.property
  obtain ⟨N, u, h⟩ := Rationalization.exists_eq_inv_pow_smul_map E
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    (fun m hm ↦ IsDiscreteValuationRing.exists_mul_eq_pow (nonZeroDivisors.ne_zero hm) hϖ)
    (e.hom ≫ φ.hom ≫ e'.inv)
  refine ⟨L, L', e, e', N, u, hL, hL', ?_⟩
  rw [← h]
  simp

/-- `Dᵇc(X, 𝒪_E)` is stable under retracts in `D(X_ét, 𝒪_E)`: derived completeness, bounded
constructibility and Tor amplitude are, and the reductions of a retract are retracts of the
reductions. -/
instance isStableUnderRetracts_boundedConstructibleIntegral :
    (boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X).IsStableUnderRetracts
    where
  of_retract {M N} e hN := by
    obtain ⟨hc, a, b, h⟩ := hN
    exact ⟨(_root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).prop_of_retract
      e hc, a, b, fun n ↦ ⟨(boundedConstructible _ X).prop_of_retract (e.map _) (h n).1,
      (torAmplitudeIn _ X a b).prop_of_retract (e.map _) (h n).2⟩⟩

/-- Over a field `A`, if `a ≠ 0` and `a⁻ᴺ • a⁻ᴺ • x = a⁻ᴺ • y`, then `x = aᴺ • y`. -/
private lemma eq_pow_smul_of_inv_pow_smul {A V : Type*} [Field A] [AddCommGroup V] [Module A V]
    {a : A} (ha : a ≠ 0) (N : ℕ) {x y : V} (h : a⁻¹ ^ N • a⁻¹ ^ N • x = a⁻¹ ^ N • y) :
    x = a ^ N • y := by
  have h' := congrArg (fun z ↦ a ^ N • a ^ N • z) h
  simp only [smul_smul, ← mul_pow, mul_inv_cancel₀ ha, one_pow] at h'
  simpa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha] using h'

/-- **The lattice lemma** (the non-formal input to idempotent completeness). Let `L ∈ Dᵇc(X, 𝒪_E)`
and `u : L ⟶ L` with `u ≫ u = ϖᴺ • u`, so that `ϖ⁻ᴺ u` is an idempotent of the rationalization of
`L`. Then there is another lattice `L'` of the rationalization of `L` in `Dᵇc(X, 𝒪_E)` on which this
idempotent is integral: an idempotent `ε` of `L'` corresponding to `ϖ⁻ᴺ u`.

In the theory of `ℓ`-adic sheaves this follows from the existence of the rationalized standard
`t`-structure on `Dᵇc(X, E)` (Ekedahl): the image of `ϖ⁻ᴺ u` has a lattice, and so does its
complement.

The lemma is equivalent to
`AlgebraicGeometry.Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational` and is
not formal. Over `R_N = 𝒪_E[u]/(u² - ϖᴺu)` the perfect complexes have all the structure used in
this file, but the idempotent `(1, 0)` of `R_N[1/ϖ] = E × E` has no lattice. Cones and clearing
denominators only produce lattices of `A ⊕ A⟦n⟧` (`n ≥ 1`) for the image `A` of `ϖ⁻ᴺ u`. A proof
needs truncations or images on the étale integral stage for an arbitrary scheme `X`, or a comparison
with the pro-étale model; neither is available here. -/
theorem exists_boundedConstructibleIntegral_idempotent
    {ϖ : Shrink.{u + 1} (PadicAlgCl.integers l E)} (hϖ : Irreducible ϖ)
    {L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (hL : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L))
    (N : ℕ) (u : L ⟶ L) (hu : u ≫ u = ϖ ^ N • u) :
    ∃ (L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) (ε : L' ⟶ L')
      (i : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L' ≅
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L),
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L') ∧ ε ≫ ε = ε ∧
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map ε ≫ i.hom =
        i.hom ≫ ((algebraMap _ E ϖ)⁻¹ ^ N •
          (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map u) :=
  sorry

/-- The rationalization `Dᵇc(X, E)` of `Dᵇc(X, 𝒪_E)` is idempotent complete.

An idempotent `p` of `K ∈ Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral `u` on a lattice `L` of `K`, and
after multiplying `u` by a power of `ϖ`, `u ≫ u = ϖᴺ • u` holds integrally. By the lattice lemma
(`AlgebraicGeometry.Etale.DerivedCategory.exists_boundedConstructibleIntegral_idempotent`), `p`
comes from an idempotent `ε` of another lattice `L'`, which splits in the idempotent complete
category `D_comp(X_ét, 𝒪_E)`; its image is a retract of `L'`, hence lies in `Dᵇc(X, 𝒪_E)`, and its
rationalization is an image of `p`. -/
theorem isIdempotentComplete_boundedConstructibleRational :
    IsIdempotentComplete (boundedConstructibleRational l E X).FullSubcategory := by
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Shrink.{u + 1} (PadicAlgCl.integers l E))
  have hϖM := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have hdiv : ∀ m ∈ nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)),
      ∃ (N : ℕ) (a : Shrink.{u + 1} (PadicAlgCl.integers l E)), m * a = ϖ ^ N :=
    fun m hm ↦ IsDiscreteValuationRing.exists_mul_eq_pow (nonZeroDivisors.ne_zero hm) hϖ
  set Q := DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E
  have ha : algebraMap _ E ϖ ≠ 0 := (IsLocalization.map_units E ⟨ϖ, hϖM⟩).ne_zero
  refine ⟨fun K p hp ↦ ?_⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := K.property
  -- `p` is `ϖ⁻ᴺ u` on the lattice `L`
  obtain ⟨N, u, hφ⟩ := Rationalization.exists_eq_inv_pow_smul_map E hϖM hdiv
    (e.hom ≫ p.hom ≫ e.inv)
  have hφφ : (e.hom ≫ p.hom ≫ e.inv) ≫ (e.hom ≫ p.hom ≫ e.inv) = e.hom ≫ p.hom ≫ e.inv := by
    have hp' : p.hom ≫ p.hom = p.hom := congrArg (fun f ↦ f.hom) hp
    simp [reassoc_of% hp']
  -- integrally, `u ≫ u = ϖᴺ • u` up to torsion
  have hQ : Q.map (u ≫ u) = Q.map (ϖ ^ N • u) := by
    rw [hφ, Linear.smul_comp, Linear.comp_smul] at hφφ
    rw [Functor.map_comp, Functor.map_smul,
      eq_pow_smul_of_inv_pow_smul ha N hφφ, ← map_pow, algebraMap_smul]
  obtain ⟨m, hm, hm'⟩ := (Rationalization.map_eq_map_iff _ _).1 hQ
  obtain ⟨K₀, b, hb⟩ := hdiv m hm
  let u' := ϖ ^ K₀ • u
  have hu' : u' ≫ u' = ϖ ^ (N + K₀) • u' := by
    have h₁ : (ϖ ^ K₀ * ϖ ^ K₀) • (u ≫ u) = (ϖ ^ K₀ * ϖ ^ K₀ * ϖ ^ N) • u := by
      rw [← hb, mul_comm m b, ← mul_assoc, mul_smul, hm', ← mul_smul, ← mul_smul, mul_assoc,
        mul_assoc, mul_assoc]
    simp only [u', Linear.smul_comp, Linear.comp_smul, smul_smul, pow_add] at h₁ ⊢
    rw [h₁]
    congr 1
    ring
  have hφ' : e.hom ≫ p.hom ≫ e.inv = (algebraMap _ E ϖ)⁻¹ ^ (N + K₀) • Q.map u' := by
    rw [hφ, Functor.map_smul, ← algebraMap_smul E (ϖ ^ K₀), smul_smul, map_pow, pow_add,
      mul_assoc, ← mul_pow, inv_mul_cancel₀ ha, one_pow, mul_one]
  -- the lattice lemma, and the splitting in `D_comp(X_ét, 𝒪_E)`
  obtain ⟨L', ε, i, hL', hε, hεi⟩ :=
    exists_boundedConstructibleIntegral_idempotent l E X hϖ hL (N + K₀) u' hu'
  obtain ⟨A, r, hr⟩ := retract_of_isIdempotentComplete L' ε hε
  have hA : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj A) :=
    (boundedConstructibleIntegral _ X).prop_of_retract (r.map _) hL'
  refine ⟨⟨Q.obj A, boundedConstructibleRational_obj l E X hA⟩,
    ObjectProperty.homMk (Q.map r.i ≫ i.hom ≫ e.hom),
    ObjectProperty.homMk (e.inv ≫ i.inv ≫ Q.map r.r), ?_, ?_⟩
  · ext
    simp [← Functor.map_comp]
  · ext
    have : Q.map r.r ≫ Q.map r.i ≫ i.hom = i.hom ≫ (e.hom ≫ p.hom ≫ e.inv) := by
      rw [← Functor.map_comp_assoc, hr, hεi, hφ']
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Category.assoc]
    rw [reassoc_of% this]
    simp

/-- Idempotent completeness: `Dᵇc(X, E)` is idempotent complete, so that the canonical functor to
its Karoubi envelope `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleRational` is an
equivalence. -/
theorem isEquivalence_toKaroubi_boundedConstructibleRational :
    (Idempotents.toKaroubi (boundedConstructibleRational l E X).FullSubcategory).IsEquivalence :=
  have := isIdempotentComplete_boundedConstructibleRational l E X
  Rationalization.isEquivalence_toKaroubi _

/-- Transport of functors and natural transformations: an `𝒪_E`-linear triangulated functor `F`
between derived complete integral categories induces an `E`-linear functor `Rationalization.map _ F`
between the rational categories, and a natural transformation `τ : F ⟶ G` induces a natural
transformation between the induced functors, compatible with `τ` on rationalizations of integral
objects. -/
theorem rationalization_transport {Y : Scheme.{u}}
    {F G : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))]
    [G.CommShift ℤ] [G.IsTriangulated] [G.Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))]
    (τ : F ⟶ G) :
    (Rationalization.map (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) F).Linear E ∧
      ∃ τ' : Rationalization.map (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) F ⟶
          Rationalization.map (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) G,
        ∀ L, (Rationalization.mapFac
            (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) F).inv.app L ≫
          τ'.app ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L) ≫
            (Rationalization.mapFac
              (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) G).hom.app L =
          (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map (τ.app L) :=
  ⟨inferInstance, Rationalization.mapNatTrans _ τ, fun L ↦ by
    rw [Rationalization.mapFac_hom_naturality, Iso.inv_hom_id_app_assoc]⟩

end Etale.DerivedCategory

end AlgebraicGeometry
