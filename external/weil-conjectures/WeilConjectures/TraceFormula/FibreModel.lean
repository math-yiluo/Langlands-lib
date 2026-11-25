/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeFrobenius
public import WeilConjectures.TraceFormula.FixedPoint

/-!
# The fibres of a morphism of models at Frobenius-fixed points

Let `k₀ = 𝔽_q` be a finite field, `k` an algebraically closed field containing `k₀`, and
`f : X ⟶ Y` a morphism of schemes over `Spec k` which is the base change of a morphism
`f₀ : X₀ ⟶ Y₀` of `k₀`-schemes and commutes with the model Frobenii `Φ_X`, `Φ_Y`. Let `m ≥ 1`
and `y` a rational point of `Y` fixed by `Φ_Y^m`. The fibre `Z = X ×_{Y, y} Spec k` carries the
restriction `Φ_Z` of `Φ_X^m` (`ProEtale.CondensedRing.fibreFrobenius`).

The point `y` descends to a point `y₀ : Spec 𝔽_{q^m} ⟶ Y₀` of the fixed field
`𝔽_{q^m} = {a ∈ k | a ^ (q ^ m) = a}` (`ProEtale.CondensedRing.frobeniusFixedField`), and `Z` is
the base change of `Z₀ = X₀ ×_{Y₀, y₀} Spec 𝔽_{q^m}` along `Spec k ⟶ Spec 𝔽_{q^m}`, with `Φ_Z` the
base change of the `q^m`-power Frobenius of `Z₀` (blueprint
`lemma-comparison-via-relative-frobenius` (4), and `lemma-comparison-via-relative-frobenius--4`
(2)).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.pullbackMap`: the Frobenius of a fibre product is
  induced by the Frobenii of its factors.
- `AlgebraicGeometry.Scheme.exists_specMap_algebraMap_comp_eq`: a field point fixed by a ring
  endomorphism `ψ` descends to every subfield containing the elements fixed by `ψ`.
- `AlgebraicGeometry.ProEtale.CondensedRing.natCard_frobeniusFixedField`: the fixed field of
  `σ^m` has `q ^ m` elements.
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.isModelFrobenius_fibreFrobenius`:
  the restriction `Φ_Z` is the model Frobenius of `Z₀ = X₀ ×_{Y₀, y₀} Spec 𝔽_{q^m}`.
- `ProEtale.CondensedRing.IsModelFrobenius.exists_isModelFrobenius_fibreFrobenius`:
  the existence statement, with a model locally of finite type.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Frobenius on affine schemes of fields and on fibre products -/

namespace Scheme.Hom.IsFrobenius

/-- The identity of `Spec R` is the `q`-power Frobenius if every element of `R` satisfies
`a ^ q = a`, for instance for `R = 𝔽_q`. -/
lemma id_spec {R : CommRingCat.{u}} {q : ℕ} (h : ∀ a : R, a ^ q = a) :
    Scheme.Hom.IsFrobenius (𝟙 (Spec R)) q := by
  intro S t φ hφ
  obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = t := ⟨_, Spec.map_preimage t⟩
  rw [Category.comp_id, ← Spec.map_comp]
  congr 1
  ext a
  simp [hφ, ← map_pow, h]

/-- The `q`-power Frobenius of a fibre product `X ×_S Y` is induced by the `q`-power Frobenii
of `X` and `Y` (blueprint `lemma-comparison-via-relative-frobenius`). -/
lemma pullbackMap {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {FX : X ⟶ X} {FY : Y ⟶ Y}
    {FS : S ⟶ S} {q : ℕ} (hFX : FX.IsFrobenius q) (hFY : FY.IsFrobenius q)
    (h₁ : f ≫ FS = FX ≫ f) (h₂ : g ≫ FS = FY ≫ g) :
    (pullback.map f g f g FX FY FS h₁ h₂).IsFrobenius q := by
  intro R t φ hφ
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hFX _ φ hφ, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hFY _ φ hφ, Category.assoc]

end Scheme.Hom.IsFrobenius

/-! ### Descent of fixed field points -/

/-- A point `g : Spec Ω ⟶ X` with values in a field `Ω` which is fixed by `Spec ψ` for a ring
endomorphism `ψ` of `Ω` descends to every subfield `L ⊆ Ω` containing the elements fixed by
`ψ`: the embedding `κ(x) ↪ Ω` of the residue field takes values in `L`
(blueprint `lemma-comparison-via-relative-frobenius`). -/
theorem Scheme.exists_specMap_algebraMap_comp_eq {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (ψ : Ω →+* Ω) (L : Subfield Ω) (hL : ∀ a, ψ a = a → a ∈ L) (g : Spec (.of Ω) ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom ψ) ≫ g = g) :
    ∃ g₀ : Spec (.of L) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ g₀ = g := by
  obtain ⟨φ, hφ⟩ := exists_eq_specMap_comp_fromSpecResidueField g
    (Set.mem_range_self (default : Spec (.of Ω)))
  rw [hφ, specMap_comp_specMap_comp_fromSpecResidueField_eq_iff] at hg
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict L
    fun a ↦ hL _ (congrArg (fun χ ↦ χ.hom a) hg))) ≫ X.fromSpecResidueField _, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  refine Eq.trans ?_ hφ.symm
  congr 2

namespace ProEtale.CondensedRing

/-! ### The fixed field of a power of the arithmetic Frobenius -/

section FixedField

variable (k₀ k : Type u) [Field k₀] [Fintype k₀] [Field k] [Algebra k₀ k]

/-- The fixed field `𝔽_{q^m} = {a ∈ k | a ^ (q ^ m) = a}` of the `m`-th power of the arithmetic
Frobenius `σ : a ↦ a ^ q` of `k` over `k₀ = 𝔽_q` (blueprint
`lemma-comparison-via-relative-frobenius`). -/
def frobeniusFixedField (m : ℕ) : Subfield k :=
  RingHom.eqLocusField ((FiniteField.frobeniusAlgHom k₀ k ^ m : k →ₐ[k₀] k) : k →+* k)
    (RingHom.id k)

variable {k₀ k}

lemma mem_frobeniusFixedField_iff {m : ℕ} {a : k} :
    a ∈ frobeniusFixedField k₀ k m ↔ a ^ (Nat.card k₀ ^ m) = a := by
  rw [← frobeniusAlgHom_pow_apply (k₀ := k₀) m a]
  rfl

/-- The elements of the fixed field `𝔽_{q^m}` satisfy `a ^ (q ^ m) = a`. -/
lemma frobeniusFixedField_pow_eq {m : ℕ} (a : frobeniusFixedField k₀ k m) :
    a ^ (Nat.card k₀ ^ m) = a :=
  Subtype.ext (mem_frobeniusFixedField_iff.1 a.2)

/-- For `m ≥ 1` the fixed field `𝔽_{q^m}` is finite: its elements are roots of
`X ^ (q ^ m) - X`. -/
instance finite_frobeniusFixedField {m : ℕ} [NeZero m] :
    Finite (frobeniusFixedField k₀ k m) := by
  classical
  have hq : 1 < Nat.card k₀ ^ m := Nat.one_lt_pow (NeZero.ne m) Finite.one_lt_card
  have hf := FiniteField.X_pow_card_sub_X_ne_zero k hq
  refine Set.Finite.to_subtype ((Polynomial.X ^ (Nat.card k₀ ^ m) - Polynomial.X :
    Polynomial k).roots.toFinset.finite_toSet.subset fun a ha ↦ ?_)
  have h := mem_frobeniusFixedField_iff.1 ha
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hf,
    Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    sub_eq_zero]
  exact h

/-- For `k` algebraically closed and `m ≥ 1`, the fixed field of `σ^m` has `q ^ m` elements: it
is the image of an embedding of the degree `m` extension of `k₀` (blueprint
`lemma-comparison-via-relative-frobenius`). -/
theorem natCard_frobeniusFixedField [IsAlgClosed k] {m : ℕ} (hm : m ≠ 0) :
    Nat.card (frobeniusFixedField k₀ k m) = Nat.card k₀ ^ m := by
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  let := Fintype.ofFinite (FiniteField.galoisExtension k₀ m)
  let ι : FiniteField.galoisExtension k₀ m →ₐ[k₀] k := IsAlgClosed.lift
  have hE : Fintype.card (FiniteField.galoisExtension k₀ m) = Nat.card k₀ ^ m := by
    rw [← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k₀ m hm]
  rw [← FiniteField.nat_card_galoisExtension k₀ m hm,
    ← Nat.card_range_of_injective ι.toRingHom.injective]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
  rw [mem_frobeniusFixedField_iff, ← hE]
  exact FiniteField.pow_card_eq_self_iff_mem_range ι.toRingHom

end FixedField

/-! ### The fibre and its Frobenius -/

section Fibre

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y}

/-- The underlying morphism of a morphism to the base point is the structure morphism. -/
lemma left_eq_hom_of_point {T : Over (Spec (.of k))} (g : T ⟶ point k) : g.left = T.hom := by
  rw [toPoint_ext g (toPoint T), toPoint_left]

/-- The restriction `Φ_Z` of `Φ_X^m` to the fibre `Z = X ×_{Y, y} Spec k` of `f : X ⟶ Y` at a
rational point `y` fixed by `Φ_Y^m` (blueprint `lemma-comparison-via-relative-frobenius` (4),
`lemma-comparison-via-relative-frobenius--4`). -/
noncomputable def fibreFrobenius (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY) (m : ℕ)
    (y : RationalPoint Y) (hy : y ≫ frobeniusIterate ΦY m = y) : pullback f y ⟶ pullback f y :=
  pullback.lift (pullback.fst f y ≫ frobeniusIterate ΦX m) (pullback.snd f y) (by
    rw [Category.assoc, frobeniusIterate_comp_of_comp hf, ← Category.assoc, pullback.condition,
      Category.assoc, hy])

/-- `Φ_Z ≫ i = i ≫ Φ_X^m` for the inclusion `i : Z ⟶ X` of the fibre. -/
@[reassoc (attr := simp)]
lemma fibreFrobenius_fst (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY) (m : ℕ) (y : RationalPoint Y)
    (hy : y ≫ frobeniusIterate ΦY m = y) :
    fibreFrobenius f hf m y hy ≫ pullback.fst f y = pullback.fst f y ≫ frobeniusIterate ΦX m :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fibreFrobenius_snd (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY) (m : ℕ) (y : RationalPoint Y)
    (hy : y ≫ frobeniusIterate ΦY m = y) :
    fibreFrobenius f hf m y hy ≫ pullback.snd f y = pullback.snd f y :=
  pullback.lift_snd _ _ _

variable {k₀ : Type u} [Field k₀] [Fintype k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}}
  {fX₀ : X₀ ⟶ Spec (.of k₀)} {fY₀ : Y₀ ⟶ Spec (.of k₀)} {pX : X.left ⟶ X₀} {pY : Y.left ⟶ Y₀}

/-- The rational point `y` of `Y = Y₀ ×_{k₀} k` fixed by `Φ_Y^m` descends to a point
`y₀ : Spec 𝔽_{q^m} ⟶ Y₀` of the model, with `y = (y₀ ×_{k₀} k) ∘ Spec(𝔽_{q^m} ⊆ k)` on
underlying schemes (blueprint `lemma-comparison-via-relative-frobenius` (4)). -/
noncomputable def IsModelFrobenius.descendedPoint (hY : IsModelFrobenius ΦY fY₀ pY) {m : ℕ}
    (y : RationalPoint Y) (hy : y ≫ frobeniusIterate ΦY m = y) :
    Spec (.of (frobeniusFixedField k₀ k m)) ⟶ Y₀ :=
  (Scheme.exists_specMap_algebraMap_comp_eq _ (frobeniusFixedField k₀ k m) (fun _ h ↦ h)
    (y.left ≫ pY) ((hY.comp_frobeniusIterate_left_eq_iff m y.left).1
      (congrArg CommaMorphism.left hy))).choose

@[reassoc]
lemma IsModelFrobenius.specMap_comp_descendedPoint (hY : IsModelFrobenius ΦY fY₀ pY) {m : ℕ}
    (y : RationalPoint Y) (hy : y ≫ frobeniusIterate ΦY m = y) :
    Spec.map (CommRingCat.ofHom (algebraMap (frobeniusFixedField k₀ k m) k)) ≫
      hY.descendedPoint y hy = y.left ≫ pY :=
  (Scheme.exists_specMap_algebraMap_comp_eq _ (frobeniusFixedField k₀ k m) (fun _ h ↦ h)
    (y.left ≫ pY) ((hY.comp_frobeniusIterate_left_eq_iff m y.left).1
      (congrArg CommaMorphism.left hy))).choose_spec

/-- The comparison map `p_Z : Z ⟶ Z₀ = X₀ ×_{Y₀, y₀} Spec 𝔽_{q^m}` from the fibre of `f` at `y`
to the fibre of the model `f₀` at the descended point `y₀` (blueprint
`lemma-comparison-via-relative-frobenius`). -/
noncomputable def IsModelFrobenius.fibreModelMap (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y}
    {f₀ : X₀ ⟶ Y₀} (hfp : f.left ≫ pY = pX ≫ f₀) {m : ℕ} (y : RationalPoint Y)
    (hy : y ≫ frobeniusIterate ΦY m = y) :
    (pullback f y).left ⟶ pullback f₀ (hY.descendedPoint y hy) :=
  pullback.lift ((pullback.fst f y).left ≫ pX)
    ((pullback f y).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ k))) (by
      rw [Category.assoc, ← hfp, ← Category.assoc, ← Over.comp_left, pullback.condition,
        Over.comp_left, Category.assoc, Category.assoc, specMap_comp_descendedPoint,
        left_eq_hom_of_point])

@[reassoc (attr := simp)]
lemma IsModelFrobenius.fibreModelMap_fst (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y}
    {f₀ : X₀ ⟶ Y₀} (hfp : f.left ≫ pY = pX ≫ f₀) {m : ℕ} (y : RationalPoint Y)
    (hy : y ≫ frobeniusIterate ΦY m = y) :
    hY.fibreModelMap hfp y hy ≫ pullback.fst _ _ = (pullback.fst f y).left ≫ pX :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma IsModelFrobenius.fibreModelMap_snd (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y}
    {f₀ : X₀ ⟶ Y₀} (hfp : f.left ≫ pY = pX ≫ f₀) {m : ℕ} (y : RationalPoint Y)
    (hy : y ≫ frobeniusIterate ΦY m = y) :
    hY.fibreModelMap hfp y hy ≫ pullback.snd _ _ =
      (pullback f y).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ k)) :=
  pullback.lift_snd _ _ _

omit [Fintype k₀] in
/-- For models `X = X₀ ×_{k₀} k`, `Y = Y₀ ×_{k₀} k` and a base change `f` of a `k₀`-morphism
`f₀`, the square `f ∘ p_X = p_Y ∘ f₀` is cartesian: `X = X₀ ×_{Y₀} Y`. -/
lemma IsModelFrobenius.isPullback_left (hX : IsModelFrobenius ΦX fX₀ pX)
    (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀}
    (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀) : IsPullback f.left pX pY f₀ := by
  refine IsPullback.of_right ?_ hfp hY.isPullback.flip
  rw [Over.w f, h₀]
  exact hX.isPullback.flip

/-- The fibre `Z = X ×_{Y, y} Spec k` is the base change of `Z₀ = X₀ ×_{Y₀, y₀} Spec 𝔽_{q^m}`
along `Spec k ⟶ Spec 𝔽_{q^m}` (blueprint `lemma-comparison-via-relative-frobenius` (4)). -/
lemma IsModelFrobenius.isPullback_fibreModelMap (hX : IsModelFrobenius ΦX fX₀ pX)
    (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀}
    (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀) {m : ℕ} (y : RationalPoint Y)
    (hy : y ≫ frobeniusIterate ΦY m = y) :
    IsPullback (hY.fibreModelMap hfp y hy) (pullback f y).hom
      (pullback.snd f₀ (hY.descendedPoint y hy))
      (Spec.map (CommRingCat.ofHom (algebraMap (frobeniusFixedField k₀ k m) k))) := by
  have hZ := (IsPullback.of_hasPullback f y).map (Over.forget _)
  simp only [Over.forget_map, left_eq_hom_of_point] at hZ
  have houter := hZ.paste_horiz (hX.isPullback_left hY hfp h₀).flip
  rw [← hY.specMap_comp_descendedPoint y hy] at houter
  refine IsPullback.of_right ?_ (hY.fibreModelMap_snd hfp y hy)
    (IsPullback.of_hasPullback _ _)
  rw [fibreModelMap_fst]
  exact houter

/-- **The fibres of a morphism of models are models** (blueprint
`lemma-comparison-via-relative-frobenius` (4), side clause;
`lemma-comparison-via-relative-frobenius--4` (2)). Let `f : X ⟶ Y` be the base change of a
`k₀`-morphism `f₀ : X₀ ⟶ Y₀` commuting with the model Frobenii, `m ≥ 1`, and `y` a rational point of
`Y` fixed by `Φ_Y^m`, descending to `y₀ : Spec 𝔽_{q^m} ⟶ Y₀`. Then the restriction `Φ_Z` of `Φ_X^m`
to the fibre `Z = X ×_{Y, y} Spec k` is the model Frobenius of `Z₀ = X₀ ×_{Y₀, y₀} Spec 𝔽_{q^m}`
over `𝔽_{q^m}`: `Z = Z₀ ×_{𝔽_{q^m}} k` and `Φ_Z` is the base change of the `q^m`-power Frobenius of
`Z₀`, which is induced by `F_{X₀}^m`. -/
theorem IsModelFrobenius.isModelFrobenius_fibreFrobenius {m : ℕ} [NeZero m] [IsAlgClosed k]
    (hX : IsModelFrobenius ΦX fX₀ pX) (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y}
    (hf : ΦX ≫ f = f ≫ ΦY) {f₀ : X₀ ⟶ Y₀} (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀)
    (y : RationalPoint Y) (hy : y ≫ frobeniusIterate ΦY m = y) :
    IsModelFrobenius (fibreFrobenius f hf m y hy) (pullback.snd f₀ (hY.descendedPoint y hy))
      (hY.fibreModelMap hfp y hy) := by
  refine ⟨hX.isPullback_fibreModelMap hY hfp h₀ y hy, ?_⟩
  obtain ⟨FX, hFX, hpX⟩ := hX.exists_isFrobenius
  obtain ⟨FY, hFY, -⟩ := hY.exists_isFrobenius
  have h₁ := (End.asHom_pow_comp_eq_comp_asHom_pow (hFX.comp_eq_comp fX₀ hFY f₀).symm m).symm
  have h₂ : hY.descendedPoint y hy ≫ End.asHom (End.of FY ^ m) =
      𝟙 _ ≫ hY.descendedPoint y hy := by
    rw [hFY.pow fY₀ m _ (𝟙 _) fun r ↦ (frobeniusFixedField_pow_eq r).symm, Spec.map_id]
  refine ⟨pullback.map _ _ _ _ _ (𝟙 _) _ h₁ h₂, ?_, ?_⟩
  · rw [natCard_frobeniusFixedField (NeZero.ne m)]
    exact (hFX.pow fX₀ m).pullbackMap
      (Scheme.Hom.IsFrobenius.id_spec frobeniusFixedField_pow_eq) h₁ h₂
  · apply pullback.hom_ext
    · rw [Category.assoc, fibreModelMap_fst, Category.assoc, pullback.lift_fst,
        fibreModelMap_fst_assoc, ← Category.assoc, ← Over.comp_left, fibreFrobenius_fst,
        Over.comp_left, Category.assoc, IsModelFrobenius.frobeniusIterate_left_comp hpX]
    · rw [Category.assoc, fibreModelMap_snd, Category.assoc, pullback.lift_snd,
        fibreModelMap_snd_assoc, Category.comp_id, Over.w_assoc]

/-- **The fibres of a morphism of models are models**, existence form (blueprint
`lemma-comparison-via-relative-frobenius` (4), side clause;
`lemma-comparison-via-relative-frobenius--4` (2)): the fibre of `f` at a rational point `y` fixed by
`Φ_Y^m` is the base change of a scheme `Z₀` locally of finite type over a finite field `k'` with
`q ^ m` elements, whose `q ^ m`-power Frobenius base-changes to the restriction of `Φ_X^m`. -/
theorem IsModelFrobenius.exists_isModelFrobenius_fibreFrobenius {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] [IsAlgClosed k] {X₀ Y₀ : Scheme.{u}}
    {fX₀ : X₀ ⟶ Spec (.of k₀)} {fY₀ : Y₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType fX₀]
    {pX : X.left ⟶ X₀} {pY : Y.left ⟶ Y₀} (hX : IsModelFrobenius ΦX fX₀ pX)
    (hY : IsModelFrobenius ΦY fY₀ pY) {f : X ⟶ Y} (hf : ΦX ≫ f = f ≫ ΦY) {f₀ : X₀ ⟶ Y₀}
    (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀) {m : ℕ} (hm : m ≠ 0)
    (y : RationalPoint Y) (hy : y ≫ frobeniusIterate ΦY m = y) :
    ∃ (k' : Type u) (_ : Field k') (_ : Finite k') (_ : Algebra k' k) (Z₀ : Scheme.{u})
      (g₀ : Z₀ ⟶ Spec (.of k')) (pZ : (pullback f y).left ⟶ Z₀),
      Nat.card k' = Nat.card k₀ ^ m ∧ LocallyOfFiniteType g₀ ∧
        IsModelFrobenius (fibreFrobenius f hf m y hy) g₀ pZ := by
  let := Fintype.ofFinite k₀
  have : NeZero m := ⟨hm⟩
  have : LocallyOfFiniteType (f₀ ≫ fY₀) := by
    rw [h₀]
    infer_instance
  have := locallyOfFiniteType_of_comp f₀ fY₀
  exact ⟨_, inferInstance, inferInstance, inferInstance, _, _, _,
    natCard_frobeniusFixedField hm, inferInstance,
    hX.isModelFrobenius_fibreFrobenius hY hf hfp h₀ y hy⟩

end Fibre

end ProEtale.CondensedRing

end AlgebraicGeometry
