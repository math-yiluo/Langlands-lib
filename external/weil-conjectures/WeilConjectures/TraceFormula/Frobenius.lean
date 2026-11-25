/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPointsCount
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.TraceFormula.Basic

/-!

# The model Frobenius and the iterated Weil structures

Let `k₀ = 𝔽_q` be a finite field, `k` an algebraically closed field containing `k₀`, `X₀` a
separated `k₀`-scheme of finite type and `X = X₀ ×_{k₀} k` its base change, an object of
`Over (Spec (.of k))`. The *model Frobenius* of `X` is the base change `Φ = F₀ × 𝟙` of the
`q`-power Frobenius `F₀` of `X₀`. It is an endomorphism of `X` over `Spec k`, a finite universal
homeomorphism but not an isomorphism, and the Weil objects of the trace formula are the Weil
objects `WeilBoundedConstructible ℓ Φ` for it: objects `K` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with an isomorphism
`φ : LΦ^* K ≅ K`.

## The iterates

Put `Φ_m = Φ^m` (`ProEtale.CondensedRing.frobeniusIterate`); for the model Frobenius it is the
base change of the `q^m`-power Frobenius of `X₀`. The iterate `φ_m : LΦ_m^* K ≅ K` of the Weil
structure composes the pulled back copies of `φ` along the composition isomorphisms of the
derived pullback (`ProEtale.CondensedRing.WeilBoundedConstructible.iterateStr`):
```
φ_0 : L(𝟙 X)^* K ≅ K,
φ_{m+1} : L(Φ ≫ Φ_m)^* K ≅ LΦ^* LΦ_m^* K --LΦ^* φ_m--> LΦ^* K --φ--> K.
```
The pair `(K, φ_m)` is a Weil object for `Φ_m`
(`ProEtale.CondensedRing.WeilBoundedConstructible.iterate`); the degree `m` trace formula for
`(K, φ)` is the degree one trace formula for `(K, φ_m)`.

## The fixed points

The rational points `x : s ⟶ X` of `X` fixed by `Φ_m` are the `𝔽_{q^m}`-points of `X₀`
(`ProEtale.CondensedRing.IsModelFrobenius.fixedPointEquiv` in
`WeilConjectures.TraceFormula.FixedPoint`, blueprint `lemma-frobenius-fixed-scheme--1`); there are
finitely many of them, and a closed point of `X₀` of degree `d ∣ m` carries exactly `d` of them
(`IsModelFrobenius.sum_fixedPoint`).

## Main definitions

- `ProEtale.CondensedRing.frobeniusIterate`: the iterate `Φ_m = Φ^m` of an endomorphism.
- `ProEtale.CondensedRing.FixedPoint`: the rational points fixed by `Φ_m`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.iterateStr`,
  `ProEtale.CondensedRing.WeilBoundedConstructible.iterate`: the iterated Weil structure
  `φ_m : LΦ_m^* K ≅ K` and the Weil object `(K, φ_m)` for `Φ_m`.
- `ProEtale.CondensedRing.IsModelFrobenius`: `Φ` is the base change of the `q`-power Frobenius
  of a model `X₀` over `k₀` (blueprint `definition-frobenius-correspondences-their-operators`).

## Main statements

- `ProEtale.CondensedRing.IsModelFrobenius.isUniversalHomeomorphism`,
  `ProEtale.CondensedRing.IsModelFrobenius.isFinite`: the iterates of the model Frobenius are
  finite universal homeomorphisms (blueprint `lemma-comparison-via-relative-frobenius--1`).
- `ProEtale.CondensedRing.IsModelFrobenius.finite_fixedPoint`,
  `ProEtale.CondensedRing.IsModelFrobenius.sum_fixedPoint`: there are finitely many fixed
  points of `Φ_m`, counted by the closed points of `X₀`
  (blueprint `lemma-frobenius-fixed-scheme--1`); they are proved in
  `WeilConjectures.TraceFormula.FixedPoint`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Iterates of an endomorphism -/

section Iterate

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (Φ : X ⟶ X)

/-- The `m`-th iterate `Φ_m = Φ^m : X ⟶ X` of an endomorphism `Φ`. -/
noncomputable def frobeniusIterate (m : ℕ) : X ⟶ X :=
  End.asHom (End.of Φ ^ m)

@[simp]
lemma frobeniusIterate_zero : frobeniusIterate Φ 0 = 𝟙 X :=
  rfl

lemma frobeniusIterate_succ (m : ℕ) :
    frobeniusIterate Φ (m + 1) = Φ ≫ frobeniusIterate Φ m := by
  rw [frobeniusIterate, pow_succ]
  rfl

lemma frobeniusIterate_add (m n : ℕ) :
    frobeniusIterate Φ (m + n) = frobeniusIterate Φ n ≫ frobeniusIterate Φ m := by
  rw [frobeniusIterate, pow_add]
  rfl

lemma frobeniusIterate_mul (d n : ℕ) :
    frobeniusIterate Φ (d * n) = frobeniusIterate (frobeniusIterate Φ d) n := by
  rw [frobeniusIterate, pow_mul]
  rfl

@[simp]
lemma frobeniusIterate_one : frobeniusIterate Φ 1 = Φ := by
  rw [frobeniusIterate_succ, frobeniusIterate_zero, Category.comp_id]

/-- `Φ` commutes with its iterates. -/
lemma comp_frobeniusIterate_comm (m : ℕ) :
    Φ ≫ frobeniusIterate Φ m = frobeniusIterate Φ m ≫ Φ := by
  have h₁ := frobeniusIterate_add Φ m 1
  have h₂ := frobeniusIterate_add Φ 1 m
  rw [frobeniusIterate_one] at h₁ h₂
  rw [← h₁, ← h₂, add_comm]

/-- The underlying morphism of schemes of `Φ_m` is the `m`-th iterate of `Φ.left`. -/
lemma frobeniusIterate_left (m : ℕ) :
    (frobeniusIterate Φ m).left = End.asHom (End.of Φ.left ^ m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [frobeniusIterate_succ, Over.comp_left, ih, pow_succ]
    rfl

variable {Φ} in
/-- A point fixed by `Φ` is fixed by every iterate `Φ_m`. -/
lemma comp_frobeniusIterate_of_comp {T : Over (Spec (.of k))} {x : T ⟶ X} (hx : x ≫ Φ = x)
    (m : ℕ) : x ≫ frobeniusIterate Φ m = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [frobeniusIterate_succ, ← Category.assoc, hx, ih]

/-- The rational points `x : s ⟶ X` fixed by the iterate `Φ_m`. -/
abbrev FixedPoint (m : ℕ) : Type u :=
  {x : RationalPoint X // x ≫ frobeniusIterate Φ m = x}

variable {Φ} in
/-- A morphism intertwining two endomorphisms intertwines their iterates. -/
lemma frobeniusIterate_comp_of_comp {Y : Over (Spec (.of k))} {ΦY : Y ⟶ Y} {f : X ⟶ Y}
    (hf : Φ ≫ f = f ≫ ΦY) (m : ℕ) :
    frobeniusIterate Φ m ≫ f = f ≫ frobeniusIterate ΦY m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [frobeniusIterate_succ, frobeniusIterate_succ, Category.assoc, ih, ← Category.assoc, hf,
      Category.assoc]

variable {Φ} in
/-- The image of a point fixed by `Φ_m` under a morphism intertwining `Φ` and `Φ_Y` is fixed by
`Φ_{Y,m}`. -/
lemma comp_comp_frobeniusIterate_of_comp {Y T : Over (Spec (.of k))} {ΦY : Y ⟶ Y} {f : X ⟶ Y}
    (hf : Φ ≫ f = f ≫ ΦY) {x : T ⟶ X} {m : ℕ} (hx : x ≫ frobeniusIterate Φ m = x) :
    (x ≫ f) ≫ frobeniusIterate ΦY m = x ≫ f := by
  rw [Category.assoc, ← frobeniusIterate_comp_of_comp hf, ← Category.assoc, hx]

variable {Φ} in
/-- If `x` is fixed by `Φ_m`, so is its Frobenius translate `x ≫ Φ`. -/
lemma comp_comp_frobeniusIterate {T : Over (Spec (.of k))} {x : T ⟶ X} {m : ℕ}
    (hx : x ≫ frobeniusIterate Φ m = x) : (x ≫ Φ) ≫ frobeniusIterate Φ m = x ≫ Φ := by
  rw [Category.assoc, comp_frobeniusIterate_comm, ← Category.assoc, hx]

end Iterate

/-! ### The iterated Weil structure -/

section WeilIterate

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Φ : X ⟶ X}

namespace WeilBoundedConstructible

/-- The iterate `φ_m : LΦ_m^* K ≅ K` of the Weil structure `φ` of a Weil object `(K, φ)`:
`φ_0` is the identity isomorphism `L(𝟙 X)^* K ≅ K` and `φ_{m+1}` is the composite
```
LΦ_{m+1}^* K = L(Φ ≫ Φ_m)^* K ≅ LΦ^* LΦ_m^* K --LΦ^* φ_m--> LΦ^* K --φ--> K
```
(blueprint `definition-frobenius-correspondences-their-operators--4`). -/
noncomputable def iterateStr (K : WeilBoundedConstructible ℓ Φ) :
    (m : ℕ) → (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K.carrier ≅ K.carrier
  | 0 => (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app K.carrier
  | m + 1 =>
    eqToIso (by rw [frobeniusIterate_succ]) ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ
        (frobeniusIterate Φ m)).app K.carrier ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).mapIso
        (iterateStr K m) ≪≫
      K.str

/-- The `m`-th iterate `(K, φ_m)` of a Weil object `(K, φ)` for `Φ`: a Weil object for the
iterate `Φ_m` with the same underlying complex. -/
noncomputable def iterate (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    WeilBoundedConstructible ℓ (frobeniusIterate Φ m) :=
  IsoAlgebra.mk K.carrier (K.iterateStr m)

@[simp]
lemma iterate_carrier (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    (K.iterate m).carrier = K.carrier :=
  IsoAlgebra.mk_carrier _ _

/- The carriers `(K.iterate m).carrier` and `K.carrier` are defeq, but checking it unfolds the
pullbacks `LΦ_m^*` and `LΦ^*` (the structure eta check compares the types `IsoAlgebra (LΦ_m^*)`
and `IsoAlgebra (LΦ^*)`), which times out, so the statement casts along `iterate_carrier`. -/
lemma iterate_str (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    (K.iterate m).str =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m)).mapIso (eqToIso (K.iterate_carrier m)) ≪≫ K.iterateStr m ≪≫
        eqToIso (K.iterate_carrier m).symm := by
  have key (a : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      (φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m)).obj a ≅ a) :
      (IsoAlgebra.mk a φ).str =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ m)).mapIso (eqToIso (IsoAlgebra.mk_carrier a φ)) ≪≫ φ ≪≫
          eqToIso (IsoAlgebra.mk_carrier a φ).symm := by
    ext
    simp
  exact key _ _

/-- The iterates are a cocycle: `φ_{m+n}` is `φ_n` composed with the pullback of `φ_m` along
`Φ_n`, through the composition isomorphism `L(Φ_n ≫ Φ_m)^* ≅ LΦ_n^* LΦ_m^*` (blueprint
`definition-frobenius-correspondences-their-operators--4`). -/
lemma iterateStr_add (K : WeilBoundedConstructible ℓ Φ) (m n : ℕ) :
    (K.iterateStr (m + n)).hom =
      eqToHom (by rw [frobeniusIterate_add]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ n) (frobeniusIterate Φ m)).hom.app K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ n)).map (K.iterateStr m).hom ≫
        (K.iterateStr n).hom := by
  induction n with
  | zero =>
    have h₀ : (K.iterateStr 0).hom =
        eqToHom (show _ = (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (𝟙 X)).obj K.carrier by rw [frobeniusIterate_zero]) ≫
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app
            K.carrier := by
      simp only [iterateStr, eqToHom_refl, Category.id_comp, Iso.app_hom]
    rw [h₀]
    exact (boundedConstructibleUpperStarComp_id_aux _ ℓ (frobeniusIterate_zero Φ)
      (frobeniusIterate_add Φ m 0) (K.iterateStr m).hom).symm
  | succ n ih =>
    have h := boundedConstructibleUpperStarComp_cocycle_aux (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate_succ Φ (m + n)) (frobeniusIterate_add Φ m n)
      (frobeniusIterate_add Φ m (n + 1)) (frobeniusIterate_succ Φ n) (K.iterateStr m).hom
      (K.iterateStr n).hom K.str.hom (K.iterateStr (m + n)).hom ih
    simp only [Nat.add_succ, Nat.add_zero, iterateStr, Iso.trans_hom, eqToIso.hom, Iso.app_hom,
      Functor.mapIso_hom] at h ⊢
    dsimp only [HAdd.hAdd, Add.add] at h ⊢
    exact h

end WeilBoundedConstructible

end WeilIterate

/-! ### The model Frobenius -/

section Model

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (Φ : X ⟶ X)
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  (f₀ : X₀ ⟶ Spec (.of k₀)) (p : X.left ⟶ X₀)

/-- The endomorphism `Φ` of `X` over `Spec k` is the *model Frobenius* of a model `X₀` of `X`
over the finite field `k₀ ⊆ k`: the square
```
     X ───p───▶ X₀
     │          │
  a_X│          │f₀
     ▼          ▼
  Spec k ───▶ Spec k₀
```
is cartesian, so that `X = X₀ ×_{k₀} k`, and `Φ = F₀ × 𝟙` is the base change of the
`#k₀`-power Frobenius `F₀` of `X₀`, that is `Φ ≫ p = p ≫ F₀`. Since the square is cartesian, the
two equations `Φ ≫ p = p ≫ F₀` and `Φ ≫ a_X = a_X` determine `Φ` (blueprint
`definition-frobenius-correspondences-their-operators`). -/
structure IsModelFrobenius : Prop where
  /-- `X` is the base change `X₀ ×_{k₀} k`. -/
  isPullback : IsPullback p X.hom f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))
  /-- `Φ` is the base change of the `#k₀`-power Frobenius of `X₀`. -/
  exists_isFrobenius : ∃ F₀ : X₀ ⟶ X₀, F₀.IsFrobenius (Nat.card k₀) ∧ Φ.left ≫ p = p ≫ F₀

variable {Φ f₀ p}

/-- The iterates `Φ_m` of the model Frobenius are universal homeomorphisms (blueprint
`lemma-comparison-via-relative-frobenius--1`, Step 2). -/
lemma IsModelFrobenius.isUniversalHomeomorphism (hΦ : IsModelFrobenius Φ f₀ p) (m : ℕ) :
    IsUniversalHomeomorphism (frobeniusIterate Φ m).left := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have : IsUniversalHomeomorphism Φ.left :=
    hF₀.isUniversalHomeomorphism_of_isPullback hΦ.isPullback (Over.w Φ) hp
  induction m with
  | zero => exact inferInstanceAs (IsUniversalHomeomorphism (𝟙 X.left))
  | succ m ih =>
    rw [frobeniusIterate_succ, Over.comp_left]
    infer_instance

/-- The iterates `Φ_m` of the model Frobenius of a model locally of finite type are finite
(blueprint `lemma-comparison-via-relative-frobenius--1`, Step 1). -/
lemma IsModelFrobenius.isFinite [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (m : ℕ) : IsFinite (frobeniusIterate Φ m).left := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have : IsFinite Φ.left := hF₀.isFinite_of_isPullback hΦ.isPullback (Over.w Φ) hp
  induction m with
  | zero => exact inferInstanceAs (IsFinite (𝟙 X.left))
  | succ m ih =>
    rw [frobeniusIterate_succ, Over.comp_left]
    infer_instance

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
