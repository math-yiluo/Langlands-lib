/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFiberFrobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusExistence
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite
public import WeilConjectures.TraceFormula.ModelExtension

/-!

# The base change from a finite field to an algebraically closed field

Let `k = 𝔽_q` be a finite field, `Ω` a field containing `k` (in the applications the algebraic
closure `k̄`) and `X` a scheme over `Spec k`. This file sets up the geometry of the base change
`X̄ = X ×_k Ω`, an object of `Over (Spec Ω)`, which connects the Weil objects of
`WeilConjectures.TraceFormula.Statement`, living over `k` with an automorphism `e`, and the
model-Frobenius setting of the Lefschetz–Verdier formula, living over `Ω` with an endomorphism
`Φ` over `Spec Ω`.

* The `q`-power Frobenius `F_X : X ⟶ X` (`AlgebraicGeometry.overFrobenius`) is a morphism
  over `Spec k`, since `k = 𝔽_q`, and commutes with every morphism of schemes over `Spec k`.
* For an endomorphism `g` of `X` over `Spec k` and `N : ℕ`, the *model Frobenius*
  `Φ = (g ≫ F_X^N) ×_k Ω` of `X̄` (`baseChangeModelFrobenius N g`) is an
  endomorphism over `Spec Ω`. For `g = 𝟙` it is the base change of the `q^N`-power Frobenius,
  the model Frobenius of `IsModelFrobenius` for a model of `X̄` over `𝔽_{q^N}`
  (`AlgebraicGeometry.exists_isModelFrobenius_modelFrobenius_id`). For an automorphism `e`,
  `Φ = (e^{n+1} ≫ F_X^{n+1}) ×_k k̄` is the Frobenius `σ^{n+1}` twisted by `e^{n+1}`.
* A morphism `x̄ : Spec Ω ⟶ X` over `Spec k` is the same as an `Ω`-rational point
  `x̄' = (x̄, 𝟙)` of `X̄` (`AlgebraicGeometry.geometricBaseChangePoint`). Let `σ` be an
  automorphism of `Spec Ω` inverse to `Spec(y ↦ y ^ (q ^ N))`; for `Ω = k̄` this is `σ^N` for the
  Galois Frobenius `σ` (`AlgebraicGeometry.geometricFrobeniusField_pow_inv`). Then
  `x̄ ≫ g = σ ≫ x̄` if and only if `x̄'` is fixed by `Φ = (g ≫ F_X^N) ×_k Ω`
  (`AlgebraicGeometry.geometricBaseChangePoint_comp_modelFrobenius_eq_iff`), since
  `x̄ ≫ F_X^N = Spec(y ↦ y ^ (q ^ N)) ≫ x̄`. In particular the points of degree `n + 1` for `e`
  (`ProEtale.CondensedRing.frobeniusFixedPoints e (n + 1)`) are the rational points of `X̄` fixed by
  `Φ = (e^{n+1} ≫ F_X^{n+1}) ×_k k̄` (`AlgebraicGeometry.frobeniusFixedPointsEquiv`).

The statements are made for a general field `Ω` and specialized to `Ω = k̄` only at the end:
statements about the categories of sheaves on the concrete scheme `Spec k̄` hit kernel timeouts.

## Main definitions

- `AlgebraicGeometry.overFrobenius`: the `q`-power Frobenius of a scheme over `Spec k`.
- `AlgebraicGeometry.geometricBaseChange`: the base change functor
  `Over (Spec k) ⥤ Over (Spec Ω)`, with projection
  `AlgebraicGeometry.geometricBaseChangeProj : X̄ ⟶ X`.
- `baseChangeModelFrobenius`: the model Frobenius `(g ≫ F_X^N) ×_k Ω` of `X̄`.
- `AlgebraicGeometry.geometricBaseChangePoint`: the rational point of `X̄` attached to a
  morphism `Spec Ω ⟶ X` over `Spec k`.
- `AlgebraicGeometry.frobeniusFixedPointsEquiv`: the points of degree `n + 1` for `e` are
  the rational points of `X̄ = X ×_k k̄` fixed by the model Frobenius.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme ProEtale.CondensedRing

variable {k : Type u} [Field k] [Finite k]

/-! ### The Frobenius of a scheme over a finite field -/

section Frobenius

variable (X : Over (Spec (.of k)))

/-- The `#k`-power Frobenius `F_X` of a scheme `X` over the finite field `k`, as a morphism over
`Spec k`: the scheme Frobenius `Scheme.Hom.modelFrobenius X.hom`, the absolute
`#k`-power Frobenius of `X.left`. -/
noncomputable def overFrobenius : X ⟶ X :=
  Over.homMk X.hom.modelFrobenius X.hom.modelFrobenius_comp

@[simp]
lemma overFrobenius_left : (overFrobenius X).left = X.hom.modelFrobenius :=
  rfl

lemma isFrobenius_overFrobenius_left : (overFrobenius X).left.IsFrobenius (Nat.card k) :=
  X.hom.isFrobenius_modelFrobenius

variable {X} in
/-- The Frobenius commutes with every morphism over `Spec k`. -/
lemma comp_overFrobenius {Y : Over (Spec (.of k))} (f : X ⟶ Y) :
    f ≫ overFrobenius Y = overFrobenius X ≫ f := by
  ext1
  exact Scheme.Hom.comp_modelFrobenius (f := X.hom) (g := Y.hom) f.left

/-- The `N`-th iterate of the Frobenius is the `#k ^ N`-power Frobenius. -/
lemma isFrobenius_frobeniusIterate_overFrobenius_left (N : ℕ) :
    (frobeniusIterate (overFrobenius X) N).left.IsFrobenius (Nat.card k ^ N) := by
  rw [frobeniusIterate_left]
  exact (isFrobenius_overFrobenius_left X).pow X.hom N

omit [Finite k] in
/-- The characteristic `ringChar k` vanishes on a scheme over `k`. -/
lemma natCast_ringChar_left_eq_zero : (ringChar k : Γ(X.left, ⊤)) = 0 :=
  isOfCharacteristic_of_hom_spec X.hom

/-- The `N`-th iterate of the Frobenius is the absolute `p ^ (a * N)`-power Frobenius, where
`#k = p ^ a`. -/
lemma frobeniusIterate_overFrobenius_left (N : ℕ) :
    (frobeniusIterate (overFrobenius X) N).left =
      X.left.iterateFrobenius (FiniteField.ringChar_prime (k := k))
        (natCast_ringChar_left_eq_zero X)
        (FiniteField.frobeniusExponent k * N) := by
  induction N with
  | zero => rw [frobeniusIterate_zero, mul_zero, Scheme.iterateFrobenius_zero]; rfl
  | succ N ih =>
    rw [frobeniusIterate_succ, Over.comp_left, ih, overFrobenius_left, Nat.mul_succ, add_comm,
      Scheme.iterateFrobenius_add]
    rfl

end Frobenius

/-! ### The Frobenius of `Spec Ω` -/

section PowCard

variable (k) (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- The ring endomorphism `y ↦ y ^ (#k ^ N)` of a field `Ω` containing `k`. -/
noncomputable def powCardPowRingHom (N : ℕ) : CommRingCat.of Ω ⟶ CommRingCat.of Ω :=
  letI := Fintype.ofFinite k
  CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k Ω).toRingHom ^ N)

variable {k Ω}

lemma powCardPowRingHom_apply (N : ℕ) (y : Ω) :
    (powCardPowRingHom k Ω N).hom y = y ^ (Nat.card k ^ N) := by
  let := Fintype.ofFinite k
  simp only [powCardPowRingHom, CommRingCat.hom_ofHom, RingHom.coe_pow]
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card, ← pow_mul, pow_succ']

omit [Finite k] in
/-- The prime `ringChar k` vanishes in a field `Ω` containing `k`. -/
lemma ringChar_cast_eq_zero : (ringChar k : Ω) = 0 := by
  rw [← map_natCast (algebraMap k Ω), ringChar.Nat.cast_ringChar, map_zero]

/-- On `Spec Ω`, the absolute `p ^ (a N)`-power Frobenius, for `#k = p ^ a`, is `Spec` of the
`#k ^ N`-power map. -/
lemma iterateFrobenius_spec_eq_specMap_powCardPowRingHom (N : ℕ)
    (hΩ : (ringChar k : Γ(Spec (.of Ω), ⊤)) = 0) :
    (Spec (.of Ω)).iterateFrobenius (FiniteField.ringChar_prime (k := k)) hΩ
        (FiniteField.frobeniusExponent k * N) = Spec.map (powCardPowRingHom k Ω N) := by
  rw [Scheme.iterateFrobenius_Spec _ _ (ringChar_cast_eq_zero (k := k) (Ω := Ω))]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_))
  rw [CommRingCat.hom_ofHom, powCardPowRingHom_apply, iterateFrobeniusOfPrime_apply,
    pow_mul, ← FiniteField.card_eq_ringChar_pow_frobeniusExponent]

end PowCard

section Galois

/-- The `N`-th power of the geometric Frobenius of `k̄` is a left inverse of the
`#k ^ N`-power map. -/
lemma geometricFrobenius_pow_apply_pow (N : ℕ) (y : AlgebraicClosure k) :
    ((FiniteField.geometricFrobenius k (AlgebraicClosure k)) ^ N) (y ^ (Nat.card k ^ N)) = y := by
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, AlgEquiv.mul_apply, pow_succ, pow_mul,
      (FiniteField.geometricFrobenius_eq_iff k (AlgebraicClosure k)).2 rfl, ih]

/-- The `N`-th power of the geometric Frobenius `σ` of `Spec k̄` is inverse to `Spec` of the
`#k ^ N`-power map of `k̄`: `σ^N ≫ Spec(y ↦ y ^ (#k ^ N)) = 𝟙`. -/
lemma geometricFrobeniusField_pow_hom_comp_specMap (n : ℕ) :
    ((geometricFrobeniusField k).pow (n + 1)).hom ≫
      Spec.map (powCardPowRingHom k (AlgebraicClosure k) (n + 1)) = 𝟙 _ := by
  rw [Iso.pow_hom_eq_pow, geometricFrobeniusField_hom_pow, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext y
  change ((FiniteField.geometricFrobenius k (AlgebraicClosure k)) ^ (n + 1))
    ((powCardPowRingHom k (AlgebraicClosure k) (n + 1)).hom y) = y
  rw [powCardPowRingHom_apply]
  exact geometricFrobenius_pow_apply_pow (n + 1) y

/-- The inverse of the `N`-th power of the geometric Frobenius `σ` of `Spec k̄` is `Spec` of the
`#k ^ N`-power map of `k̄`. -/
lemma geometricFrobeniusField_pow_inv (n : ℕ) :
    ((geometricFrobeniusField k).pow (n + 1)).inv =
      Spec.map (powCardPowRingHom k (AlgebraicClosure k) (n + 1)) := by
  rw [← cancel_epi ((geometricFrobeniusField k).pow (n + 1)).hom, Iso.hom_inv_id,
    geometricFrobeniusField_pow_hom_comp_specMap]

end Galois

/-! ### The base change -/

section BaseChange

variable (k) (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- The base change functor `X ↦ X̄ = X ×_k Ω` from schemes over `Spec k` to schemes over
`Spec Ω`. -/
noncomputable abbrev geometricBaseChange : Over (Spec (.of k)) ⥤ Over (Spec (.of Ω)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

variable {Ω} (X : Over (Spec (.of k)))

instance [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((geometricBaseChange k Ω).obj X).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))

instance [QuasiCompact X.hom] : QuasiCompact ((geometricBaseChange k Ω).obj X).hom :=
  inferInstanceAs (QuasiCompact
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))

instance [IsSeparated X.hom] : IsSeparated ((geometricBaseChange k Ω).obj X).hom :=
  inferInstanceAs (IsSeparated
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))

variable {k}

/-- The projection `π : X̄ ⟶ X` of the base change. -/
noncomputable def geometricBaseChangeProj : ((geometricBaseChange k Ω).obj X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

omit [Finite k] in
lemma isPullback_geometricBaseChangeProj :
    IsPullback (geometricBaseChangeProj (Ω := Ω) X) ((geometricBaseChange k Ω).obj X).hom X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
  IsPullback.of_hasPullback _ _

omit [Finite k] in
variable {X} in
/-- The base change of a morphism `f` lies over `f`: `f̄ ≫ π = π ≫ f`. -/
@[reassoc (attr := simp)]
lemma geometricBaseChange_map_left_comp_proj {Y : Over (Spec (.of k))} (f : X ⟶ Y) :
    ((geometricBaseChange k Ω).map f).left ≫ geometricBaseChangeProj Y =
      geometricBaseChangeProj X ≫ f.left := by
  simp [geometricBaseChangeProj]

variable (Ω) in
/-- The model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω` of the base change `X̄`, for an endomorphism `g`
of `X` over `Spec k`: an endomorphism of `X̄` over `Spec Ω`. For an automorphism `e`, the model
Frobenius `(e^{n+1} ≫ F_X^{n+1}) ×_k k̄` is the Frobenius `σ^{n+1}` twisted by `e^{n+1}`. -/
noncomputable def baseChangeModelFrobenius (N : ℕ) (g : X ⟶ X) :
    (geometricBaseChange k Ω).obj X ⟶ (geometricBaseChange k Ω).obj X :=
  (geometricBaseChange k Ω).map (g ≫ frobeniusIterate (overFrobenius X) N)

/-- `Φ ≫ π = π ≫ g ≫ F_X^N`. -/
@[reassoc]
lemma modelFrobenius_left_comp_proj (N : ℕ) (g : X ⟶ X) :
    (baseChangeModelFrobenius Ω X N g).left ≫ geometricBaseChangeProj X =
      geometricBaseChangeProj X ≫ (g ≫ frobeniusIterate (overFrobenius X) N).left :=
  geometricBaseChange_map_left_comp_proj _

/-- For `g = 𝟙`, the model Frobenius `F_X^N ×_k Ω` is the `N`-th iterate of `F_X ×_k Ω`. -/
lemma modelFrobenius_id (N : ℕ) :
    baseChangeModelFrobenius Ω X N (𝟙 X) = frobeniusIterate (baseChangeModelFrobenius Ω X 1 (𝟙 X))
        N := by
  simp only [baseChangeModelFrobenius, Category.id_comp, frobeniusIterate_one]
  induction N with
  | zero => simp
  | succ N ih => rw [frobeniusIterate_succ, frobeniusIterate_succ, Functor.map_comp, ih]

/-- For `g = 𝟙`, the model Frobenius `F_X ×_k Ω` is the model Frobenius of the model `X` of
`X̄` over `k` (blueprint `definition-frobenius-correspondences-their-operators`). -/
theorem isModelFrobenius_modelFrobenius_one :
    IsModelFrobenius (baseChangeModelFrobenius Ω X 1 (𝟙 X)) X.hom (geometricBaseChangeProj X) where
  isPullback := isPullback_geometricBaseChangeProj X
  exists_isFrobenius := ⟨(overFrobenius X).left, isFrobenius_overFrobenius_left X, by
    rw [modelFrobenius_left_comp_proj, Category.id_comp, frobeniusIterate_one]⟩

/-- For `g = 𝟙`, `Ω` algebraically closed and `N ≠ 0`, the model Frobenius `F_X^N ×_k Ω` is the
model Frobenius of a model of `X̄` over the subfield `𝔽_{q^N}` of `Ω` (blueprint
`definition-frobenius-correspondences-their-operators`). -/
theorem exists_isModelFrobenius_modelFrobenius_id [IsAlgClosed Ω] [LocallyOfFiniteType X.hom]
    {N : ℕ} (hN : N ≠ 0) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₁ Ω)
      (X₁ : Scheme.{u}) (f₁ : X₁ ⟶ Spec (.of k₁)) (_ : LocallyOfFiniteType f₁)
      (p₁ : ((geometricBaseChange k Ω).obj X).left ⟶ X₁),
      Nat.card k₁ = Nat.card k ^ N ∧ IsModelFrobenius (baseChangeModelFrobenius Ω X N (𝟙 X)) f₁ p₁
          := by
  obtain ⟨k₁, _, _, _, _, _, hcard⟩ := exists_finiteField_natCard_eq_pow k Ω hN
  have h := (isModelFrobenius_modelFrobenius_one (Ω := Ω) X).fieldChange (k₁ := k₁) hcard
  rw [← modelFrobenius_id] at h
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, _, modelFieldChange X.hom k₁,
    inferInstance, _, hcard, h⟩

end BaseChange

/-! ### Rational points of the base change -/

section Points

variable {Ω : Type u} [Field Ω] [Algebra k Ω] {X : Over (Spec (.of k))}

/-- The `Ω`-rational point `x̄' = (x̄, 𝟙)` of `X̄ = X ×_k Ω` attached to a morphism
`x̄ : Spec Ω ⟶ X` over `Spec k`. -/
noncomputable def geometricBaseChangePoint (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    RationalPoint ((geometricBaseChange k Ω).obj X) :=
  Over.homMk (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])) (by simp)

omit [Finite k] in
@[reassoc (attr := simp)]
lemma geometricBaseChangePoint_left_comp_proj (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (geometricBaseChangePoint x hx).left ≫ geometricBaseChangeProj X = x :=
  pullback.lift_fst _ _ _

omit [Finite k] in
/-- A rational point of `X̄` is determined by its image in `X`. -/
lemma rationalPoint_ext {y y' : RationalPoint ((geometricBaseChange k Ω).obj X)}
    (h : y.left ≫ geometricBaseChangeProj X = y'.left ≫ geometricBaseChangeProj X) : y = y' := by
  ext1
  refine pullback.hom_ext h ?_
  have hy := Over.w y
  have hy' := Over.w y'
  simp only [Over.pullback_obj_hom] at hy hy'
  exact hy.trans hy'.symm

omit [Finite k] in
/-- The image `y ≫ π` of a rational point `y` of `X̄` lies over `Spec k`. -/
lemma rationalPoint_left_comp_proj_comp (y : RationalPoint ((geometricBaseChange k Ω).obj X)) :
    (y.left ≫ geometricBaseChangeProj X) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  have hy := Over.w y
  simp only [Over.pullback_obj_hom] at hy
  rw [Category.assoc, geometricBaseChangeProj, pullback.condition, ← Category.assoc, hy]
  exact Category.id_comp _

omit [Finite k] in
/-- The rational point of `X̄` attached to the image `y ≫ π` of a rational point `y` is `y`. -/
lemma geometricBaseChangePoint_left_comp_proj_eq
    (y : RationalPoint ((geometricBaseChange k Ω).obj X)) :
    geometricBaseChangePoint (y.left ≫ geometricBaseChangeProj X)
      (rationalPoint_left_comp_proj_comp y) = y :=
  rationalPoint_ext (geometricBaseChangePoint_left_comp_proj _ _)

/-- Let `σ` be an automorphism of `Spec Ω` whose inverse is `Spec(y ↦ y ^ (#k ^ N))`. A morphism
`x̄ : Spec Ω ⟶ X` over `Spec k` satisfies `x̄ ≫ g = σ ≫ x̄` if and only if the rational point
`x̄' = (x̄, 𝟙)` of `X̄` is fixed by the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω`: since
`(x̄ ≫ g) ≫ F_X^N = Spec(y ↦ y ^ (#k ^ N)) ≫ x̄ ≫ g`. -/
theorem geometricBaseChangePoint_comp_modelFrobenius_eq_iff (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (N : ℕ) (g : X ⟶ X)
    (σ : Spec (.of Ω) ≅ Spec (.of Ω)) (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) :
    geometricBaseChangePoint x hx ≫ baseChangeModelFrobenius Ω X N g = geometricBaseChangePoint x
        hx ↔
      x ≫ g.left = σ.hom ≫ x := by
  have hF : (x ≫ g.left) ≫ (frobeniusIterate (overFrobenius X) N).left =
      Spec.map (powCardPowRingHom k Ω N) ≫ x ≫ g.left :=
    isFrobenius_frobeniusIterate_overFrobenius_left X N (x ≫ g.left) _
      (powCardPowRingHom_apply N)
  have key : geometricBaseChangePoint x hx ≫ baseChangeModelFrobenius Ω X N g =
      geometricBaseChangePoint x hx ↔
      x ≫ (g ≫ frobeniusIterate (overFrobenius X) N).left = x := by
    constructor
    · intro h
      have := congrArg (fun y ↦ y.left ≫ geometricBaseChangeProj X) h
      simpa [modelFrobenius_left_comp_proj] using this
    · intro h
      refine rationalPoint_ext ?_
      simpa [modelFrobenius_left_comp_proj] using h
  rw [Over.comp_left, ← Category.assoc, hF, ← hσ] at key
  rw [key]
  constructor
  · intro h
    conv_rhs => rw [← h]
    rw [Iso.hom_inv_id_assoc]
  · intro h
    rw [h, Iso.inv_hom_id_assoc]

/-- The points of degree `n + 1` of `X` for the Frobenius twisted by `e` are the rational points
of the base change `X̄ = X ×_k k̄` fixed by the model Frobenius
`Φ = (e^{n+1} ≫ F_X^{n+1}) ×_k k̄`: `x̄ ↦ (x̄, 𝟙)`. -/
noncomputable def frobeniusFixedPointsEquiv (e : X ≅ X) (n : ℕ) :
    frobeniusFixedPoints e (n + 1) ≃
      {y : RationalPoint ((geometricBaseChange k (AlgebraicClosure k)).obj X) //
        y ≫ baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (e.pow (n + 1)).hom = y} where
  toFun x := ⟨geometricBaseChangePoint x.1 x.2.1,
    (geometricBaseChangePoint_comp_modelFrobenius_eq_iff _ _ _ _ _
      (geometricFrobeniusField_pow_inv n)).2 x.2.2⟩
  invFun y := ⟨y.1.left ≫ geometricBaseChangeProj X, rationalPoint_left_comp_proj_comp y.1, by
    rw [← geometricBaseChangePoint_comp_modelFrobenius_eq_iff _
      (rationalPoint_left_comp_proj_comp y.1) _ _ _ (geometricFrobeniusField_pow_inv n),
      geometricBaseChangePoint_left_comp_proj_eq]
    exact y.2⟩
  left_inv x := Subtype.ext (geometricBaseChangePoint_left_comp_proj _ x.2.1)
  right_inv y := Subtype.ext (geometricBaseChangePoint_left_comp_proj_eq y.1)

end Points

end AlgebraicGeometry
