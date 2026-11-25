/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!

# Duality and invariants under a finite group of invertible order

This file proves the finite-group core of blueprint `lemma-duality-invariants-pro-p--1` ("Verdier
duality commutes with invariants under a pro-`p` group"). Let `G` be a finite group acting on an
object `E` of an `R`-linear category, `ρ : G →* End E`, with `|G|` invertible in `R`. Then the
invariants of `E` are the image of the *averaging idempotent*
```
e = |G|⁻¹ ∑_{h ∈ G} ρ(h)
```
(`CategoryTheory.averaging`, `CategoryTheory.averaging_comp_averaging`). Let `D` be a
contravariant additive functor (Verdier duality), and let `G` act on `D E` by the contragredient
action `h ↦ D(ρ(h⁻¹))` (`CategoryTheory.contragredient`). Then:

* `D` sends the averaging idempotent of `E` to the averaging idempotent of the contragredient
  action, since inversion permutes the summands (`CategoryTheory.map_averaging_op`);
* hence the image of the dual idempotent is the dual of the image: for splittings
  `E^G ⟶ E ⟶ E^G` of `e` and `(D E)^G ⟶ D E ⟶ (D E)^G` of the averaging idempotent of
  `D E`, the composite `(D E)^G ⟶ D E ⟶ D(E^G)` is an isomorphism
  (`CategoryTheory.invariantsDualIso`);
* for Verdier duality `D = RHom(-, ω)` in a monoidal closed category, the corresponding pairing
  `E^G ⊗ (D E)^G ⟶ ω` is the restriction of the evaluation `E ⊗ D E ⟶ ω` to the two invariant
  direct summands (`CategoryTheory.uncurry_invariantsDualIso_hom`).

For a pro-`p` group `P` acting continuously, the blueprint deduces the statement from the finite
quotients of `P` by exactness and continuity of `RΓ(P, -)` on prime-to-`p` torsion coefficients;
that limit argument is not formalised here.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ w

open CategoryTheory Opposite

namespace CategoryTheory

section Split

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C'] (D : Cᵒᵖ ⥤ C')

/-- **The image of the dual idempotent is the dual of the image.** Let `e : E ⟶ E` be split by
`ι : I ⟶ E`, `π : E ⟶ I` (`ι ≫ π = 𝟙`, `π ≫ ι = e`) and let `D(e) : D E ⟶ D E` be split by
`ι' : I' ⟶ D E`, `π' : D E ⟶ I'`, for a contravariant functor `D`. Then
`ι' ≫ D(ι) : I' ⟶ D I` is an isomorphism, with inverse `D(π) ≫ π'`. -/
@[simps]
def splitDualIso {E I : C} {e : E ⟶ E} {ι : I ⟶ E} {π : E ⟶ I} (hιπ : ι ≫ π = 𝟙 I)
    (hπι : π ≫ ι = e) {I' : C'} {ι' : I' ⟶ D.obj (op E)} {π' : D.obj (op E) ⟶ I'}
    (hιπ' : ι' ≫ π' = 𝟙 I') (hπι' : π' ≫ ι' = D.map e.op) :
    I' ≅ D.obj (op I) where
  hom := ι' ≫ D.map ι.op
  inv := D.map π.op ≫ π'
  hom_inv_id := by
    have h : D.map ι.op ≫ D.map π.op = π' ≫ ι' := by rw [← D.map_comp, ← op_comp, hπι, hπι']
    rw [Category.assoc, reassoc_of% h, reassoc_of% hιπ', hιπ']
  inv_hom_id := by
    have h : ι ≫ e ≫ π = 𝟙 I := by rw [← hπι, Category.assoc, reassoc_of% hιπ, hιπ]
    rw [Category.assoc, reassoc_of% hπι', ← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp,
      Category.assoc, h, op_id, D.map_id]

end Split

section Averaging

variable (R : Type w) [CommRing R] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {G : Type u₃} [Group G] [Fintype G] [Invertible (Fintype.card G : R)]

/-- The **averaging endomorphism** `|G|⁻¹ ∑_{h ∈ G} ρ(h)` of a family of endomorphisms `ρ`
indexed by a finite group `G` of order invertible in `R`. For an action `ρ : G →* End E` it is
an idempotent (`CategoryTheory.averaging_comp_averaging`) whose image is the object of
invariants. -/
noncomputable def averaging {E : C} (ρ : G → (E ⟶ E)) : E ⟶ E :=
  ⅟(Fintype.card G : R) • ∑ h, ρ h

variable {R}

omit [Group G] in
/-- `|G|` times the averaging endomorphism is the sum `∑_{h ∈ G} ρ(h)`. -/
lemma nsmul_averaging {E : C} (ρ : G → (E ⟶ E)) :
    Fintype.card G • averaging R ρ = ∑ h, ρ h := by
  rw [averaging, ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_invOf_self, one_smul]

/-- The averaging endomorphism is invariant: `ρ(g) ∘ e = e`. -/
lemma averaging_comp {E : C} (ρ : G →* End E) (g : G) :
    averaging R (fun h ↦ (ρ h).asHom) ≫ (ρ g).asHom =
      averaging R (fun h ↦ (ρ h).asHom) := by
  rw [averaging, Linear.smul_comp, Preadditive.sum_comp]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h ↦ ?_
  rw [Equiv.coe_mulLeft, map_mul, End.mul_asHom]

/-- The averaging endomorphism is invariant: `e ∘ ρ(g) = e`. -/
lemma comp_averaging {E : C} (ρ : G →* End E) (g : G) :
    (ρ g).asHom ≫ averaging R (fun h ↦ (ρ h).asHom) =
      averaging R (fun h ↦ (ρ h).asHom) := by
  rw [averaging, Linear.comp_smul, Preadditive.comp_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h ↦ ?_
  rw [Equiv.coe_mulRight, map_mul, End.mul_asHom]

/-- The averaging endomorphism of an action is an **idempotent**. -/
lemma averaging_comp_averaging {E : C} (ρ : G →* End E) :
    averaging R (fun h ↦ (ρ h).asHom) ≫ averaging R (fun h ↦ (ρ h).asHom) =
      averaging R (fun h ↦ (ρ h).asHom) := by
  nth_rewrite 2 [averaging]
  rw [Linear.comp_smul, Preadditive.comp_sum]
  simp only [averaging_comp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, invOf_mul_self, one_smul]

variable {C' : Type u₂} [Category.{v₂} C'] [Preadditive C'] [Linear R C'] (D : Cᵒᵖ ⥤ C')
  [D.Additive]

/-- The **contragredient action** `h ↦ D(ρ(h⁻¹))` of `G` on `D E`, for a contravariant functor
`D`. -/
@[simps]
def contragredient {E : C} (ρ : G →* End E) : G →* End (D.obj (op E)) where
  toFun h := End.of (D.map (ρ h⁻¹).asHom.op)
  map_one' := by
    apply End.ext
    change D.map (ρ 1⁻¹).asHom.op = 𝟙 _
    rw [inv_one, map_one, End.one_asHom, op_id, D.map_id]
  map_mul' g h := by
    apply End.ext
    change D.map (ρ (g * h)⁻¹).asHom.op =
      D.map (ρ h⁻¹).asHom.op ≫ D.map (ρ g⁻¹).asHom.op
    rw [mul_inv_rev, map_mul, End.mul_asHom, op_comp, D.map_comp]

/-- **Duality sends the averaging idempotent to the averaging idempotent of the contragredient
action**, since inversion `h ↦ h⁻¹` permutes the summands. Only additivity of `D` is used: the
scalar `|G|⁻¹` is recovered from `|G| ⬝ e = ∑ ρ(h)`. -/
theorem map_averaging_op {E : C} (ρ : G → (E ⟶ E)) :
    D.map (averaging R ρ).op = averaging R (fun h ↦ D.map (ρ h⁻¹).op) := by
  have hS : Fintype.card G • D.map (averaging R ρ).op = ∑ h, D.map (ρ h⁻¹).op := by
    rw [← Functor.map_nsmul, ← natCast_zsmul, ← op_zsmul, natCast_zsmul, nsmul_averaging,
      op_sum, Functor.map_sum]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ fun h ↦ by simp
  conv_rhs => rw [averaging, ← hS]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, invOf_mul_self, one_smul]

/-- **Duality commutes with invariants** under a finite group of invertible order (blueprint
`lemma-duality-invariants-pro-p--1`, finite case): if `ι : E^G ⟶ E`, `π : E ⟶ E^G` split the
averaging idempotent of `ρ` and `ι'`, `π'` split the averaging idempotent of the contragredient
action on `D E`, then `(D E)^G ⟶ D E ⟶ D(E^G)` is an isomorphism `(D E)^G ≅ D(E^G)`. -/
noncomputable def invariantsDualIso {E I : C} (ρ : G →* End E) {ι : I ⟶ E} {π : E ⟶ I}
    (hιπ : ι ≫ π = 𝟙 I) (hπι : π ≫ ι = averaging R (fun h ↦ (ρ h).asHom))
    {I' : C'} {ι' : I' ⟶ D.obj (op E)}
    {π' : D.obj (op E) ⟶ I'} (hιπ' : ι' ≫ π' = 𝟙 I')
    (hπι' : π' ≫ ι' = averaging R (fun h ↦ (contragredient D ρ h).asHom)) :
    I' ≅ D.obj (op I) :=
  splitDualIso D hιπ hπι hιπ' (by rw [hπι', map_averaging_op]; rfl)

@[simp]
lemma invariantsDualIso_hom {E I : C} (ρ : G →* End E) {ι : I ⟶ E} {π : E ⟶ I}
    (hιπ : ι ≫ π = 𝟙 I) (hπι : π ≫ ι = averaging R (fun h ↦ (ρ h).asHom))
    {I' : C'} {ι' : I' ⟶ D.obj (op E)}
    {π' : D.obj (op E) ⟶ I'} (hιπ' : ι' ≫ π' = 𝟙 I')
    (hπι' : π' ≫ ι' = averaging R (fun h ↦ (contragredient D ρ h).asHom)) :
    (invariantsDualIso D ρ hιπ hπι hιπ' hπι').hom = ι' ≫ D.map ι.op :=
  rfl

end Averaging

section Pairing

open MonoidalCategory MonoidalClosed

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

/-- **The invariant pairing is the restriction of evaluation** (blueprint
`lemma-duality-invariants-pro-p--1`): for Verdier duality `D = RHom(-, ω)`, the pairing
`E^G ⊗ (D E)^G ⟶ ω` adjoint to `ι' ≫ D(ι) : (D E)^G ⟶ D(E^G)` is the evaluation
`E ⊗ D E ⟶ ω` restricted along the inclusions `ι ⊗ ι'` of the two invariant direct summands. -/
lemma uncurry_invariantsDualIso_hom (ω : C) {E I I' : C} (ι : I ⟶ E)
    (ι' : I' ⟶ (ihom E).obj ω) :
    uncurry (ι' ≫ (MonoidalClosed.internalHom.flip.obj ω).map ι.op) =
      (ι ⊗ₘ ι') ≫ (ihom.ev E).app ω := by
  change uncurry (ι' ≫ (pre ι).app ω) = _
  rw [uncurry_pre_app, uncurry_eq, tensorHom_def, Category.assoc]

end Pairing

end CategoryTheory
