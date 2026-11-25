/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.Algebra.Field.Opposite
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Preadditive.EndModule
public import WeilConjectures.Mathlib.LinearAlgebra.Basis.VectorSpace
public import WeilConjectures.CategoryTheory.Monoidal.EndTensorUnit
public import WeilConjectures.TraceFormula.CategoricalTrace

/-!
# Objects with a basis of copies of the monoidal unit

A *unit basis* of an object `X` of a preadditive monoidal category
(`CategoryTheory.MonoidalCategory.UnitBasis`) is a presentation of `X` as a finite biproduct of
copies of the unit `𝟙_ C`: inclusions `𝟙_ C ⟶ X` and projections `X ⟶ 𝟙_ C` satisfying the
biproduct relations.

Such an `X` is its own right dual (`CategoryTheory.MonoidalCategory.UnitBasis.exactPairing`), and
the categorical trace of an endomorphism `φ` is the sum of its diagonal entries
`incl i ≫ φ ≫ proj i` (`CategoryTheory.MonoidalCategory.UnitBasis.traceOrZero_eq_sum`).

The morphisms `𝟙_ C ⟶ X` form a module over `(End (𝟙_ C))ᵐᵒᵖ`, with basis the inclusions
(`CategoryTheory.MonoidalCategory.UnitBasis.basis`), and the categorical trace of `φ` is the trace
of the linear map `x ↦ x ≫ φ` (`CategoryTheory.MonoidalCategory.UnitBasis.trace_rightCompEndOp`).
Every linear map between such modules comes from a morphism, and when `End (𝟙_ C)` is a field this
gives, in an abelian category, that `Hom(𝟙_ C, -)` sends exact sequences of objects with unit
bases to exact sequences of vector spaces
(`CategoryTheory.MonoidalCategory.UnitBasis.exact_rightCompEndOp`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- A *unit basis* of `X` indexed by a finite type `ι`: a presentation of `X` as the biproduct
of copies of the monoidal unit indexed by `ι`, given by inclusions and projections satisfying the
biproduct relations. -/
structure UnitBasis (X : C) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The inclusion of the `i`-th copy of the unit. -/
  incl : ι → (𝟙_ C ⟶ X)
  /-- The projection onto the `i`-th copy of the unit. -/
  proj : ι → (X ⟶ 𝟙_ C)
  incl_proj (i j : ι) : incl i ≫ proj j = if i = j then 𝟙 _ else 0
  total : ∑ i, proj i ≫ incl i = 𝟙 X

namespace UnitBasis

variable {X : C} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unit basis of an object isomorphic to the biproduct of copies of the unit. -/
noncomputable def ofIso [HasBiproduct fun _ : ι ↦ 𝟙_ C] (e : X ≅ ⨁ fun _ : ι ↦ 𝟙_ C) :
    UnitBasis X ι where
  incl i := biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ e.inv
  proj i := e.hom ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) i
  incl_proj i j := by
    rw [Category.assoc, e.inv_hom_id_assoc, biproduct.ι_π]
    split_ifs <;> rfl
  total := by
    calc ∑ i, (e.hom ≫ biproduct.π _ i) ≫ biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ e.inv =
        e.hom ≫ (∑ i, biproduct.π _ i ≫ biproduct.ι (fun _ : ι ↦ 𝟙_ C) i) ≫ e.inv := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
      _ = 𝟙 X := by
        rw [IsBilimit.total (biproduct.isBilimit _), Category.id_comp, e.hom_inv_id]

variable (b : UnitBasis X ι)

/-- Morphisms out of an object with a unit basis are determined by their restrictions to the
copies of the unit. -/
lemma hom_ext {Y : C} {f g : X ⟶ Y} (h : ∀ i, b.incl i ≫ f = b.incl i ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g, ← b.total, Preadditive.sum_comp,
    Preadditive.sum_comp]
  simp only [Category.assoc, h]

section Dual

omit [Preadditive C] in
/-- A coevaluation `𝟙_ C ⟶ M ⊗ N'` and an evaluation `N ⊗ M ⟶ 𝟙_ C` through copies of the unit
compose, in the first zig-zag shape, to `q ≫ (i ≫ p) ≫ j` up to unitors. -/
lemma whiskerLeft_rightUnitor_inv_tensorHom_comp {M N N' : C} (i : 𝟙_ C ⟶ M) (j : 𝟙_ C ⟶ N')
    (q : N ⟶ 𝟙_ C) (p : M ⟶ 𝟙_ C) :
    N ◁ ((ρ_ (𝟙_ C)).inv ≫ (i ⊗ₘ j)) ≫ (α_ N M N').inv ≫ ((q ⊗ₘ p) ≫ (ρ_ (𝟙_ C)).hom) ▷ N' =
      (ρ_ N).hom ≫ q ≫ (i ≫ p) ≫ j ≫ (λ_ N').inv := by
  let : HasRightDual (𝟙_ C) := ⟨𝟙_ C⟩
  refine (whiskerLeft_coevaluation_evaluation (A := 𝟙_ C) (B := 𝟙_ C) i j q p).trans ?_
  have hη : η_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ _).inv := rfl
  have hε : ε_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ _).hom := rfl
  simp only [whiskerRight_id, id_whiskerLeft, hη, hε]
  monoidal

omit [Preadditive C] in
/-- A coevaluation `𝟙_ C ⟶ M ⊗ N` and an evaluation `N ⊗ M' ⟶ 𝟙_ C` through copies of the unit
compose, in the second zig-zag shape, to `p ≫ (j ≫ q) ≫ i` up to unitors. -/
lemma rightUnitor_inv_tensorHom_whiskerRight_comp {M N M' : C} (i : 𝟙_ C ⟶ M) (j : 𝟙_ C ⟶ N)
    (q : N ⟶ 𝟙_ C) (p : M' ⟶ 𝟙_ C) :
    ((ρ_ (𝟙_ C)).inv ≫ (i ⊗ₘ j)) ▷ M' ≫ (α_ M N M').hom ≫ M ◁ ((q ⊗ₘ p) ≫ (ρ_ (𝟙_ C)).hom) =
      (λ_ M').hom ≫ p ≫ (j ≫ q) ≫ i ≫ (ρ_ M).inv := by
  let : HasRightDual (𝟙_ C) := ⟨𝟙_ C⟩
  refine (whiskerRight_coevaluation_evaluation (A := 𝟙_ C) (B := 𝟙_ C) i j q p).trans ?_
  have hη : η_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ _).inv := rfl
  have hε : ε_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ _).hom := rfl
  simp only [whiskerRight_id, id_whiskerLeft, hη, hε]
  monoidal

/-- A double sum `∑ⱼ ∑ᵢ f ≫ proj j ≫ (incl i ≫ proj j) ≫ incl i ≫ g` collapses to `f ≫ g`. -/
lemma sum_sum_comp_incl_proj_comp {Y Z : C} (f : Y ⟶ X) (g : X ⟶ Z) :
    ∑ j, ∑ i, f ≫ b.proj j ≫ (b.incl i ≫ b.proj j) ≫ b.incl i ≫ g = f ≫ g := by
  simp only [b.incl_proj]
  have h (i j : ι) : f ≫ b.proj j ≫ (if i = j then 𝟙 (𝟙_ C) else 0) ≫ b.incl i ≫ g =
      if i = j then f ≫ b.proj j ≫ b.incl j ≫ g else 0 := by
    split_ifs with hij
    · rw [hij, Category.id_comp]
    · rw [zero_comp, comp_zero, comp_zero]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Preadditive.comp_sum]
  simp only [← Category.assoc, ← Preadditive.sum_comp]
  rw [Category.assoc, b.total, Category.id_comp]

variable [MonoidalPreadditive C]

/-- An object with a unit basis is its own right dual, with coevaluation
`∑ᵢ incl i ⊗ incl i` and evaluation `∑ᵢ proj i ⊗ proj i`. -/
@[instance_reducible]
noncomputable def exactPairing : ExactPairing X X where
  coevaluation' := ∑ i, (ρ_ (𝟙_ C)).inv ≫ (b.incl i ⊗ₘ b.incl i)
  evaluation' := ∑ i, (b.proj i ⊗ₘ b.proj i) ≫ (ρ_ (𝟙_ C)).hom
  coevaluation_evaluation' := by
    simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
      whiskerLeft_rightUnitor_inv_tensorHom_comp]
    exact b.sum_sum_comp_incl_proj_comp _ _
  evaluation_coevaluation' := by
    simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
      rightUnitor_inv_tensorHom_whiskerRight_comp]
    exact b.sum_sum_comp_incl_proj_comp _ _

end Dual

section Trace

omit [Preadditive C] in
/-- A coevaluation and an evaluation through copies of the unit, composed with an endomorphism
and the braiding as in the definition of the trace, give the product of the scalars
`j ≫ q` and `i ≫ φ ≫ p`. -/
lemma rightUnitor_inv_tensorHom_braiding_comp [BraidedCategory C] {M M' N : C} (i : 𝟙_ C ⟶ M)
    (j : 𝟙_ C ⟶ N) (φ : M ⟶ M') (q : N ⟶ 𝟙_ C) (p : M' ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (i ⊗ₘ j) ≫ φ ▷ N ≫ (β_ M' N).hom ≫ (q ⊗ₘ p) ≫ (ρ_ (𝟙_ C)).hom =
      (j ≫ q) ≫ i ≫ φ ≫ p := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    BraidedCategory.braiding_naturality_assoc, tensorHom_comp_tensorHom_assoc,
    braiding_tensorUnit_left, unitors_equal, Category.assoc, Iso.inv_hom_id_assoc,
    rightUnitor_inv_comp_tensorHom_comp_rightUnitor_hom]
  simp only [Category.assoc]

variable [MonoidalPreadditive C] [BraidedCategory C]

/-- The categorical trace of an endomorphism of an object with a unit basis is the sum of its
diagonal entries. -/
theorem traceOrZero_eq_sum (φ : X ⟶ X) :
    traceOrZero φ = ∑ i, End.of (b.incl i ≫ φ ≫ b.proj i) := by
  let := b.exactPairing
  let : HasRightDual X := ⟨X⟩
  apply End.ext
  simp only [End.sum_asHom]
  rw [traceOrZero_eq_trace, trace_eq_of_exactPairing X]
  have hη : η_ X X = ∑ i, (ρ_ (𝟙_ C)).inv ≫ (b.incl i ⊗ₘ b.incl i) := rfl
  have hε : ε_ X X = ∑ i, (b.proj i ⊗ₘ b.proj i) ≫ (ρ_ (𝟙_ C)).hom := rfl
  rw [hη, hε]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
    rightUnitor_inv_tensorHom_braiding_comp, b.incl_proj]
  have h (i j : ι) : (if i = j then 𝟙 (𝟙_ C) else 0) ≫ b.incl i ≫ φ ≫ b.proj j =
      if i = j then b.incl i ≫ φ ≫ b.proj i else 0 := by
    split_ifs with hij
    · rw [hij, Category.id_comp]
    · rw [zero_comp]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Trace

section Linear

/-- The inclusions of a unit basis of `X` form a basis of the `(End (𝟙_ C))ᵐᵒᵖ`-module
`𝟙_ C ⟶ X`, the coordinates of `x` being the `x ≫ proj i`. -/
noncomputable def basis : Module.Basis ι (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) :=
  .ofEquivFun
    { toFun x i := .op (.of (x ≫ b.proj i))
      invFun c := ∑ i, c i • b.incl i
      map_add' x y := by
        funext i
        apply MulOpposite.unop_injective
        apply End.ext
        simp
      map_smul' r x := by
        funext i
        apply MulOpposite.unop_injective
        apply End.ext
        simp [End.smul_left, End.mul_asHom]
      left_inv x := by
        simp only [End.smul_left, MulOpposite.unop_op, Category.assoc, ← Preadditive.comp_sum,
          b.total, Category.comp_id]
      right_inv c := by
        funext j
        apply MulOpposite.unop_injective
        apply End.ext
        simp only [MulOpposite.unop_op, End.smul_left, Preadditive.sum_comp, Category.assoc,
          b.incl_proj]
        rw [Finset.sum_eq_single j (fun x _ hx ↦ by simp [hx]) (by simp)]
        simp }

@[simp]
lemma basis_apply (i : ι) : b.basis i = b.incl i := by
  rw [basis, Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.coe_symm_mk, End.smul_left]
  rw [Finset.sum_eq_single i (fun x _ hx ↦ by simp [hx]) (by simp)]
  simp

@[simp]
lemma basis_repr_apply (x : 𝟙_ C ⟶ X) (i : ι) : b.basis.repr x i = .op (.of (x ≫ b.proj i)) :=
  rfl

/-- The module `𝟙_ C ⟶ X` is finite when `X` has a unit basis. -/
lemma moduleFinite (b : UnitBasis X ι) : Module.Finite (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) :=
  Module.Finite.of_basis b.basis

/-- Morphisms `X ⟶ Y` are determined by the linear maps `(𝟙_ C ⟶ X) → (𝟙_ C ⟶ Y)` they
induce. -/
lemma rightCompEndOp_injective (b : UnitBasis X ι) {Y : C} :
    Function.Injective (Preadditive.rightCompEndOp (𝟙_ C) (Y := X) (Z := Y)) :=
  fun _ _ h ↦ b.hom_ext fun i ↦ LinearMap.congr_fun h (b.incl i)

/-- Every linear map `(𝟙_ C ⟶ X) → (𝟙_ C ⟶ Y)` is induced by a morphism `X ⟶ Y`, namely
`∑ᵢ proj i ≫ L (incl i)`. -/
lemma exists_rightCompEndOp_eq (b : UnitBasis X ι) {Y : C}
    (L : (𝟙_ C ⟶ X) →ₗ[(End (𝟙_ C))ᵐᵒᵖ] (𝟙_ C ⟶ Y)) :
    ∃ g : X ⟶ Y, Preadditive.rightCompEndOp _ g = L := by
  refine ⟨∑ i, b.proj i ≫ L (b.incl i), LinearMap.ext fun x ↦ ?_⟩
  conv_rhs => rw [← b.basis.sum_repr x]
  rw [map_sum]
  simp only [map_smul]
  simp only [End.smul_left, basis_apply, basis_repr_apply,
    MulOpposite.unop_op, Preadditive.comp_sum, Preadditive.rightCompEndOp_apply, Category.assoc]

/-- If `End (𝟙_ C)` is a field, every morphism between objects with unit bases has a generalized
inverse. -/
lemma exists_comp_comp_eq_self (hK : IsField (End (𝟙_ C))) (b : UnitBasis X ι) {Y : C}
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b' : UnitBasis Y κ) (f : X ⟶ Y) :
    ∃ s : Y ⟶ X, f ≫ s ≫ f = f := by
  let := hK.toField
  obtain ⟨S, hS⟩ := (Preadditive.rightCompEndOp (𝟙_ C) f).exists_comp_comp_eq_self
  obtain ⟨s, rfl⟩ := b'.exists_rightCompEndOp_eq S
  refine ⟨s, b.rightCompEndOp_injective (LinearMap.ext fun x ↦ ?_)⟩
  simpa using LinearMap.congr_fun hS x

/-- The categorical trace of an endomorphism `φ` of an object with a unit basis is the trace of
the linear map `x ↦ x ≫ φ` on `𝟙_ C ⟶ X`. -/
theorem trace_rightCompEndOp [MonoidalPreadditive C] [BraidedCategory C] (b : UnitBasis X ι)
    (φ : X ⟶ X) :
    LinearMap.trace (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) (Preadditive.rightCompEndOp _ φ) =
      .op (traceOrZero φ) := by
  rw [LinearMap.trace_eq_matrix_trace _ b.basis, Matrix.trace, b.traceOrZero_eq_sum]
  simp [LinearMap.toMatrix_apply]

end Linear

end UnitBasis

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]

/-- If `End (𝟙_ C)` is a field, `Hom(𝟙_ C, -)` sends an exact sequence `X ⟶ Y ⟶ Z` with `X`
and `Y` having unit bases to an exact sequence of vector spaces over `(End (𝟙_ C))ᵐᵒᵖ`. -/
theorem UnitBasis.exact_rightCompEndOp (hK : IsField (End (𝟙_ C))) {X Y Z : C} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (bX : UnitBasis X ι)
    (bY : UnitBasis Y κ) {f : X ⟶ Y} {g : Y ⟶ Z} {hfg : f ≫ g = 0}
    (hS : (ShortComplex.mk f g hfg).Exact) :
    Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) f) (Preadditive.rightCompEndOp (𝟙_ C) g) :=
  have ⟨_, hs⟩ := bX.exists_comp_comp_eq_self hK bY f
  Preadditive.exact_rightCompEndOp_of_comp_comp_eq _ hS hs

end Abelian

end MonoidalCategory

end CategoryTheory
