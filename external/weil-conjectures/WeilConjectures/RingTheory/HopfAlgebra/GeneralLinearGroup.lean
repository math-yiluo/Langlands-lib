/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The Hopf algebra of `GL_n`

The coordinate ring of the general linear group over a commutative ring `k` is
`k[x_ij, det⁻¹]`, the localization of the polynomial ring `k[x_ij]` away from the determinant of
the generic matrix `(x_ij)`. It is a commutative Hopf algebra over `k`: the comultiplication is
`x_ij ↦ ∑ₗ x_il ⊗ x_lj` (matrix multiplication), the counit is evaluation at the identity matrix
and the antipode sends `x_ij` to the `(i, j)` entry of the inverse of the generic matrix.

A `k`-algebra homomorphism `k[x_ij, det⁻¹] → R` is the same as an invertible matrix over `R`:
`Matrix.GeneralLinearGroup.evalAlgHom g` is evaluation at `g : GL n R`, and all three structure
maps are instances of it. Evaluation turns matrix multiplication into the convolution product,
so the coordinate ring represents the group functor `R ↦ GL n R`
(`Matrix.GeneralLinearGroup.algHomMulEquiv`).

## Main definitions

- `Matrix.GeneralLinearGroup.CoordinateRing`: the coordinate ring `k[x_ij, det⁻¹]` of `GL_n`,
  with its `HopfAlgebra k` instance.
- `Matrix.GeneralLinearGroup.coord`: the coordinate function `x_ij`.
- `Matrix.GeneralLinearGroup.evalAlgHom`: evaluation at an invertible matrix.
- `Matrix.GeneralLinearGroup.comulAlgHom`, `counitAlgHom`, `antipodeAlgHom`: the Hopf algebra
  structure maps.
- `Matrix.GeneralLinearGroup.algHomMulEquiv`: `k`-algebra homomorphisms out of the coordinate ring,
  with the convolution product, are the invertible matrices.

## Blueprint

- `det-d-geometry`: the ambient group `GL(V)` of the algebraic groups block, given by its
  Hopf algebra of coordinates.
-/

@[expose] public section

open TensorProduct

namespace Matrix.GeneralLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (k : Type*) [CommRing k]

/-- The generic `n × n` matrix `(x_ij)` over the polynomial ring `k[x_ij]`. -/
noncomputable abbrev genericMatrix : Matrix n n (MvPolynomial (n × n) k) :=
  Matrix.mvPolynomialX n n k

/-- The coordinate ring `k[x_ij, det⁻¹]` of the general linear group `GL_n` over `k`: the
polynomial ring in the matrix entries, localized away from the determinant.
(blueprint: `det-d-geometry`) -/
abbrev CoordinateRing :=
  Localization.Away (genericMatrix n k).det

/-- The coordinate function `x_ij` on `GL_n`. -/
noncomputable def coord (i j : n) : CoordinateRing n k :=
  algebraMap (MvPolynomial (n × n) k) _ (MvPolynomial.X (i, j))

variable {n k}

/-- Two `k`-algebra homomorphisms out of the coordinate ring of `GL_n` agreeing on the coordinate
functions are equal. -/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra k A] {f g : CoordinateRing n k →ₐ[k] A}
    (h : ∀ i j, f (coord n k i j) = g (coord n k i j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (genericMatrix n k).det)
  ext ⟨i, j⟩
  exact h i j

/-- Evaluating the determinant of the generic matrix at an invertible matrix gives a unit. -/
theorem isUnit_aeval_det {R : Type*} [CommRing R] [Algebra k R] (g : GL n R) :
    IsUnit ((MvPolynomial.aeval fun p : n × n ↦ (g : Matrix n n R) p.1 p.2)
      (genericMatrix n k).det) := by
  rw [AlgHom.map_det, mvPolynomialX_mapMatrix_aeval]
  exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

/-- Evaluation of the coordinate ring of `GL_n` at an invertible matrix `g` over a
`k`-algebra `R`, sending `x_ij` to `g i j`. -/
noncomputable def evalAlgHom {R : Type*} [CommRing R] [Algebra k R] (g : GL n R) :
    CoordinateRing n k →ₐ[k] R :=
  IsLocalization.Away.liftAlgHom (genericMatrix n k).det
    (f := MvPolynomial.aeval fun p : n × n ↦ (g : Matrix n n R) p.1 p.2) (isUnit_aeval_det g)

@[simp]
theorem evalAlgHom_coord {R : Type*} [CommRing R] [Algebra k R] (g : GL n R) (i j : n) :
    evalAlgHom g (coord n k i j) = (g : Matrix n n R) i j := by
  simp [evalAlgHom, coord]

variable (n k)

/-- The determinant of the generic matrix is a unit in the coordinate ring of `GL_n`. -/
theorem isUnit_det_map_genericMatrix :
    IsUnit ((genericMatrix n k).map (algebraMap _ (CoordinateRing n k))).det := by
  have := IsLocalization.Away.algebraMap_isUnit (S := CoordinateRing n k) (genericMatrix n k).det
  rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this

/-- The generic invertible matrix `(x_ij)` over the coordinate ring of `GL_n`. -/
noncomputable def genericUnit : GL n (CoordinateRing n k) :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_map_genericMatrix n k)).unit

@[simp]
theorem coe_genericUnit_apply (i j : n) :
    (genericUnit n k : Matrix n n (CoordinateRing n k)) i j = coord n k i j := by
  simp [genericUnit, coord]

/-- The comultiplication of the coordinate ring of `GL_n`, `x_ij ↦ ∑ₗ x_il ⊗ x_lj`: evaluation at
the product of the two copies of the generic matrix in `A ⊗ A`. -/
noncomputable def comulAlgHom :
    CoordinateRing n k →ₐ[k] CoordinateRing n k ⊗[k] CoordinateRing n k :=
  evalAlgHom (map Algebra.TensorProduct.includeLeftRingHom (genericUnit n k) *
    map Algebra.TensorProduct.includeRight.toRingHom (genericUnit n k))

@[simp]
theorem comulAlgHom_coord (i j : n) :
    comulAlgHom n k (coord n k i j) = ∑ l, coord n k i l ⊗ₜ[k] coord n k l j := by
  simp [comulAlgHom, Matrix.mul_apply]

/-- The counit of the coordinate ring of `GL_n`: evaluation at the identity matrix. -/
noncomputable def counitAlgHom : CoordinateRing n k →ₐ[k] k :=
  evalAlgHom (1 : GL n k)

/-- The antipode of the coordinate ring of `GL_n`, sending `x_ij` to the `(i, j)` entry of the
inverse of the generic matrix. -/
noncomputable def antipodeAlgHom : CoordinateRing n k →ₐ[k] CoordinateRing n k :=
  evalAlgHom (genericUnit n k)⁻¹

@[simp]
theorem counitAlgHom_coord (i j : n) :
    counitAlgHom n k (coord n k i j) = (1 : Matrix n n k) i j := by
  simp [counitAlgHom]

@[simp]
theorem antipodeAlgHom_coord (i j : n) :
    antipodeAlgHom n k (coord n k i j) =
      ((genericUnit n k)⁻¹ : GL n (CoordinateRing n k)) i j := by
  simp [antipodeAlgHom]

theorem comulAlgHom_coassoc :
    (Algebra.TensorProduct.assoc k k k (CoordinateRing n k) (CoordinateRing n k)
      (CoordinateRing n k)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlgHom n k) (.id k _)).comp (comulAlgHom n k)) =
      (Algebra.TensorProduct.map (.id k _) (comulAlgHom n k)).comp (comulAlgHom n k) := by
  refine algHom_ext fun i j ↦ ?_
  simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply, comulAlgHom_coord,
    map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, TensorProduct.sum_tmul,
    Algebra.TensorProduct.assoc_tmul, TensorProduct.tmul_sum]
  exact Finset.sum_comm

theorem map_counitAlgHom_id_comp_comulAlgHom :
    (Algebra.TensorProduct.map (counitAlgHom n k) (.id k _)).comp (comulAlgHom n k) =
      (Algebra.TensorProduct.lid k (CoordinateRing n k)).symm := by
  refine algHom_ext fun i j ↦ ?_
  simp [Matrix.one_apply, TensorProduct.ite_tmul]

theorem map_id_counitAlgHom_comp_comulAlgHom :
    (Algebra.TensorProduct.map (.id k _) (counitAlgHom n k)).comp (comulAlgHom n k) =
      (Algebra.TensorProduct.rid k k (CoordinateRing n k)).symm := by
  refine algHom_ext fun i j ↦ ?_
  simp [Matrix.one_apply, TensorProduct.tmul_ite]

/-- The coordinate ring of `GL_n` is a bialgebra, with comultiplication given by matrix
multiplication and counit given by evaluation at the identity. -/
noncomputable instance : Bialgebra k (CoordinateRing n k) :=
  Bialgebra.ofAlgHom (comulAlgHom n k) (counitAlgHom n k) (comulAlgHom_coassoc n k)
    (map_counitAlgHom_id_comp_comulAlgHom n k) (map_id_counitAlgHom_comp_comulAlgHom n k)

@[simp]
theorem comul_coord (i j : n) :
    Coalgebra.comul (R := k) (coord n k i j) = ∑ l, coord n k i l ⊗ₜ[k] coord n k l j :=
  comulAlgHom_coord n k i j

@[simp]
theorem counit_coord (i j : n) :
    Coalgebra.counit (R := k) (coord n k i j) = (1 : Matrix n n k) i j :=
  counitAlgHom_coord n k i j

/-- Two `k`-algebra homomorphisms `f` and `g` out of the coordinate ring of `GL_n`, combined along
the comultiplication, send `x_ij` to the `(i, j)` entry of the product of the matrices
`(f(x_ij))` and `(g(x_ij))`. -/
theorem lift_comul_coord {R : Type*} [CommRing R] [Algebra k R]
    (f g : CoordinateRing n k →ₐ[k] R) (i j : n) :
    Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) (Coalgebra.comul (coord n k i j)) =
      ((genericUnit n k : Matrix n n (CoordinateRing n k)).map f *
        (genericUnit n k : Matrix n n (CoordinateRing n k)).map g) i j := by
  simp [Matrix.mul_apply]

/-- The antipode sends the generic matrix to its inverse. -/
@[simp]
theorem map_antipodeAlgHom_genericUnit :
    (genericUnit n k : Matrix n n (CoordinateRing n k)).map (antipodeAlgHom n k) =
      ((genericUnit n k)⁻¹ : GL n (CoordinateRing n k)) := by
  ext
  simp

theorem mul_antipodeAlgHom_rTensor_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom n k) (.id k _) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom k (CoordinateRing n k)) =
        (Algebra.ofId k _).comp (Bialgebra.counitAlgHom k (CoordinateRing n k)) := by
  refine algHom_ext fun i j ↦ ?_
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, lift_comul_coord, AlgHom.comp_apply,
    Bialgebra.counitAlgHom_apply, counit_coord]
  simp [Matrix.one_apply]

theorem mul_antipodeAlgHom_lTensor_comulAlgHom :
    (Algebra.TensorProduct.lift (.id k _) (antipodeAlgHom n k) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom k (CoordinateRing n k)) =
        (Algebra.ofId k _).comp (Bialgebra.counitAlgHom k (CoordinateRing n k)) := by
  refine algHom_ext fun i j ↦ ?_
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, lift_comul_coord, AlgHom.comp_apply,
    Bialgebra.counitAlgHom_apply, counit_coord]
  simp [Matrix.one_apply]

/-- The coordinate ring of `GL_n` is a commutative Hopf algebra over `k`.
(blueprint: `det-d-geometry`) -/
noncomputable instance : HopfAlgebra k (CoordinateRing n k) :=
  HopfAlgebra.ofAlgHom (antipodeAlgHom n k) (mul_antipodeAlgHom_rTensor_comulAlgHom n k)
    (mul_antipodeAlgHom_lTensor_comulAlgHom n k)

/-- The coordinate ring of `GL_n` is a finitely generated `k`-algebra. -/
example : Algebra.FiniteType k (CoordinateRing n k) := inferInstance

variable {n k}

/-- Evaluation turns matrix multiplication into the convolution product. -/
theorem evalAlgHom_mul {R : Type*} [CommRing R] [Algebra k R] (g h : GL n R) :
    WithConv.toConv (evalAlgHom (k := k) (g * h)) =
      WithConv.toConv (evalAlgHom g) * WithConv.toConv (evalAlgHom h) := by
  ext1
  refine algHom_ext fun i j ↦ ?_
  simp [AlgHom.convMul_apply, Matrix.mul_apply]

/-- Evaluation at the identity matrix is the convolution unit. -/
theorem evalAlgHom_one {R : Type*} [CommRing R] [Algebra k R] :
    WithConv.toConv (evalAlgHom (k := k) (1 : GL n R)) = 1 := by
  ext1
  refine algHom_ext fun i j ↦ ?_
  simp [AlgHom.convOne_apply, Matrix.one_apply, apply_ite (algebraMap k R)]

variable (n k) (R : Type*) [CommRing R] [Algebra k R]

/-- `k`-algebra homomorphisms from the coordinate ring of `GL_n` to `R`, with the convolution
product, are the invertible `n × n` matrices over `R`: a homomorphism `φ` corresponds to the image
`(φ(x_ij))` of the generic matrix, and an invertible matrix `g` to evaluation at `g`. -/
noncomputable def algHomMulEquiv : WithConv (CoordinateRing n k →ₐ[k] R) ≃* GL n R :=
  MulEquiv.symm
    { toFun g := WithConv.toConv (evalAlgHom g)
      invFun φ := map φ.ofConv.toRingHom (genericUnit n k)
      left_inv g := by
        ext i j
        simp
      right_inv φ := by
        ext1
        exact algHom_ext fun i j ↦ by simp
      map_mul' := evalAlgHom_mul }

variable {n k R}

@[simp]
theorem algHomMulEquiv_apply (φ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    algHomMulEquiv n k R φ = map φ.ofConv.toRingHom (genericUnit n k) :=
  rfl

@[simp]
theorem algHomMulEquiv_symm_apply (g : GL n R) :
    (algHomMulEquiv n k R).symm g = WithConv.toConv (evalAlgHom g) :=
  rfl

variable {S : Type*} [CommRing S] [Algebra k S]

/-- Evaluation at the image of `g` under an algebra homomorphism `φ : R → S` is evaluation at `g`
followed by `φ`. -/
theorem evalAlgHom_map (φ : R →ₐ[k] S) (g : GL n R) :
    evalAlgHom (k := k) (map φ.toRingHom g) = φ.comp (evalAlgHom g) :=
  algHom_ext fun i j ↦ by simp

/-- The identification `algHomMulEquiv` is natural in the algebra of values. -/
theorem map_algHomMulEquiv (φ : R →ₐ[k] S) (ψ : CoordinateRing n k →ₐ[k] R) :
    map φ.toRingHom (algHomMulEquiv n k R (WithConv.toConv ψ)) =
      algHomMulEquiv n k S (WithConv.toConv (φ.comp ψ)) :=
  Units.ext (Matrix.ext fun _ _ ↦ rfl)

end Matrix.GeneralLinearGroup
