/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.Quotient
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
public import WeilConjectures.Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Mathlib.Topology.Connected.Basic
public import WeilConjectures.RingTheory.HopfAlgebra.Cartier
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# Hopf ideals of the coordinate ring of `GL_n` and their zero loci

This file is the purely algebraic side of the theory of closed subgroups of `GL_n`: it concerns
Hopf ideals `I` of the Hopf algebra `k[x_ij, det⁻¹]` and matrix groups, and never mentions
schemes. The group scheme `V(I)` itself and the comparison of its points with the matrix groups
defined here are in `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup`.

For a Hopf ideal `I` and a `k`-algebra `R`, the invertible matrices over `R` on which every
equation in `I` vanishes form a subgroup `zeroLocus I R` of `GL n R`. Conversely, an abstract
subgroup `Γ` of `GL n k` has a Zariski closure, cut out by the ideal `vanishingIdeal Γ` of all
equations vanishing on `Γ`; this ideal is a Hopf ideal. Over an algebraically closed field the
Nullstellensatz identifies the ideal of the `k`-points of `zeroLocus I` with the radical of `I`.
Finally, the identity component and the centre of `V(I)` are described by Hopf ideals of
`k[x_ij, det⁻¹]`.

## Main definitions

- `Matrix.GeneralLinearGroup.zeroLocus`: the subgroup of `GL n R` of matrices satisfying the
  equations of a Hopf ideal `I`.
- `Matrix.GeneralLinearGroup.vanishingIdeal`: the ideal of equations vanishing on a set of
  matrices; for a subgroup, the ideal of its Zariski closure.
- `Matrix.GeneralLinearGroup.toPrimeSpectrum`: the point of `Spec k[x_ij, det⁻¹]` given by a
  matrix in `GL n k`.
- `Matrix.GeneralLinearGroup.identityComponent`: the ideal of the reduced identity component
  `G°` of `V(I)`.
- `Matrix.GeneralLinearGroup.IsConnected`: `I` is the ideal of its own reduced identity component.
- `Matrix.GeneralLinearGroup.centerPoints`: the matrices of `G(k)` commuting with all of `G(k)`.
- `Matrix.GeneralLinearGroup.center`: the ideal of the reduced centre `Z(G)` of `V(I)`, for `k`
  algebraically closed.
- `Matrix.GeneralLinearGroup.translate`, `Matrix.GeneralLinearGroup.translateHomeomorph`: the
  two-sided translation `x ↦ g * x * h` on the coordinate ring of `GL_n` and on its spectrum.
- `Matrix.GeneralLinearGroup.conjBialgHom`: the bialgebra endomorphism of the coordinate ring
  pulling back along the conjugation `x ↦ g * x * g⁻¹`.
- `Matrix.GeneralLinearGroup.identityComponentSubgroup`: the `k`-points of the identity component,
  as a subgroup of `GL n k`.

## Main results

- `Matrix.GeneralLinearGroup.instIsHopfIdealVanishingIdeal`: the ideal of a subgroup of `GL n k`
  is a Hopf ideal.
- `Matrix.GeneralLinearGroup.vanishingIdeal_zeroLocus_eq_radical`: the Nullstellensatz for
  `GL_n` over an algebraically closed field.
- `Matrix.GeneralLinearGroup.isHopfIdeal_of_isRadical`: over an algebraically closed field, a
  radical ideal whose `k`-points form a subgroup is a Hopf ideal; in particular the ideal of the
  identity component is a Hopf ideal.
- `Matrix.GeneralLinearGroup.zeroLocus_vanishingIdeal_eq_of_finite`: a finite subgroup of
  `GL n k` is Zariski closed.
- `Matrix.GeneralLinearGroup.setOf_forall_mem_vanishingIdeal_mul_singleton`: the Zariski closure of
  a right coset `Γ c` is the right coset of the Zariski closure of `Γ`.
- `Matrix.GeneralLinearGroup.zeroLocus_vanishingIdeal_le_normalizer`,
  `Matrix.GeneralLinearGroup.commutator_zeroLocus_vanishingIdeal_le`: Zariski closure preserves
  normalizing and commutator inclusions between subgroups of `GL n k`.
- `Matrix.GeneralLinearGroup.commute_of_mem_zeroLocus_vanishingIdeal`,
  `Matrix.GeneralLinearGroup.mulVec_mem_of_mem_zeroLocus_vanishingIdeal`,
  `Matrix.GeneralLinearGroup.map_mem_zeroLocus_vanishingIdeal`: centralizers, stabilizers of
  subspaces and polynomial homomorphisms pass to the Zariski closure.
- `Matrix.GeneralLinearGroup.exists_evalAlgHom_eq_det_of_mk_eq`,
  `Matrix.GeneralLinearGroup.evalAlgHom_mem_of_mem_zeroLocus_vanishingIdeal`: the determinant on a
  subquotient `S ⧸ U` of `k^n` is a polynomial function on the stabilizer of `U ≤ S`, and a
  polynomial function with finitely many values on a subgroup takes the same values on its
  Zariski closure.
- `Matrix.GeneralLinearGroup.IsConnected.isPrime`: in characteristic zero, a connected matrix
  group is irreducible, by Cartier's lemma; and
  `Matrix.GeneralLinearGroup.eq_of_le_of_ringKrullDim_eq`: a closed subgroup of an irreducible
  matrix group of the same dimension is the whole group.

## Implementation notes

The closure statements all rest on one fact: for sets `S, T ⊆ GL n k`, the product `S × T` is
schematically dense in the product `S̄ × T̄` of their Zariski closures, that is, an element of
`k[S̄] ⊗ k[T̄]` vanishing at all pairs of points of `S × T` is zero
(`Algebra.TensorProduct.eq_zero_of_forall_liftQuotient_eq_zero`). A word in a pair of points, such
as `g h g⁻¹` or `g h g⁻¹ h⁻¹`, is then evaluated on the universal pair of points
`(inlQuotient _ _ x, inrQuotient _ _ x)` of `S̄ × T̄`, and specialised to `R`-points along
`Algebra.TensorProduct.liftQuotient`.

The constructions on `(A ⧸ I) ⊗[k] (A ⧸ J)` are stated for an arbitrary `k`-algebra `A` and only
then specialised to the coordinate ring of `GL_n`: elaborating them directly at the localization
`CoordinateRing n k` makes instance unification time out.

## Blueprint

- `det-d-geometry`: matrix algebraic groups as reduced closed subgroups of `GL(V)`, their identity
  component and centre.
- `def-wf-algebraic-components`: the identity component `identityComponent`, with its `k`-points
  `identityComponentSubgroup`.
- `lemma-normality-geometric-monodromy--1`: the Zariski closure of a subgroup of `GL n k` is a
closed
  subgroup.
- `lemma-restriction-normal-subgroup`: the Zariski closure of a subgroup of `GL n k` is an algebraic
group, and
  closure preserves normalizing and commutator inclusions.
- `proposition-central-element-arithmetic-monodromy-group--2`: closed stabilizers and density.
- `lemma-determinant-weight-from-central-scalar--1`: the determinant character of a subquotient has
finite image on the closure of a
  subgroup on which it has finite image.
- `lemma-connected-components-images-homomorphisms`: the identity component is cut out by a Hopf
ideal.
- `lemma-connected-components-images-homomorphisms--3` (clause (1)),
`lemma-connected-components-images-homomorphisms--3`: connected
  matrix groups are irreducible; equal dimension forces equality.
-/

@[expose] public section

open WithConv
open scoped Matrix TensorProduct

namespace Matrix.GeneralLinearGroup

section CommRing

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
  {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation at `g` composed with the antipode is evaluation at `g⁻¹`. -/
theorem evalAlgHom_comp_antipodeAlgHom (g : GL n R) :
    (evalAlgHom g).comp (antipodeAlgHom n k) = evalAlgHom g⁻¹ := by
  have hg : map (evalAlgHom (k := k) g).toRingHom (genericUnit n k) = g :=
    (algHomMulEquiv n k R).apply_symm_apply g
  refine algHom_ext fun i j ↦ ?_
  rw [AlgHom.comp_apply, antipodeAlgHom_coord, evalAlgHom_coord]
  conv_rhs => rw [← hg, ← map_inv]
  rfl

/-- The identity matrix satisfies the equations of a Hopf ideal. -/
theorem evalAlgHom_eq_zero_of_mem_one (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {a : CoordinateRing n k} (ha : a ∈ I) : evalAlgHom (1 : GL n R) a = 0 := by
  have h := congr(($(evalAlgHom_one (n := n) (k := k) (R := R))).ofConv a)
  rw [ofConv_toConv] at h
  rw [h, AlgHom.convOne_apply, Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) ha,
    map_zero]

/-- The product of two matrices satisfying the equations of a Hopf ideal satisfies them. -/
theorem evalAlgHom_eq_zero_of_mem_mul (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g h : GL n R} (hg : ∀ a ∈ I, evalAlgHom g a = 0) (hh : ∀ a ∈ I, evalAlgHom h a = 0)
    {a : CoordinateRing n k} (ha : a ∈ I) : evalAlgHom (g * h) a = 0 := by
  have h := congr(($(evalAlgHom_mul (k := k) g h)).ofConv a)
  rw [ofConv_toConv] at h
  rw [h]
  exact Ideal.IsHopfIdeal.convMul_apply_eq_zero hg hh ha

/-- The inverse of a matrix satisfying the equations of a Hopf ideal satisfies them. -/
theorem evalAlgHom_eq_zero_of_mem_inv (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    {g : GL n R} (hg : ∀ a ∈ I, evalAlgHom g a = 0) {a : CoordinateRing n k} (ha : a ∈ I) :
    evalAlgHom g⁻¹ a = 0 := by
  rw [← evalAlgHom_comp_antipodeAlgHom, AlgHom.comp_apply]
  exact hg _ (Ideal.IsHopfIdeal.antipode_mem (R := k) ha)

/-- The `R`-points of the closed subgroup scheme `V(I)` of `GL_n` cut out by a Hopf ideal `I`: the
invertible matrices over `R` on which every equation in `I` vanishes.
(blueprint: `det-d-geometry`) -/
noncomputable def zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] (R : Type*)
    [CommRing R] [Algebra k R] : Subgroup (GL n R) where
  carrier := {g | ∀ a ∈ I, evalAlgHom g a = 0}
  one_mem' _ ha := evalAlgHom_eq_zero_of_mem_one I ha
  mul_mem' hg hh _ ha := evalAlgHom_eq_zero_of_mem_mul I hg hh ha
  inv_mem' hg _ ha := evalAlgHom_eq_zero_of_mem_inv I hg ha

@[simp]
theorem mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {g : GL n R} :
    g ∈ zeroLocus I R ↔ ∀ a ∈ I, evalAlgHom g a = 0 :=
  Iff.rfl

theorem zeroLocus_anti {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]
    (h : I ≤ J) : zeroLocus J R ≤ zeroLocus I R :=
  fun _ hg a ha ↦ hg a (h ha)

variable {S : Type*} [CommRing S] [Algebra k S]

/-- An algebra homomorphism `R → S` maps the `R`-points of `V(I)` to its `S`-points. -/
theorem map_mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    {g : GL n R} (hg : g ∈ zeroLocus I R) : map φ.toRingHom g ∈ zeroLocus I S := by
  intro a ha
  rw [evalAlgHom_map, AlgHom.comp_apply, hg a ha, map_zero]

/-- Along an injective algebra homomorphism `R → S`, a matrix over `R` is an `R`-point of `V(I)` if
and only if its image is an `S`-point. -/
theorem map_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {φ : R →ₐ[k] S}
    (hφ : Function.Injective φ) {g : GL n R} :
    map φ.toRingHom g ∈ zeroLocus I S ↔ g ∈ zeroLocus I R := by
  refine ⟨fun hg a ha ↦ hφ ?_, map_mem_zeroLocus φ⟩
  rw [map_zero, ← AlgHom.comp_apply, ← evalAlgHom_map]
  exact hg a ha

/-- The group homomorphism `V(I)(R) →* V(I)(S)` induced by an algebra homomorphism `R → S`. -/
noncomputable def zeroLocus.map (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    (φ : R →ₐ[k] S) : zeroLocus I R →* zeroLocus I S :=
  ((Matrix.GeneralLinearGroup.map φ.toRingHom).comp (zeroLocus I R).subtype).codRestrict _
    fun g ↦ map_mem_zeroLocus φ g.2

@[simp]
theorem zeroLocus.coe_map_apply {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    (g : zeroLocus I R) :
    (zeroLocus.map I φ g : GL n S) = Matrix.GeneralLinearGroup.map φ.toRingHom g :=
  rfl

/-- The ideal of equations vanishing on a set `S` of invertible matrices over `k`. For a subgroup
`S`, it cuts out the Zariski closure of `S`. (blueprint: `lemma-restriction-normal-subgroup`) -/
noncomputable def vanishingIdeal (S : Set (GL n k)) : Ideal (CoordinateRing n k) :=
  ⨅ g ∈ S, RingHom.ker (evalAlgHom (k := k) g)

theorem mem_vanishingIdeal {S : Set (GL n k)} {a : CoordinateRing n k} :
    a ∈ vanishingIdeal S ↔ ∀ g ∈ S, evalAlgHom g a = 0 := by
  simp [vanishingIdeal, Submodule.mem_iInf]

theorem vanishingIdeal_anti {S T : Set (GL n k)} (h : S ⊆ T) :
    vanishingIdeal T ≤ vanishingIdeal S :=
  fun _ ha ↦ mem_vanishingIdeal.2 fun g hg ↦ mem_vanishingIdeal.1 ha g (h hg)

theorem le_vanishingIdeal_zeroLocus (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    I ≤ vanishingIdeal (zeroLocus I k : Set (GL n k)) :=
  fun _ ha ↦ mem_vanishingIdeal.2 fun _ hg ↦ hg _ ha

/-- The equation `(g * h)_ij - (h * g)_ij = 0` in the entries of `g`, for a fixed matrix `h`. -/
noncomputable def commutatorEquation (h : GL n k) (i j : n) : CoordinateRing n k :=
  ∑ l, (coord n k i l * algebraMap k _ ((h : Matrix n n k) l j) -
    algebraMap k _ ((h : Matrix n n k) i l) * coord n k l j)

@[simp]
theorem evalAlgHom_commutatorEquation (g h : GL n k) (i j : n) :
    evalAlgHom g (commutatorEquation h i j) =
      ((g : Matrix n n k) * h) i j - ((h : Matrix n n k) * g) i j := by
  simp [commutatorEquation, Matrix.mul_apply, Finset.sum_sub_distrib]

section Pair

variable {A : Type*} [CommRing A] [Algebra k A] (I J : Ideal A)

/-- The image `x ⊗ 1` in `GL n ((A ⧸ I) ⊗[k] (A ⧸ J))` of an invertible matrix `x` over `A`. For
`x` the generic matrix this is the first point of the universal pair of points of `V(I) × V(J)`. -/
noncomputable def inlQuotient (x : GL n A) : GL n ((A ⧸ I) ⊗[k] (A ⧸ J)) :=
  map (Algebra.TensorProduct.includeLeftRingHom.comp (Ideal.Quotient.mk I)) x

/-- The image `1 ⊗ x` in `GL n ((A ⧸ I) ⊗[k] (A ⧸ J))` of an invertible matrix `x` over `A`. For
`x` the generic matrix this is the second point of the universal pair of points of
`V(I) × V(J)`. -/
noncomputable def inrQuotient (x : GL n A) : GL n ((A ⧸ I) ⊗[k] (A ⧸ J)) :=
  map ((Algebra.TensorProduct.includeRight (R := k) (A := A ⧸ I)).toRingHom.comp
    (Ideal.Quotient.mk J)) x

variable {I J}

theorem map_liftQuotient_inlQuotient (f g : A →ₐ[k] R) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ a ∈ J, g a = 0) (x : GL n A) :
    map (Algebra.TensorProduct.liftQuotient I J f g hf hg).toRingHom (inlQuotient I J x) =
      map f.toRingHom x := by
  ext i j
  simp [inlQuotient, Algebra.TensorProduct.liftQuotient]

theorem map_liftQuotient_inrQuotient (f g : A →ₐ[k] R) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ a ∈ J, g a = 0) (x : GL n A) :
    map (Algebra.TensorProduct.liftQuotient I J f g hf hg).toRingHom (inrQuotient I J x) =
      map g.toRingHom x := by
  ext i j
  simp [inrQuotient, Algebra.TensorProduct.liftQuotient]

end Pair

@[simp]
theorem map_evalAlgHom_genericUnit {R : Type*} [CommRing R] [Algebra k R] (x : GL n R) :
    map (evalAlgHom (k := k) x).toRingHom (genericUnit n k) = x :=
  (algHomMulEquiv n k R).apply_symm_apply x

@[simp]
theorem evalAlgHom_genericUnit : evalAlgHom (genericUnit n k) = AlgHom.id k _ :=
  algHom_ext fun i j ↦ by simp

theorem evalAlgHom_injective {R : Type*} [CommRing R] [Algebra k R] :
    Function.Injective fun g : GL n R ↦ evalAlgHom (k := k) g := fun x y h ↦ by
  rw [← map_evalAlgHom_genericUnit (k := k) x, ← map_evalAlgHom_genericUnit (k := k) y]
  exact congr(map (AlgHom.toRingHom $h) (genericUnit n k))

@[simp]
theorem evalAlgHom_map_genericUnit {R : Type*} [CommRing R] [Algebra k R]
    (φ : CoordinateRing n k →ₐ[k] R) : evalAlgHom (map φ.toRingHom (genericUnit n k)) = φ := by
  rw [evalAlgHom_map, evalAlgHom_genericUnit, AlgHom.comp_id]

/-- The algebra endomorphism of the coordinate ring of `GL_n` pulling functions back along the
two-sided translation `x ↦ g * x * h`. -/
noncomputable def translate (g h : GL n k) : CoordinateRing n k →ₐ[k] CoordinateRing n k :=
  evalAlgHom (map (algebraMap k (CoordinateRing n k)) g * genericUnit n k *
    map (algebraMap k (CoordinateRing n k)) h)

theorem evalAlgHom_comp_translate {R : Type*} [CommRing R] [Algebra k R] (g h : GL n k)
    (x : GL n R) : (evalAlgHom x).comp (translate g h) =
      evalAlgHom (map (algebraMap k R) g * x * map (algebraMap k R) h) := by
  have (g : GL n k) : map (evalAlgHom (k := k) x).toRingHom
      (map (algebraMap k (CoordinateRing n k)) g) = map (algebraMap k R) g := by
    ext
    simp
  rw [translate, ← evalAlgHom_map, map_mul, map_mul, map_evalAlgHom_genericUnit, this, this]

theorem translate_comp_translate (g h g' h' : GL n k) :
    (translate g h).comp (translate g' h') = translate (g' * g) (h * h') := by
  rw [translate, evalAlgHom_comp_translate, translate, map_mul, map_mul]
  simp only [mul_assoc]

@[simp]
theorem translate_one_one : translate (1 : GL n k) 1 = AlgHom.id k _ := by
  simp [translate]

/-- The algebra automorphism of the coordinate ring of `GL_n` pulling functions back along the
two-sided translation `x ↦ g * x * h`. -/
noncomputable def translateAlgEquiv (g h : GL n k) :
    CoordinateRing n k ≃ₐ[k] CoordinateRing n k :=
  AlgEquiv.ofAlgHom (translate g h) (translate g⁻¹ h⁻¹)
    (by rw [translate_comp_translate, inv_mul_cancel, mul_inv_cancel, translate_one_one])
    (by rw [translate_comp_translate, mul_inv_cancel, inv_mul_cancel, translate_one_one])

/-- Conjugation `x ↦ g * x * g⁻¹` is an endomorphism of the group scheme `GL_n`: the translation
`translate g g⁻¹` of its coordinate ring is a bialgebra homomorphism. Both conditions are
identities between evaluations at matrices, by `evalAlgHom_comp_translate`: the counit is
evaluation at `1 = g * 1 * g⁻¹`, and the comultiplication is evaluation at the product `x y` of
the two copies of the generic matrix, whose conjugate is `(g x g⁻¹) (g y g⁻¹)`. -/
noncomputable def conjBialgHom (g : GL n k) : CoordinateRing n k →ₐc[k] CoordinateRing n k :=
  .ofAlgHom (translate g g⁻¹)
    (by
      have hc : Bialgebra.counitAlgHom k (CoordinateRing n k) = evalAlgHom (1 : GL n k) :=
        algHom_ext fun i j ↦ by simp
      have hk (h : GL n k) : map (algebraMap k k) h = h := by
        ext
        simp
      rw [hc, evalAlgHom_comp_translate, hk, hk, mul_one, mul_inv_cancel])
    (by
      have hc : Bialgebra.comulAlgHom k (CoordinateRing n k) = comulAlgHom n k :=
        algHom_ext fun i j ↦ by simp
      set A := CoordinateRing n k
      set x : GL n (A ⊗[k] A) :=
        map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toRingHom (genericUnit n k)
      set y : GL n (A ⊗[k] A) :=
        map Algebra.TensorProduct.includeRight.toRingHom (genericUnit n k)
      have hcomul : comulAlgHom n k = evalAlgHom (x * y) := rfl
      have hmap (φ : A →ₐ[k] A ⊗[k] A) (h : GL n k) :
          map φ.toRingHom (map (algebraMap k A) h) = map (algebraMap k (A ⊗[k] A)) h := by
        ext
        simp
      have ht : map (translate g g⁻¹).toRingHom (genericUnit n k) =
          map (algebraMap k A) g * genericUnit n k * map (algebraMap k A) g⁻¹ :=
        (algHomMulEquiv n k A).apply_symm_apply _
      set F := Algebra.TensorProduct.map (translate g g⁻¹) (translate g g⁻¹)
      have hconj (ι : A →ₐ[k] A ⊗[k] A) (hι : F.comp ι = ι.comp (translate g g⁻¹)) :
          map F.toRingHom (map ι.toRingHom (genericUnit n k)) =
            map (algebraMap k (A ⊗[k] A)) g * map ι.toRingHom (genericUnit n k) *
              map (algebraMap k (A ⊗[k] A)) g⁻¹ := by
        calc map F.toRingHom (map ι.toRingHom (genericUnit n k))
            = map ι.toRingHom (map (translate g g⁻¹).toRingHom (genericUnit n k)) := by
              ext i j
              exact congr($hι (genericUnit n k i j))
          _ = _ := by rw [ht, map_mul, map_mul, hmap, hmap]
      have hx := hconj _ (Algebra.TensorProduct.map_comp_includeLeft _ _)
      have hy := hconj _ (Algebra.TensorProduct.map_comp_includeRight _ _)
      rw [hc, hcomul, evalAlgHom_comp_translate, ← evalAlgHom_map, map_mul, hx, hy]
      congr 1
      simp only [map_inv, mul_assoc, inv_mul_cancel_left]
      rfl)

@[simp]
theorem coe_conjBialgHom (g : GL n k) : (conjBialgHom g : CoordinateRing n k →ₐ[k] _) =
    translate g g⁻¹ :=
  rfl

theorem antipodeAlgHom_comp_antipodeAlgHom :
    (antipodeAlgHom n k).comp (antipodeAlgHom n k) = AlgHom.id k _ := by
  have := evalAlgHom_comp_antipodeAlgHom (k := k) (genericUnit n k)⁻¹
  rwa [inv_inv, evalAlgHom_genericUnit] at this

/-- Two-sided translations by points of `V(I)` preserve the ideal `I`. -/
theorem translate_mem {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {g h : GL n k}
    (hg : g ∈ zeroLocus I k) (hh : h ∈ zeroLocus I k) {a : CoordinateRing n k} (ha : a ∈ I) :
    translate g h a ∈ I := by
  set q := Ideal.Quotient.mkₐ k I
  have hγ : map q.toRingHom (genericUnit n k) ∈ zeroLocus I (CoordinateRing n k ⧸ I) := by
    intro b hb
    rw [evalAlgHom_map, evalAlgHom_genericUnit, AlgHom.comp_id, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  have key := congr($(evalAlgHom_comp_translate g h (map q.toRingHom (genericUnit n k))) a)
  rw [AlgHom.comp_apply, evalAlgHom_map, evalAlgHom_genericUnit, AlgHom.comp_id] at key
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k, key]
  exact (zeroLocus I _).mul_mem ((zeroLocus I _).mul_mem
    (map_mem_zeroLocus (Algebra.ofId k _) hg) hγ) (map_mem_zeroLocus (Algebra.ofId k _) hh) a ha

/-- Every `k`-point of `V(J)` is evaluation at a matrix. -/
theorem exists_eq_liftₐ_evalAlgHom {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k]
    (χ : CoordinateRing n k ⧸ J →ₐ[k] k) :
    ∃ g, ∃ hg : g ∈ zeroLocus J k, χ = Ideal.Quotient.liftₐ J (evalAlgHom g) hg := by
  obtain ⟨g, hgdef⟩ : ∃ g, g = algHomMulEquiv n k k
      (WithConv.toConv (χ.comp (Ideal.Quotient.mkₐ k J))) := ⟨_, rfl⟩
  have hev : evalAlgHom g = χ.comp (Ideal.Quotient.mkₐ k J) := by
    rw [hgdef, algHomMulEquiv_apply, WithConv.ofConv_toConv, evalAlgHom_map_genericUnit]
  have hg : g ∈ zeroLocus J k := fun a ha ↦ by
    rw [hev, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 ha,
      map_zero]
  exact ⟨g, hg, Ideal.Quotient.algHom_ext k (by rw [Ideal.Quotient.liftₐ_comp, hev])⟩

end CommRing

section Field

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

theorem isRadical_vanishingIdeal (S : Set (GL n k)) : (vanishingIdeal S).IsRadical := by
  rintro a ⟨m, hm⟩
  refine mem_vanishingIdeal.2 fun g hg ↦ IsNilpotent.eq_zero ⟨m, ?_⟩
  rw [← map_pow]
  exact mem_vanishingIdeal.1 hm g hg

theorem mem_vanishingIdeal_iff_forall_subtype {S : Set (GL n k)} (a : CoordinateRing n k) :
    a ∈ vanishingIdeal S ↔ ∀ g : S, evalAlgHom (g : GL n k) a = 0 :=
  mem_vanishingIdeal.trans ⟨fun h g ↦ h g g.2, fun h g hg ↦ h ⟨g, hg⟩⟩

private theorem map_evalAlgHom_toRingHom_genericUnit {R : Type*} [CommRing R] [Algebra k R]
    (g : GL n R) : map (evalAlgHom (k := k) g).toRingHom (genericUnit n k) = g :=
  (algHomMulEquiv n k R).apply_symm_apply g

/-- Passage to the closure for a pair of points: let `I` and `J` be the ideals of equations
vanishing on two families of `k`-points `χ s` and `χ' t` of `Spec A`. If a matrix `x` over
`(A ⧸ I) ⊗[k] (A ⧸ J)` specializes at every pair `(χ s, χ' t)` to a matrix satisfying the equation
`a`, then so does its specialization at every pair of `R`-points of `Spec (A ⧸ I)` and
`Spec (A ⧸ J)`. This is the schematic density of the product of the two families
(`Algebra.TensorProduct.eq_zero_of_forall_liftQuotient_eq_zero`). -/
theorem evalAlgHom_map_liftQuotient_eq_zero {A : Type*} [CommRing A] [Algebra k A]
    {I J : Ideal A} {S T : Type*} (χ : S → A →ₐ[k] k) (χ' : T → A →ₐ[k] k)
    (hI : ∀ a, a ∈ I ↔ ∀ s, χ s a = 0) (hJ : ∀ a, a ∈ J ↔ ∀ t, χ' t a = 0)
    (x : GL n ((A ⧸ I) ⊗[k] (A ⧸ J))) (a : CoordinateRing n k)
    (hx : ∀ s t, evalAlgHom (map (Algebra.TensorProduct.liftQuotient I J (χ s) (χ' t)
      (fun b hb ↦ (hI b).1 hb s) (fun b hb ↦ (hJ b).1 hb t)).toRingHom x) a = 0)
    {R : Type*} [CommRing R] [Algebra k R] (f g : A →ₐ[k] R) (hf : ∀ b ∈ I, f b = 0)
    (hg : ∀ b ∈ J, g b = 0) :
    evalAlgHom (map (Algebra.TensorProduct.liftQuotient I J f g hf hg).toRingHom x) a = 0 := by
  have hc : evalAlgHom x a = 0 := by
    refine Algebra.TensorProduct.eq_zero_of_forall_liftQuotient_eq_zero χ χ' hI hJ
      fun s t ↦ ?_
    have := hx s t
    rwa [evalAlgHom_map, AlgHom.comp_apply] at this
  rw [evalAlgHom_map, AlgHom.comp_apply, hc, map_zero]

/-- The Zariski closure of a subgroup of `GL n k` is a closed subgroup scheme: the ideal of
equations vanishing on the subgroup is a Hopf ideal.

For the comultiplication, the image of `Δ(a)` in `k[Γ̄] ⊗ k[Γ̄]` vanishes at every pair of points
`(γ, δ)` of `Γ × Γ`, where it takes the value `a(γδ) = 0`; by schematic density it is zero.
(blueprint: `lemma-normality-geometric-monodromy--1`, `lemma-restriction-normal-subgroup`) -/
instance instIsHopfIdealVanishingIdeal (Γ : Subgroup (GL n k)) :
    (vanishingIdeal (Γ : Set (GL n k))).IsHopfIdeal k where
  counit_eq_zero a ha := mem_vanishingIdeal.1 ha 1 Γ.one_mem
  map_mkQ_comul_eq_zero a ha := by
    refine (Algebra.TensorProduct.map_mkQ_restrictScalars_eq_zero_iff _ _ _).2
      (Algebra.TensorProduct.eq_zero_of_forall_liftQuotient_eq_zero
        (fun γ : Γ ↦ evalAlgHom (γ : GL n k)) (fun γ : Γ ↦ evalAlgHom (γ : GL n k))
        mem_vanishingIdeal_iff_forall_subtype mem_vanishingIdeal_iff_forall_subtype
        fun γ δ ↦ ?_)
    rw [Algebra.TensorProduct.liftQuotient_map_mkₐ, ← ofConv_toConv (evalAlgHom (γ : GL n k)),
      ← ofConv_toConv (evalAlgHom (δ : GL n k)), ← AlgHom.convMul_apply, ← evalAlgHom_mul,
      ofConv_toConv]
    exact mem_vanishingIdeal.1 ha _ (Γ.mul_mem γ.2 δ.2)
  antipode_mem a ha := mem_vanishingIdeal.2 fun g hg ↦
    (DFunLike.congr_fun (evalAlgHom_comp_antipodeAlgHom g) a).trans
      (mem_vanishingIdeal.1 ha _ (Γ.inv_mem hg))

theorem subset_zeroLocus_vanishingIdeal (Γ : Subgroup (GL n k)) :
    Γ ≤ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k :=
  fun g hg _ ha ↦ mem_vanishingIdeal.1 ha g hg

/-- The `k`-points of the Zariski closure of a subgroup `Γ` lie in `Γ` as soon as `Γ` is cut out by
some set `J` of equations. -/
theorem zeroLocus_vanishingIdeal_le {Γ : Subgroup (GL n k)} (J : Set (CoordinateRing n k))
    (hΓ : ∀ g ∈ Γ, ∀ a ∈ J, evalAlgHom g a = 0)
    (hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) → g ∈ Γ) :
    zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k ≤ Γ :=
  fun g hg ↦ hJ g fun a ha ↦ hg a (mem_vanishingIdeal.2 fun h hh ↦ hΓ h hh a ha)

/-- A matrix outside a finite subgroup `Γ` of `GL n k` is separated from `Γ` by an equation: the
product, over `γ ∈ Γ`, of `x_ij - γ_ij` for an entry `(i, j)` at which `g` and `γ` differ. -/
theorem exists_mem_vanishingIdeal_evalAlgHom_ne_zero {Γ : Subgroup (GL n k)} [Finite Γ]
    {g : GL n k} (hg : g ∉ Γ) :
    ∃ a ∈ vanishingIdeal (Γ : Set (GL n k)), evalAlgHom g a ≠ 0 := by
  have : Fintype Γ := Fintype.ofFinite Γ
  have hne (γ : Γ) :
      ∃ p : n × n, (g : Matrix n n k) p.1 p.2 ≠ ((γ : GL n k) : Matrix n n k) p.1 p.2 := by
    by_contra! h
    exact hg (Units.ext (Matrix.ext fun i j ↦ h (i, j)) ▸ γ.2)
  choose p hp using hne
  refine ⟨∏ γ : Γ, (coord n k (p γ).1 (p γ).2 -
    algebraMap k _ (((γ : GL n k) : Matrix n n k) (p γ).1 (p γ).2)),
    mem_vanishingIdeal.2 fun δ hδ ↦ ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨δ, hδ⟩) (by simp)
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun γ _ ↦ by simpa [sub_eq_zero] using hp γ

/-- A finite subgroup of `GL n k` is Zariski closed: the `k`-points of its Zariski closure are
the subgroup itself. -/
theorem zeroLocus_vanishingIdeal_eq_of_finite (Γ : Subgroup (GL n k)) [Finite Γ] :
    zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k = Γ := by
  refine le_antisymm (zeroLocus_vanishingIdeal_le (vanishingIdeal (Γ : Set (GL n k)))
    (fun g hg a ha ↦ mem_vanishingIdeal.1 ha g hg) fun g hg ↦ ?_)
    (subset_zeroLocus_vanishingIdeal Γ)
  by_contra hgΓ
  obtain ⟨a, ha, hga⟩ := exists_mem_vanishingIdeal_evalAlgHom_ne_zero hgΓ
  exact hga (hg a ha)

/-- If a subgroup `Γ` of `GL n k` normalizes a subgroup `Δ`, then the Zariski closure of `Γ`
normalizes the Zariski closure of `Δ`, on `R`-points for every `k`-algebra `R`.

The conjugate `x y x⁻¹` of the universal pair of points `(x, y)` of `Γ̄ × Δ̄` satisfies the
equations of `Δ̄`, because its specializations `γ δ γ⁻¹` at the points of `Γ × Δ` lie in `Δ` and
`Γ × Δ` is schematically dense in `Γ̄ × Δ̄` (`evalAlgHom_map_liftQuotient_eq_zero`); specializing
along `Algebra.TensorProduct.liftQuotient` gives the statement on `R`-points.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem zeroLocus_vanishingIdeal_le_normalizer {Γ Δ : Subgroup (GL n k)}
    (hΓ : Γ ≤ Subgroup.normalizer (Δ : Set (GL n k)))
    (R : Type*) [CommRing R] [Algebra k R] :
    zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R ≤
      Subgroup.normalizer (zeroLocus (vanishingIdeal (Δ : Set (GL n k))) R : Set (GL n R)) := by
  have key {g h : GL n R} (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R)
      (hh : h ∈ zeroLocus (vanishingIdeal (Δ : Set (GL n k))) R) :
      g * h * g⁻¹ ∈ zeroLocus (vanishingIdeal (Δ : Set (GL n k))) R := by
    intro a ha
    have := evalAlgHom_map_liftQuotient_eq_zero (fun γ : Γ ↦ evalAlgHom (γ : GL n k))
      (fun δ : Δ ↦ evalAlgHom (δ : GL n k)) mem_vanishingIdeal_iff_forall_subtype
      mem_vanishingIdeal_iff_forall_subtype
      (inlQuotient _ _ (genericUnit n k) * inrQuotient _ _ (genericUnit n k) *
        (inlQuotient _ _ (genericUnit n k))⁻¹) a (fun γ δ ↦ by
          rw [map_mul, map_mul, map_inv, map_liftQuotient_inlQuotient,
            map_liftQuotient_inrQuotient, map_evalAlgHom_toRingHom_genericUnit,
            map_evalAlgHom_toRingHom_genericUnit]
          exact mem_vanishingIdeal.1 ha _ ((hΓ γ.2 δ).1 δ.2))
      (evalAlgHom g) (evalAlgHom h) (fun b hb ↦ hg b hb) (fun b hb ↦ hh b hb)
    rwa [map_mul, map_mul, map_inv, map_liftQuotient_inlQuotient, map_liftQuotient_inrQuotient,
      map_evalAlgHom_toRingHom_genericUnit, map_evalAlgHom_toRingHom_genericUnit] at this
  intro g hg h
  refine ⟨key hg, fun hghg ↦ ?_⟩
  simpa [mul_assoc] using key (inv_mem hg) hghg

open scoped commutatorElement in
/-- If the commutators of a subgroup `Γ` of `GL n k` lie in a subgroup `Δ`, then the commutators of
the Zariski closure of `Γ` lie in the Zariski closure of `Δ`, on `R`-points for every `k`-algebra
`R`.

As in `zeroLocus_vanishingIdeal_le_normalizer`, by the schematic density of `Γ × Γ` in
`Γ̄ × Γ̄`, applied to the commutator `⁅x, y⁆` of the universal pair of points `(x, y)`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem commutator_zeroLocus_vanishingIdeal_le {Γ Δ : Subgroup (GL n k)} (hΓ : ⁅Γ, Γ⁆ ≤ Δ)
    (R : Type*) [CommRing R] [Algebra k R] :
    ⁅zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R,
        zeroLocus (vanishingIdeal (Γ : Set (GL n k))) R⁆ ≤
      zeroLocus (vanishingIdeal (Δ : Set (GL n k))) R := by
  rw [Subgroup.commutator_le]
  intro g hg h hh a ha
  have := evalAlgHom_map_liftQuotient_eq_zero (fun γ : Γ ↦ evalAlgHom (γ : GL n k))
    (fun γ : Γ ↦ evalAlgHom (γ : GL n k)) mem_vanishingIdeal_iff_forall_subtype
    mem_vanishingIdeal_iff_forall_subtype
    ⁅inlQuotient _ _ (genericUnit n k), inrQuotient _ _ (genericUnit n k)⁆ a (fun γ δ ↦ by
      rw [map_commutatorElement, map_liftQuotient_inlQuotient, map_liftQuotient_inrQuotient,
        map_evalAlgHom_toRingHom_genericUnit, map_evalAlgHom_toRingHom_genericUnit]
      exact mem_vanishingIdeal.1 ha _ (hΓ (Subgroup.commutator_mem_commutator γ.2 δ.2)))
    (evalAlgHom g) (evalAlgHom h) (fun b hb ↦ hg b hb) (fun b hb ↦ hh b hb)
  rwa [map_commutatorElement, map_liftQuotient_inlQuotient, map_liftQuotient_inrQuotient,
    map_evalAlgHom_toRingHom_genericUnit, map_evalAlgHom_toRingHom_genericUnit] at this

/-- The linear equation `φ(g u) = 0` in the entries of `g`, for a vector `u` and a linear form
`φ` on `n → k`. -/
noncomputable def linearFormEquation (φ : Module.Dual k (n → k)) (u : n → k) :
    CoordinateRing n k :=
  ∑ i, ∑ j, algebraMap k _ (φ (fun l ↦ if i = l then 1 else 0) * u j) * coord n k i j

@[simp]
theorem evalAlgHom_linearFormEquation (φ : Module.Dual k (n → k)) (u : n → k) (g : GL n k) :
    evalAlgHom g (linearFormEquation φ u) = φ ((g : Matrix n n k) *ᵥ u) := by
  rw [LinearMap.pi_apply_eq_sum_univ φ]
  simp only [linearFormEquation, map_sum, map_mul, AlgHom.commutes, evalAlgHom_coord,
    Matrix.mulVec, dotProduct, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- **Closed stabilizers and density.** A subspace `S ⊆ k^n` stable under a subgroup `Γ` of
`GL n k` is stable under its Zariski closure: the stabilizer of `S` is cut out by the linear
equations `φ(g x) = 0`, for `x ∈ S` and `φ` in the annihilator of `S`.
(blueprint: `proposition-central-element-arithmetic-monodromy-group--2`,
`lemma-restriction-normal-subgroup`) -/
theorem mulVec_mem_of_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)}
    {S : Submodule k (n → k)} (hΓ : ∀ g ∈ Γ, ∀ x ∈ S, (g : Matrix n n k) *ᵥ x ∈ S) {g : GL n k}
    (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k) {x : n → k} (hx : x ∈ S) :
    (g : Matrix n n k) *ᵥ x ∈ S := by
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).1 fun φ hφ ↦ ?_
  rw [← evalAlgHom_linearFormEquation]
  refine hg _ (mem_vanishingIdeal.2 fun γ hγ ↦ ?_)
  rw [evalAlgHom_linearFormEquation]
  exact (Submodule.mem_dualAnnihilator φ).1 hφ _ (hΓ γ hγ x hx)

/-- A subspace `U ⊆ k^n` is stable under a subgroup `Γ` of `GL n k` if and only if it is stable
under its Zariski closure. (blueprint:
`proposition-central-element-arithmetic-monodromy-group--2`) -/
theorem forall_mulVec_mem_iff_forall_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)}
    {U : Submodule k (n → k)} :
    (∀ g ∈ Γ, ∀ u ∈ U, (g : Matrix n n k) *ᵥ u ∈ U) ↔
      ∀ g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k, ∀ u ∈ U,
        (g : Matrix n n k) *ᵥ u ∈ U :=
  ⟨fun hU _ hg _ hu ↦ mulVec_mem_of_mem_zeroLocus_vanishingIdeal hU hg hu,
    fun hU g hg ↦ hU g (subset_zeroLocus_vanishingIdeal Γ hg)⟩

/-- The determinant of the endomorphism induced on a subquotient `S ⧸ U` of `k^n` by a matrix
`g` stabilizing `U ≤ S` is a polynomial function of the entries of `g`: there is one `p` in the
coordinate ring of `GL_n` with `p(g) = det f` for every `g` and every endomorphism `f` of `S ⧸ U`
induced by `g`.  In a basis `(mk sⱼ)` of `S ⧸ U`, with coordinate forms extended to linear forms
`νᵢ` on `k^n`, the matrix of `f` is `(νᵢ(g sⱼ))ᵢⱼ`, whose entries are linear in `g`.
(blueprint: `lemma-determinant-weight-from-central-scalar--1`) -/
theorem exists_evalAlgHom_eq_det_of_mk_eq (S U : Submodule k (n → k)) :
    ∃ p : CoordinateRing n k, ∀ (g : GL n k) (f : Module.End k (S ⧸ U.comap S.subtype)),
      (∀ x : S, ∃ y : S, (y : n → k) = (g : Matrix n n k) *ᵥ x ∧
        f (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) →
      evalAlgHom g p = LinearMap.det f := by
  classical
  let b := Module.finBasis k (S ⧸ U.comap S.subtype)
  choose s hs using fun j ↦ Submodule.Quotient.mk_surjective _ (b j)
  choose ν hν using fun i ↦ LinearMap.exists_extend ((b.coord i).comp (U.comap S.subtype).mkQ)
  refine ⟨(Matrix.of fun i j ↦ linearFormEquation (ν i) (s j : n → k)).det, fun g f hf ↦ ?_⟩
  rw [← LinearMap.det_toMatrix b, AlgHom.map_det]
  congr 1
  ext i j
  obtain ⟨y, hy, hfy⟩ := hf (s j)
  have := congr($(hν i) y)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
    Module.Basis.coord_apply] at this
  simp [LinearMap.toMatrix_apply, ← hs, hfy, ← this, hy]

/-- A polynomial function `p` on `GL_n` whose values on a subgroup `Γ` lie in a finite set `A`
has its values in `A` on the whole Zariski closure of `Γ`: the product `∏_{a ∈ A} (p - a)`
vanishes on `Γ`. (blueprint: `lemma-determinant-weight-from-central-scalar--1`) -/
theorem evalAlgHom_mem_of_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)}
    (p : CoordinateRing n k) {A : Set k} (hA : A.Finite) (hΓ : ∀ γ ∈ Γ, evalAlgHom γ p ∈ A)
    {g : GL n k} (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k) :
    evalAlgHom g p ∈ A := by
  classical
  have h := hg (∏ a ∈ hA.toFinset, (p - algebraMap k _ a)) (mem_vanishingIdeal.2 fun γ hγ ↦ by
    simpa [Finset.prod_eq_zero_iff, sub_eq_zero] using hΓ γ hγ)
  simpa [Finset.prod_eq_zero_iff, sub_eq_zero] using h

/-- Over an algebraically closed field, every maximal ideal of the coordinate ring of `GL_n` is the
ideal of a point. -/
theorem exists_ker_evalAlgHom_eq [IsAlgClosed k] (m : Ideal (CoordinateRing n k)) [m.IsMaximal] :
    ∃ g : GL n k, RingHom.ker (evalAlgHom g) = m := by
  let : Field (CoordinateRing n k ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (CoordinateRing n k ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let φ : CoordinateRing n k →ₐ[k] k :=
    (IsAlgClosed.lift : (CoordinateRing n k ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)
  refine ⟨algHomMulEquiv n k k (toConv φ), ?_⟩
  have hφ : evalAlgHom (algHomMulEquiv n k k (toConv φ)) = φ :=
    congrArg ofConv ((algHomMulEquiv n k k).symm_apply_apply (toConv φ))
  rw [hφ]
  ext a
  simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The Nullstellensatz for `GL_n`: over an algebraically closed field, an element vanishing at
every point where the equations `J` vanish lies in the radical of `J`. -/
theorem vanishingIdeal_setOf_le_radical [IsAlgClosed k] (J : Ideal (CoordinateRing n k)) :
    vanishingIdeal {g : GL n k | ∀ a ∈ J, evalAlgHom g a = 0} ≤ J.radical := by
  have : IsJacobsonRing (CoordinateRing n k) := isJacobsonRing_of_finiteType (A := k)
  intro a ha
  rw [J.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hJm, hm⟩
  obtain ⟨g, rfl⟩ := exists_ker_evalAlgHom_eq m
  exact mem_vanishingIdeal.1 ha g fun b hb ↦ hJm hb

/-- The Nullstellensatz for closed subgroup schemes of `GL_n`: the ideal of the `k`-points of
`V(I)` is the radical of `I`. (blueprint: `det-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_eq_radical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : vanishingIdeal (zeroLocus I k : Set (GL n k)) = I.radical :=
  le_antisymm (vanishingIdeal_setOf_le_radical I)
    ((isRadical_vanishingIdeal _).radical_le_iff.2 (le_vanishingIdeal_zeroLocus I))

/-- Over an algebraically closed field, a radical Hopf ideal is the ideal of its `k`-points.
(blueprint: `det-d-geometry`) -/
theorem vanishingIdeal_zeroLocus_le_of_isRadical [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] (hI : I.IsRadical) : vanishingIdeal (zeroLocus I k : Set (GL n k)) ≤ I :=
  ((vanishingIdeal_zeroLocus_eq_radical I).trans hI.radical).le

/-- The point of `Spec k[x_ij, det⁻¹]` given by an invertible matrix `g`: the kernel of evaluation
at `g`. -/
noncomputable def toPrimeSpectrum (g : GL n k) : PrimeSpectrum (CoordinateRing n k) :=
  ⟨RingHom.ker (evalAlgHom (k := k) g), RingHom.ker_isPrime _⟩

theorem toPrimeSpectrum_mem_zeroLocus_iff {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
    {g : GL n k} :
    toPrimeSpectrum g ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) ↔
      g ∈ zeroLocus I k :=
  Iff.rfl

theorem toPrimeSpectrum_injective :
    Function.Injective (toPrimeSpectrum : GL n k → PrimeSpectrum (CoordinateRing n k)) := by
  intro g h hgh
  ext i j
  have hmem : coord n k i j - algebraMap k _ ((g : Matrix n n k) i j) ∈
      (toPrimeSpectrum g).asIdeal := by
    simp [toPrimeSpectrum]
  rw [hgh] at hmem
  exact (sub_eq_zero.1 (by simpa [toPrimeSpectrum] using hmem)).symm

/-- The ideal of the reduced identity component `G°` of the closed subscheme `V(I)` of `GL_n`: the
functions vanishing on the connected component of `V(I)` containing the identity matrix. The set
`π₀(G)` of connected components is Mathlib's `ConnectedComponents` of the underlying space.
(blueprint: `det-d-geometry`, `def-wf-algebraic-components`) -/
noncomputable def identityComponent (I : Ideal (CoordinateRing n k)) :
    Ideal (CoordinateRing n k) :=
  PrimeSpectrum.vanishingIdeal
    (connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
      (toPrimeSpectrum 1))

theorem le_identityComponent (I : Ideal (CoordinateRing n k)) : I ≤ identityComponent I :=
  (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal _ I).1 (connectedComponentIn_subset _ _)

theorem isRadical_identityComponent (I : Ideal (CoordinateRing n k)) :
    (identityComponent I).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- The reduced identity component is monotone in the group: if `V(J) ⊆ V(I)` then
`V(J)° ⊆ V(I)°`. -/
theorem identityComponent_mono (I : Ideal (CoordinateRing n k)) {J : Ideal (CoordinateRing n k)}
    (h : I ≤ J) : identityComponent I ≤ identityComponent J :=
  PrimeSpectrum.vanishingIdeal_anti_mono
    (connectedComponentIn_mono _ (PrimeSpectrum.zeroLocus_anti_mono h))

/-- The closed subgroup `V(I)` of `GL_n` is connected (and reduced): `I` is the ideal of its own
reduced identity component. -/
def IsConnected (I : Ideal (CoordinateRing n k)) : Prop :=
  identityComponent I = I

theorem IsConnected.isRadical {I : Ideal (CoordinateRing n k)} (h : IsConnected I) :
    I.IsRadical :=
  h ▸ isRadical_identityComponent I

section Translation

@[simp]
theorem evalAlgHom_translate_apply (g h x : GL n k) (a : CoordinateRing n k) :
    evalAlgHom x (translate g h a) = evalAlgHom (g * x * h) a := by
  have := congr($(evalAlgHom_comp_translate (R := k) g h x) a)
  rw [AlgHom.comp_apply] at this
  rw [this]
  congr 3

open scoped Pointwise in
/-- The Zariski closure of a right translate `S c` of a set of matrices is the right translate of
the Zariski closure of `S`: a matrix `g` satisfies the equations vanishing on `S c` if and only if
`g c⁻¹` satisfies the equations vanishing on `S`, because pulling back along the right translation
by `c` (`translate 1 c`) is an automorphism of the coordinate ring. -/
theorem forall_mem_vanishingIdeal_mul_singleton_iff {S : Set (GL n k)} {c g : GL n k} :
    (∀ a ∈ vanishingIdeal (S * {c}), evalAlgHom g a = 0) ↔
      ∀ a ∈ vanishingIdeal S, evalAlgHom (g * c⁻¹) a = 0 := by
  have hmem {c : GL n k} {a : CoordinateRing n k} (ha : a ∈ vanishingIdeal (S * {c})) :
      translate 1 c a ∈ vanishingIdeal S :=
    mem_vanishingIdeal.2 fun s hs ↦ by
      rw [evalAlgHom_translate_apply, one_mul]
      exact mem_vanishingIdeal.1 ha _ (Set.mul_mem_mul hs rfl)
  refine ⟨fun h a ha ↦ ?_, fun h a ha ↦ ?_⟩
  · have hb : translate 1 c⁻¹ a ∈ vanishingIdeal (S * {c}) := by
      refine mem_vanishingIdeal.2 fun _ hs ↦ ?_
      obtain ⟨s, hs, _, rfl, rfl⟩ := hs
      rw [evalAlgHom_translate_apply, one_mul, mul_inv_cancel_right]
      exact mem_vanishingIdeal.1 ha s hs
    simpa using h _ hb
  · simpa using h _ (hmem ha)

open scoped Pointwise in
/-- The Zariski closure of a right coset `Γ c` of a subgroup of `GL n k` is the right coset of
the Zariski closure of `Γ`. -/
theorem setOf_forall_mem_vanishingIdeal_mul_singleton (Γ : Subgroup (GL n k)) (c : GL n k) :
    {g : GL n k | ∀ a ∈ vanishingIdeal ((Γ : Set (GL n k)) * {c}), evalAlgHom g a = 0} =
      (zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k : Set (GL n k)) * {c} := by
  ext g
  rw [Set.mem_ofPred_eq, forall_mem_vanishingIdeal_mul_singleton_iff, Set.mul_singleton]
  exact ⟨fun h ↦ ⟨g * c⁻¹, h, inv_mul_cancel_right g c⟩, by
    rintro ⟨h, hh, rfl⟩
    simpa using hh⟩

theorem comap_translate_toPrimeSpectrum (g h x : GL n k) :
    PrimeSpectrum.comap (translate g h) (toPrimeSpectrum x) = toPrimeSpectrum (g * x * h) := by
  ext a
  simp [toPrimeSpectrum, RingHom.mem_ker]

/-- The homeomorphism of the spectrum of the coordinate ring of `GL_n` induced by the two-sided
translation `x ↦ g * x * h`. -/
noncomputable def translateHomeomorph (g h : GL n k) :
    PrimeSpectrum (CoordinateRing n k) ≃ₜ PrimeSpectrum (CoordinateRing n k) :=
  PrimeSpectrum.homeomorphOfRingEquiv (translateAlgEquiv g h).symm.toRingEquiv

@[simp]
theorem translateHomeomorph_apply (g h : GL n k) (p : PrimeSpectrum (CoordinateRing n k)) :
    translateHomeomorph g h p = PrimeSpectrum.comap (translate g h) p :=
  rfl

@[simp]
theorem translateHomeomorph_symm_apply (g h : GL n k) (p : PrimeSpectrum (CoordinateRing n k)) :
    (translateHomeomorph g h).symm p = PrimeSpectrum.comap (translate g⁻¹ h⁻¹) p :=
  rfl

theorem translateHomeomorph_toPrimeSpectrum (g h x : GL n k) :
    translateHomeomorph g h (toPrimeSpectrum x) = toPrimeSpectrum (g * x * h) :=
  comap_translate_toPrimeSpectrum g h x

theorem translateHomeomorph_translateHomeomorph (a b c d : GL n k)
    (p : PrimeSpectrum (CoordinateRing n k)) :
    translateHomeomorph a b (translateHomeomorph c d p) =
      translateHomeomorph (a * c) (d * b) p := by
  simp only [translateHomeomorph_apply]
  rw [← PrimeSpectrum.comap_comp_apply, ← AlgHom.comp_toRingHom, translate_comp_translate]

@[simp]
theorem translateHomeomorph_one_one_apply (p : PrimeSpectrum (CoordinateRing n k)) :
    translateHomeomorph (1 : GL n k) 1 p = p := by
  rw [translateHomeomorph_apply, translate_one_one]
  rfl

/-- Over an algebraically closed field, every closed point of `Spec k[GL_n]` is a matrix. -/
theorem exists_toPrimeSpectrum_eq_of_mem_closedPoints [IsAlgClosed k]
    {q : PrimeSpectrum (CoordinateRing n k)} (hq : q ∈ closedPoints _) :
    ∃ z : GL n k, toPrimeSpectrum z = q := by
  have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 hq
  obtain ⟨z, hz⟩ := exists_ker_evalAlgHom_eq q.asIdeal
  exact ⟨z, PrimeSpectrum.ext hz⟩

/-- The homeomorphism of the spectrum of the coordinate ring of `GL_n` induced by the inversion
`x ↦ x⁻¹`, the spectrum of the antipode. -/
noncomputable def invHomeomorph :
    PrimeSpectrum (CoordinateRing n k) ≃ₜ PrimeSpectrum (CoordinateRing n k) :=
  PrimeSpectrum.homeomorphOfRingEquiv (AlgEquiv.ofAlgHom (antipodeAlgHom n k) (antipodeAlgHom n k)
    antipodeAlgHom_comp_antipodeAlgHom antipodeAlgHom_comp_antipodeAlgHom).symm.toRingEquiv

@[simp]
theorem invHomeomorph_apply (p : PrimeSpectrum (CoordinateRing n k)) :
    invHomeomorph p = PrimeSpectrum.comap (antipodeAlgHom n k) p :=
  rfl

theorem invHomeomorph_toPrimeSpectrum (x : GL n k) :
    invHomeomorph (toPrimeSpectrum x) = toPrimeSpectrum x⁻¹ := by
  ext a
  simp [toPrimeSpectrum, RingHom.mem_ker, ← AlgHom.comp_apply, evalAlgHom_comp_antipodeAlgHom]

theorem invHomeomorph_invHomeomorph (p : PrimeSpectrum (CoordinateRing n k)) :
    invHomeomorph (invHomeomorph p) = p := by
  simp only [invHomeomorph_apply]
  rw [← PrimeSpectrum.comap_comp_apply, ← AlgHom.comp_toRingHom,
    antipodeAlgHom_comp_antipodeAlgHom]
  rfl

variable {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]

theorem comap_translate_mem_zeroLocus {g h : GL n k} (hg : g ∈ zeroLocus I k)
    (hh : h ∈ zeroLocus I k) {p : PrimeSpectrum (CoordinateRing n k)}
    (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) :
    PrimeSpectrum.comap (translate g h) p ∈
      PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) :=
  fun _ ha ↦ hp (translate_mem hg hh ha)

theorem translateHomeomorph_mem_zeroLocus_iff {g h : GL n k} (hg : g ∈ zeroLocus I k)
    (hh : h ∈ zeroLocus I k) {p : PrimeSpectrum (CoordinateRing n k)} :
    translateHomeomorph g h p ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) ↔
      p ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) := by
  refine ⟨fun hp ↦ ?_, comap_translate_mem_zeroLocus hg hh⟩
  rw [← (translateHomeomorph g h).symm_apply_apply p]
  exact comap_translate_mem_zeroLocus ((zeroLocus I k).inv_mem hg) ((zeroLocus I k).inv_mem hh) hp

/-- Two-sided translation by points of `V(I)` maps `V(I)` onto itself. -/
theorem translateHomeomorph_image_zeroLocus {g h : GL n k} (hg : g ∈ zeroLocus I k)
    (hh : h ∈ zeroLocus I k) :
    translateHomeomorph g h '' PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) =
      PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) := by
  refine (Set.image_subset_iff.2 fun p hp ↦
    show translateHomeomorph g h p ∈ _ from comap_translate_mem_zeroLocus hg hh hp).antisymm
    fun p hp ↦ ⟨(translateHomeomorph g h).symm p, ?_, (translateHomeomorph g h).apply_symm_apply p⟩
  exact comap_translate_mem_zeroLocus ((zeroLocus I k).inv_mem hg) ((zeroLocus I k).inv_mem hh) hp

/-- Two-sided translation by points of `V(I)` permutes the connected components of `V(I)`. -/
theorem translateHomeomorph_image_connectedComponentIn {g h : GL n k} (hg : g ∈ zeroLocus I k)
    (hh : h ∈ zeroLocus I k) {p : PrimeSpectrum (CoordinateRing n k)}
    (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) :
    translateHomeomorph g h ''
        connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) p =
      connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
        (translateHomeomorph g h p) := by
  rw [(translateHomeomorph g h).image_connectedComponentIn hp,
    translateHomeomorph_image_zeroLocus hg hh]

omit [I.IsHopfIdeal k] in
/-- Over an algebraically closed field, a radical ideal `J` of the coordinate ring of `GL_n` whose
`k`-points form a subgroup `H` of `GL n k` is a Hopf ideal: `V(J)` is a closed subgroup scheme.
Each Hopf ideal condition is an equation between functions on a reduced variety (`V(J)` or
`V(J) × V(J)`), which may be tested on `k`-points. -/
theorem isHopfIdeal_of_isRadical [IsAlgClosed k] {J : Ideal (CoordinateRing n k)}
    (hJ : J.IsRadical) (H : Subgroup (GL n k)) (hH : ∀ g, g ∈ H ↔ ∀ a ∈ J, evalAlgHom g a = 0) :
    J.IsHopfIdeal k where
  counit_eq_zero a ha := (hH 1).1 H.one_mem a ha
  map_mkQ_comul_eq_zero a ha := by
    set q := Ideal.Quotient.mkₐ k J
    have : IsReduced (CoordinateRing n k ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
    let e := Submodule.Quotient.restrictScalarsEquiv k J
    have he : (TensorProduct.congr e e).toLinearMap ∘ₗ
        TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ =
          (Algebra.TensorProduct.map q q).toLinearMap := by
      ext
      rfl
    refine (TensorProduct.congr e e).injective ?_
    rw [map_zero, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply, he]
    refine Algebra.TensorProduct.eq_zero_of_forall_lift_algHom_eq_zero k _ _ fun φ ψ ↦ ?_
    have hpt (φ : CoordinateRing n k ⧸ J →ₐ[k] k) :
        algHomMulEquiv n k k (toConv (φ.comp q)) ∈ H := by
      refine (hH _).2 fun b hb ↦ ?_
      rw [algHomMulEquiv_apply, ofConv_toConv, evalAlgHom_map, evalAlgHom_genericUnit,
        AlgHom.comp_id, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
    have key : Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ .all _ _)
        (Algebra.TensorProduct.map q q (Coalgebra.comul a)) =
          ofConv (toConv (φ.comp q) * toConv (ψ.comp q)) a := by
      rw [AlgHom.convMul_apply]
      simp only [← AlgHom.comp_apply]
      congr 1
      ext <;> simp
    rw [AlgHom.toLinearMap_apply, key,
      ← (algHomMulEquiv n k k).symm_apply_apply (toConv (φ.comp q)),
      ← (algHomMulEquiv n k k).symm_apply_apply (toConv (ψ.comp q)), algHomMulEquiv_symm_apply,
      algHomMulEquiv_symm_apply, ← evalAlgHom_mul, ofConv_toConv]
    exact (hH _).1 (H.mul_mem (hpt φ) (hpt ψ)) a ha
  antipode_mem a ha := by
    refine hJ.radical.le (vanishingIdeal_setOf_le_radical J (mem_vanishingIdeal.2 fun g hg ↦ ?_))
    change evalAlgHom g (antipodeAlgHom n k a) = 0
    rw [← AlgHom.comp_apply, evalAlgHom_comp_antipodeAlgHom]
    exact (hH _).1 (H.inv_mem ((hH g).2 hg)) a ha

section IdentityComponent

variable (I) in
/-- The `k`-points of the identity component `G°` of `G = V(I)`, as a subgroup of `GL n k`: the
matrices whose point lies in the connected component of `V(I)` containing the identity.
(blueprint: `def-wf-algebraic-components`) -/
noncomputable def identityComponentSubgroup : Subgroup (GL n k) where
  carrier := {g | toPrimeSpectrum g ∈ connectedComponentIn
    (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum 1)}
  one_mem' := mem_connectedComponentIn (toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem)
  mul_mem' {g h} hg hh := by
    have h1 := translateHomeomorph_image_connectedComponentIn
      (toPrimeSpectrum_mem_zeroLocus_iff.1 (connectedComponentIn_subset _ _ hg))
      (zeroLocus I k).one_mem (toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem)
    rw [translateHomeomorph_toPrimeSpectrum, mul_one, mul_one, ← connectedComponentIn_eq hg]
      at h1
    rw [Set.mem_ofPred_eq, ← h1]
    exact ⟨_, hh, by rw [translateHomeomorph_toPrimeSpectrum, mul_one]⟩
  inv_mem' {g} hg := by
    have hg' : g ∈ zeroLocus I k :=
      toPrimeSpectrum_mem_zeroLocus_iff.1 (connectedComponentIn_subset _ _ hg)
    have h1 := translateHomeomorph_image_connectedComponentIn ((zeroLocus I k).inv_mem hg')
      (zeroLocus I k).one_mem (toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem)
    rw [translateHomeomorph_toPrimeSpectrum, mul_one, mul_one] at h1
    have h2 : toPrimeSpectrum 1 ∈ connectedComponentIn
        (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum g⁻¹) := by
      rw [← h1]
      exact ⟨_, hg, by rw [translateHomeomorph_toPrimeSpectrum, mul_one, inv_mul_cancel]⟩
    rw [Set.mem_ofPred_eq, ← connectedComponentIn_eq h2]
    exact mem_connectedComponentIn
      (toPrimeSpectrum_mem_zeroLocus_iff.2 ((zeroLocus I k).inv_mem hg'))

theorem mem_identityComponentSubgroup_iff {g : GL n k} :
    g ∈ identityComponentSubgroup I ↔ ∀ a ∈ identityComponent I, evalAlgHom g a = 0 := by
  have hC := (PrimeSpectrum.isClosed_zeroLocus
    (I : Set (CoordinateRing n k))).isClosed_connectedComponentIn (toPrimeSpectrum 1)
  change toPrimeSpectrum g ∈ connectedComponentIn
    (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum 1) ↔ _
  rw [← hC.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  rfl

/-- The identity component of an algebraic group over an algebraically closed field is a closed
subgroup scheme: its ideal is radical, and its `k`-points form the subgroup
`identityComponentSubgroup I`. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
instance [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    (identityComponent I).IsHopfIdeal k :=
  isHopfIdeal_of_isRadical (isRadical_identityComponent I) (identityComponentSubgroup I)
    fun _ ↦ mem_identityComponentSubgroup_iff

theorem zeroLocus_identityComponent [IsAlgClosed k] :
    zeroLocus (identityComponent I) k = identityComponentSubgroup I :=
  SetLike.ext fun _ ↦ mem_identityComponentSubgroup_iff.symm

end IdentityComponent

end Translation


theorem one_mem_zeroLocus_identityComponent [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : (1 : GL n k) ∈ zeroLocus (identityComponent I) k := by
  intro a ha
  have h1 : toPrimeSpectrum (1 : GL n k) ∈ PrimeSpectrum.zeroLocus (I : Set _) :=
    toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha _ (mem_connectedComponentIn h1)

/-- The matrices of `G(k)` commuting with all of `G(k)`, for `G = V(I)`: the `k`-points of the
centre `Z(G)` when `k` is algebraically closed, and in general the subgroup `Z(G)(k) ⊆ G(k)` of
`k`-points of the centre that are central in `G(k)`. (blueprint: `det-d-geometry`) -/
noncomputable def centerPoints (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Subgroup (GL n k) :=
  zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k))

theorem mem_centerPoints_iff (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] {g : GL n k} :
    g ∈ centerPoints I ↔ g ∈ zeroLocus I k ∧ ∀ h ∈ zeroLocus I k, g * h = h * g :=
  ⟨fun ⟨hg, hc⟩ ↦ ⟨hg, fun h hh ↦ (Subgroup.mem_centralizer_iff.1 hc h hh).symm⟩,
    fun ⟨hg, hc⟩ ↦ ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh ↦ (hc h hh).symm⟩⟩

/-- The ideal of the reduced centre `Z(G)` of the closed subgroup scheme `G = V(I)` of `GL_n`, for
`k` algebraically closed: the Zariski closure of the matrices of `G(k)` commuting with all of
`G(k)`. Over an algebraically closed field the `k`-points are dense in the reduced centre, so this
is its ideal; over a general field the closure of `centerPoints I` can be strictly smaller (for
`k = 𝔽_q` and `G = GL_n` it is finite), which is why `k` is assumed algebraically closed.
(blueprint: `det-d-geometry`) -/
noncomputable def center [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Ideal (CoordinateRing n k) :=
  vanishingIdeal (centerPoints I : Set (GL n k))

instance [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    (center I).IsHopfIdeal k :=
  instIsHopfIdealVanishingIdeal _

/-- The ideal of `G` is contained in the ideal of its centre: `Z(G) ⊆ G`. -/
theorem le_center [IsAlgClosed k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    I ≤ center I :=
  (le_vanishingIdeal_zeroLocus I).trans (vanishingIdeal_anti fun _ hg ↦ hg.1)

/-- The `k`-points of the centre of `G = V(I)` are the matrices of `G(k)` commuting with all of
`G(k)`. (blueprint: `det-d-geometry`) -/
theorem mem_zeroLocus_center_iff [IsAlgClosed k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] {g : GL n k} :
    g ∈ zeroLocus (center I) k ↔ g ∈ zeroLocus I k ∧ ∀ h ∈ zeroLocus I k, g * h = h * g := by
  let J : Set (CoordinateRing n k) :=
    I ∪ {c | ∃ h ∈ zeroLocus I k, ∃ i j, c = commutatorEquation h i j}
  have hΓ : ∀ g ∈ (zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
      Subgroup (GL n k)), ∀ a ∈ J, evalAlgHom g a = 0 := by
    rintro g ⟨hg, hc⟩ a (ha | ⟨h, hh, i, j, rfl⟩)
    · exact hg a ha
    · rw [evalAlgHom_commutatorEquation, ← Units.val_mul, ← Units.val_mul,
        Subgroup.mem_centralizer_iff.1 hc h hh, sub_self]
  have hJ : ∀ g : GL n k, (∀ a ∈ J, evalAlgHom g a = 0) →
      g ∈ (zeroLocus I k ⊓ Subgroup.centralizer (zeroLocus I k : Set (GL n k)) :
        Subgroup (GL n k)) := by
    refine fun g hg ↦ ⟨fun a ha ↦ hg a (Or.inl ha),
      Subgroup.mem_centralizer_iff.2 fun h hh ↦ ?_⟩
    ext i j
    have := hg _ (Or.inr ⟨h, hh, i, j, rfl⟩)
    rw [evalAlgHom_commutatorEquation, sub_eq_zero] at this
    simpa using this.symm
  constructor
  · intro hg
    obtain ⟨hg, hc⟩ := zeroLocus_vanishingIdeal_le J hΓ hJ hg
    exact ⟨hg, fun h hh ↦ (Subgroup.mem_centralizer_iff.1 hc h hh).symm⟩
  · rintro ⟨hg, hc⟩
    exact subset_zeroLocus_vanishingIdeal _
      ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh ↦ (hc h hh).symm⟩

/-- An element commuting with a subgroup `Γ` of `GL n k` commutes with the `k`-points of its
Zariski closure: the commutator equations are closed. (blueprint:
`lemma-restriction-normal-subgroup`) -/
theorem commute_of_mem_zeroLocus_vanishingIdeal {Γ : Subgroup (GL n k)} {z : GL n k}
    (hz : ∀ g ∈ Γ, z * g = g * z) {g : GL n k}
    (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k) : z * g = g * z := by
  ext i j
  have h := hg (commutatorEquation z i j) <| mem_vanishingIdeal.2 fun h hh ↦ by
    rw [evalAlgHom_commutatorEquation, ← Units.val_mul, ← Units.val_mul, hz h hh, sub_self]
  rw [evalAlgHom_commutatorEquation, sub_eq_zero] at h
  exact h.symm

open scoped commutatorElement in
/-- Over an algebraically closed field, the points of the reduced centre `Z(G)` of a reduced
`G = V(I)` commute with the points of `G`, with values in any `k`-algebra `R`: the commutator of
the universal pair of points of `Z(G) × G` is trivial at every pair of `k`-points, hence trivial by
the schematic density of the `k`-points (`evalAlgHom_map_liftQuotient_eq_zero`).
(blueprint: `lemma-stable-subspaces-center`) -/
theorem commute_of_mem_zeroLocus_center [IsAlgClosed k] {I : Ideal (CoordinateRing n k)}
    [I.IsHopfIdeal k] (hI : I.IsRadical) {R : Type*} [CommRing R] [Algebra k R] {g h : GL n R}
    (hg : g ∈ zeroLocus (center I) R) (hh : h ∈ zeroLocus I R) : Commute g h := by
  have hJ (a : CoordinateRing n k) : a ∈ I ↔ ∀ t : zeroLocus I k, evalAlgHom (t : GL n k) a = 0 :=
    ⟨fun ha t ↦ t.2 a ha, fun ht ↦ vanishingIdeal_zeroLocus_le_of_isRadical I hI
      (mem_vanishingIdeal.2 fun t htI ↦ ht ⟨t, htI⟩)⟩
  have key (i j : n) : evalAlgHom ⁅g, h⁆ (coord n k i j - algebraMap k _ ((1 : Matrix n n k) i j)) =
      0 := by
    have := evalAlgHom_map_liftQuotient_eq_zero (fun s : centerPoints I ↦ evalAlgHom (s : GL n k))
      (fun t : zeroLocus I k ↦ evalAlgHom (t : GL n k)) mem_vanishingIdeal_iff_forall_subtype hJ
      ⁅inlQuotient _ _ (genericUnit n k), inrQuotient _ _ (genericUnit n k)⁆
      (coord n k i j - algebraMap k _ ((1 : Matrix n n k) i j)) (fun s t ↦ by
        rw [map_commutatorElement, map_liftQuotient_inlQuotient, map_liftQuotient_inrQuotient,
          map_evalAlgHom_genericUnit, map_evalAlgHom_genericUnit,
          commutatorElement_eq_one_iff_mul_comm.2 (((mem_centerPoints_iff I).1 s.2).2 t t.2)]
        simp)
      (evalAlgHom g) (evalAlgHom h) (fun b hb ↦ hg b hb) (fun b hb ↦ hh b hb)
    rwa [map_commutatorElement, map_liftQuotient_inlQuotient, map_liftQuotient_inrQuotient,
      map_evalAlgHom_genericUnit, map_evalAlgHom_genericUnit] at this
  have h1 : ⁅g, h⁆ = 1 := by
    ext i j
    have := key i j
    rw [map_sub, evalAlgHom_coord, AlgHom.commutes, sub_eq_zero] at this
    rw [this, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

section Map

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A homomorphism `r : GL n k →* GL m k` given by polynomials (an algebra map `φ` of coordinate
rings with `evalAlgHom (r g) = evalAlgHom g ∘ φ`) maps the `k`-points of the Zariski closure of a
subgroup `Γ` into the Zariski closure of any subgroup `Γ'` containing `r(Γ)`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem map_mem_zeroLocus_vanishingIdeal (r : GL n k →* GL m k)
    (φ : CoordinateRing m k →ₐ[k] CoordinateRing n k)
    (hφ : ∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (r g)) {Γ : Subgroup (GL n k)}
    {Γ' : Subgroup (GL m k)} (hΓ : ∀ h ∈ Γ, r h ∈ Γ') {g : GL n k}
    (hg : g ∈ zeroLocus (vanishingIdeal (Γ : Set (GL n k))) k) :
    r g ∈ zeroLocus (vanishingIdeal (Γ' : Set (GL m k))) k := by
  intro a ha
  rw [← hφ, AlgHom.comp_apply]
  refine hg _ (mem_vanishingIdeal.2 fun h hh ↦ ?_)
  rw [← AlgHom.comp_apply, hφ]
  exact mem_vanishingIdeal.1 ha _ (hΓ h hh)

end Map

/-! ### Cartier's lemma: connected matrix groups are irreducible

By Cartier's lemma (`HopfAlgebra.isPrime_iInf_pow_ker`), in characteristic zero the functions on
`V(I)` vanishing near a `k`-point `c` form a prime ideal, contained in every prime of `V(I)` through
`c`: a single irreducible component passes through each point. -/

section Cartier

/-- The ideal of the functions on `GL_n` whose restriction to `V(I)` vanishes near the point `c`
of `V(I)`. -/
private noncomputable abbrev localVanishing (I : Ideal (CoordinateRing n k))
    (c : CoordinateRing n k ⧸ I →ₐ[k] k) : Ideal (CoordinateRing n k) :=
  (⨅ r : ℕ, RingHom.ker c ^ r).comap (Ideal.Quotient.mk I)

private theorem localVanishing_le [CharZero k] (I : Ideal (CoordinateRing n k))
    (c : CoordinateRing n k ⧸ I →ₐ[k] k) {q : Ideal (CoordinateRing n k)} [q.IsPrime] (hIq : I ≤ q)
    (hq : q ≤ RingHom.ker (c.comp (Ideal.Quotient.mkₐ k I))) : localVanishing I c ≤ q := by
  intro a ha
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  obtain ⟨t, ht, hta⟩ := AlgHom.mem_iInf_pow_ker_iff.1 (Ideal.mem_comap.1 ha)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hta
  refine ((‹q.IsPrime›.mem_or_mem (hIq hta)).resolve_left fun htq ↦ ?_)
  have := hq htq
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ht] at this
  exact one_ne_zero this

private theorem le_localVanishing (I : Ideal (CoordinateRing n k))
    (c : CoordinateRing n k ⧸ I →ₐ[k] k) : I ≤ localVanishing I c := fun a ha ↦ by
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  exact zero_mem _

private theorem localVanishing_le_ker (I : Ideal (CoordinateRing n k))
    (c : CoordinateRing n k ⧸ I →ₐ[k] k) :
    localVanishing I c ≤ RingHom.ker (c.comp (Ideal.Quotient.mkₐ k I)) := fun a ha ↦ by
  have := (Submodule.mem_iInf _).1 (Ideal.mem_comap.1 ha) 1
  rw [pow_one] at this
  exact this

private theorem localVanishing_mem_minimalPrimes [CharZero k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] (c : CoordinateRing n k ⧸ I →ₐ[k] k) :
    localVanishing I c ∈ I.minimalPrimes := by
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  have : (localVanishing I c).IsPrime :=
    Ideal.IsPrime.comap _ (hK := HopfAlgebra.isPrime_iInf_pow_ker c)
  refine ⟨⟨this, le_localVanishing I c⟩, fun q ⟨hq, hIq⟩ hqP ↦ ?_⟩
  exact localVanishing_le I c hIq (hqP.trans (localVanishing_le_ker I c))

/-- **A connected matrix group is irreducible**: in characteristic zero, over an algebraically
closed field, the ideal of a connected closed subgroup `V(I)` of `GL_n` is prime.

By Cartier's lemma the functions vanishing near a point `c` of `V(I)` form a prime ideal, contained
in every prime of `V(I)` through `c`: a single irreducible component passes through each point,
so the irreducible components of `V(I)` are pairwise disjoint, and the connected `V(I)` has only
one. (blueprint: `lemma-connected-components-images-homomorphisms--3`, clause (1)) -/
theorem IsConnected.isPrime [IsAlgClosed k] [CharZero k] {I : Ideal (CoordinateRing n k)}
    [I.IsHopfIdeal k] (hconn : IsConnected I) : I.IsPrime := by
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  set e := Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)
  set P := localVanishing I e
  have hPmin := localVanishing_mem_minimalPrimes I e
  have hP : P.IsPrime := hPmin.1.1
  -- a minimal prime meeting `V(P)` is `P`
  have key (Q : Ideal (CoordinateRing n k)) (hQ : Q ∈ I.minimalPrimes)
      (x : PrimeSpectrum (CoordinateRing n k)) (hQx : Q ≤ x.asIdeal) (hPx : P ≤ x.asIdeal) :
      Q = P := by
    obtain ⟨M, hM, hxM⟩ := x.asIdeal.exists_le_maximal x.2.ne_top
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq_of_isMaximal k (CoordinateRing n k) M
    have hIM : I ≤ RingHom.ker φ := hφ ▸ hQ.1.2.trans (hQx.trans hxM)
    let c : CoordinateRing n k ⧸ I →ₐ[k] k := Ideal.Quotient.liftₐ I φ fun a ha ↦ hIM ha
    have hc : RingHom.ker (c.comp (Ideal.Quotient.mkₐ k I)) = M := by
      rw [← hφ]
      congr 1
    have : Q.IsPrime := hQ.1.1
    have h1 : localVanishing I c ≤ Q :=
      localVanishing_le I c hQ.1.2 (hc ▸ hQx.trans hxM)
    have h2 : localVanishing I c ≤ P := localVanishing_le I c hPmin.1.2 (hc ▸ hPx.trans hxM)
    have hc' := localVanishing_mem_minimalPrimes I c
    exact (le_antisymm (hQ.2 hc'.1 h1) h1).trans (le_antisymm (hPmin.2 hc'.1 h2) h2).symm
  have h1 : toPrimeSpectrum (1 : GL n k) ∈ PrimeSpectrum.zeroLocus (P : Set (CoordinateRing n k)) :=
    fun b hb ↦ by
      have hb' := localVanishing_le_ker I e hb
      rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Bialgebra.counitAlgHom_apply, Bialgebra.Quotient.counit_mk] at hb'
      exact hb'
  have h1I : toPrimeSpectrum (1 : GL n k) ∈
      PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) :=
    PrimeSpectrum.zeroLocus_anti_mono (le_localVanishing I e) h1
  set W := ⋃ Q ∈ {Q | Q ∈ I.minimalPrimes ∧ Q ≠ P},
    PrimeSpectrum.zeroLocus (Q : Set (CoordinateRing n k))
  have hW : IsClosed W :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun Q hQ ↦ hQ.1).isClosed_biUnion
      fun Q _ ↦ PrimeSpectrum.isClosed_zeroLocus _
  set C := connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
    (toPrimeSpectrum 1)
  have hcover : C ⊆ PrimeSpectrum.zeroLocus (P : Set (CoordinateRing n k)) ∪ W := fun x hx ↦ by
    have hxI := (PrimeSpectrum.mem_zeroLocus _ _).1 (connectedComponentIn_subset _ _ hx)
    obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le (J := x.asIdeal) hxI
    by_cases hQP : Q = P
    · subst hQP
      exact Or.inl hQx
    · exact Or.inr (Set.mem_biUnion (x := Q) ⟨hQ, hQP⟩ hQx)
  have hdisj : C ∩ (PrimeSpectrum.zeroLocus (P : Set (CoordinateRing n k)) ∩ W) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x ⟨_, hPx, hWx⟩ ↦ ?_
    obtain ⟨Q, ⟨hQ, hQP⟩, hQx⟩ := Set.mem_iUnion₂.1 hWx
    exact hQP (key Q hQ x hQx hPx)
  have hC1 : toPrimeSpectrum 1 ∈ C := mem_connectedComponentIn h1I
  have hCP : C ⊆ PrimeSpectrum.zeroLocus (P : Set (CoordinateRing n k)) :=
    ((isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn) _ _
      (PrimeSpectrum.isClosed_zeroLocus _) hW hcover hdisj).resolve_right fun hCW ↦
        (Set.eq_empty_iff_forall_notMem.1 hdisj) _ ⟨hC1, h1, hCW hC1⟩
  have hPI : P ≤ I := fun a ha ↦ by
    rw [← hconn]
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun x hx ↦ hCP hx ha
  rw [le_antisymm (le_localVanishing I e) hPI]
  exact hP

/-- **A closed subgroup of full dimension is everything**: if `V(I)` is irreducible and
`V(J) ⊆ V(I)` has the same dimension, then `J = I`. (blueprint:
`lemma-connected-components-images-homomorphisms--3`)
-/
theorem eq_of_le_of_ringKrullDim_eq (I : Ideal (CoordinateRing n k)) [I.IsPrime]
    {J : Ideal (CoordinateRing n k)} (hIJ : I ≤ J)
    (h : ringKrullDim (CoordinateRing n k ⧸ J) = ringKrullDim (CoordinateRing n k ⧸ I)) :
    J = I :=
  Ideal.eq_of_le_of_ringKrullDim_quotient_eq hIJ (ringKrullDim_ne_top_of_finiteType k _) h

end Cartier

end Field

end Matrix.GeneralLinearGroup
