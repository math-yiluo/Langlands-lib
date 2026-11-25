/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # KoszulCoefficientExtensionChi

Source: Stacks Project, Tag 0BQZ, coefficient formulas in the finite free
Koszul calculation (blueprint: new-lem-sc-koszul-coefficient-extension-chi).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

private noncomputable def coefficientFunctional
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ)
    (x : ⋀[A]^n (Fin r →₀ A) →ₗ[A] A) : ⋀[S]^n (Fin r →₀ S) →ₗ[S] S :=
  ((Finsupp.basisSingleOne : Module.Basis (Fin r) S (Fin r →₀ S)).exteriorPower n).constr S
    (fun s ↦ algebraMap A S
      (x (((Finsupp.basisSingleOne : Module.Basis (Fin r) A
        (Fin r →₀ A)).exteriorPower n) s)))

private theorem coefficientFunctional_basis
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ)
    (x : ⋀[A]^n (Fin r →₀ A) →ₗ[A] A) (s : Set.powersetCard (Fin r) n) :
    coefficientFunctional A S r n x
      (((Finsupp.basisSingleOne : Module.Basis (Fin r) S
        (Fin r →₀ S)).exteriorPower n) s) =
      algebraMap A S (x (((Finsupp.basisSingleOne : Module.Basis (Fin r) A
        (Fin r →₀ A)).exteriorPower n) s)) := by
  exact Module.Basis.constr_basis _ _ _ _

private theorem coefficientFunctional_eval
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ)
    (x : ⋀[A]^n (Fin r →₀ A) →ₗ[A] A) (v : Fin n → (Fin r →₀ A)) :
    coefficientFunctional A S r n x (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
      algebraMap A S (x (exteriorPower.ιMulti A n v)) := by
  classical
  let bA := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A))
  let bS := (Finsupp.basisSingleOne : Module.Basis (Fin r) S (Fin r →₀ S))
  let w := fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _)
  have hcoord (s : Set.powersetCard (Fin r) n) :
      (bS.exteriorPower n).repr (exteriorPower.ιMulti S n w) s =
      algebraMap A S ((bA.exteriorPower n).repr (exteriorPower.ιMulti A n v) s) := by
    simp only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    rw [RingHom.map_det]
    rfl
  have hb (s : Set.powersetCard (Fin r) n) :
      coefficientFunctional A S r n x (bS.exteriorPower n s) =
        algebraMap A S (x (bA.exteriorPower n s)) :=
    coefficientFunctional_basis A S r n x s
  calc
    _ = Finset.univ.sum (fun s ↦ algebraMap A S
        ((bA.exteriorPower n).repr (exteriorPower.ιMulti A n v) s) *
        algebraMap A S (x (bA.exteriorPower n s))) := by
      conv_lhs => rw [← (bS.exteriorPower n).sum_repr (exteriorPower.ιMulti S n w)]
      simp only [map_sum, map_smul, hcoord, hb, smul_eq_mul]
    _ = algebraMap A S (x (Finset.univ.sum (fun s ↦
        (bA.exteriorPower n).repr (exteriorPower.ιMulti A n v) s •
          bA.exteriorPower n s))) := by
      simp only [map_sum, map_smul, smul_eq_mul, map_mul]
    _ = _ := by rw [Module.Basis.sum_repr]

private noncomputable def coefficientDegreeMap
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ)
    (f : Fin r → A) :
    (koszulDualComplex A r f).X n ⟶
      (ModuleCat.restrictScalars (algebraMap A S)).obj
        ((koszulDualComplex S r (algebraMap A S ∘ f)).X n) :=
  ModuleCat.ofHom (X := (koszulDualComplex A r f).X n)
    (Y := (ModuleCat.restrictScalars (algebraMap A S)).obj
      ((koszulDualComplex S r (algebraMap A S ∘ f)).X n))
    { toFun := fun x ↦ ModuleCat.ofHom (coefficientFunctional A S r n x.hom)
      map_add' := by
        intro x y
        apply ModuleCat.hom_ext
        apply ((Finsupp.basisSingleOne : Module.Basis (Fin r) S
          (Fin r →₀ S)).exteriorPower n).ext
        intro s
        change coefficientFunctional A S r n (x.hom + y.hom) _ =
          coefficientFunctional A S r n x.hom _ + coefficientFunctional A S r n y.hom _
        simp only [coefficientFunctional_basis, LinearMap.add_apply, map_add]
      map_smul' := by
        intro a x
        apply ModuleCat.hom_ext
        apply ((Finsupp.basisSingleOne : Module.Basis (Fin r) S
          (Fin r →₀ S)).exteriorPower n).ext
        intro s
        change coefficientFunctional A S r n (a • x.hom) _ =
          algebraMap A S a * coefficientFunctional A S r n x.hom _
        simp only [coefficientFunctional_basis, LinearMap.smul_apply, smul_eq_mul, map_mul] }

private theorem koszulBoundary_wedge
    (R : Type u) [CommRing R] (r n : ℕ) (f : Fin r → R)
    (v : Fin (n + 1) → (Fin r →₀ R)) :
    koszulBoundary R r f n (exteriorPower.ιMulti R (n + 1) v) =
      Finset.univ.sum (fun i : Fin (n + 1) ↦ (((-1 : R) ^ (i.val + 2)) *
        Finsupp.linearCombination R f (v i)) •
        exteriorPower.ιMulti R n (v ∘ i.succAbove)) := by
  obtain ⟨D, h1, hrec, huniq, hgen, hzero, hdeg, hform, hleib, hderivuniq⟩ :=
    koszul_differential R (Fin r →₀ R) (Finsupp.linearCombination R f)
  have hD : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm R (Fin r →₀ R)))
      (Finsupp.linearCombination R f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro z y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R (Fin r →₀ R)))
          (Finsupp.linearCombination R f) z y
  apply Subtype.ext
  simpa only [koszulBoundary, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.coe_subtype, exteriorPower.ιMulti_apply_coe, Submodule.coe_sum,
    Submodule.coe_smul, Algebra.smul_def, hD] using hform n v

private theorem koszulDualBoundary_wedge
    (R : Type u) [CommRing R] (r n : ℕ) (f : Fin r → R)
    (x : (koszulComplex R r f).X n ⟶ ModuleCat.of R R)
    (v : Fin (n + 1) → (Fin r →₀ R)) :
    (koszulDualBoundary R r n f x).hom (exteriorPower.ιMulti R (n + 1) v) =
      (-1 : R) ^ (n + 1) * Finset.univ.sum (fun i : Fin (n + 1) ↦
        (((-1 : R) ^ (i.val + 2)) * Finsupp.linearCombination R f (v i)) *
          x.hom (exteriorPower.ιMulti R n (v ∘ i.succAbove))) := by
  change ModuleCat.of R (⋀[R]^n (Fin r →₀ R)) ⟶ ModuleCat.of R R at x
  change (-1 : R) ^ (n + 1) * x.hom
    (((koszulComplex R r f).d (n + 1) n).hom
      (exteriorPower.ιMulti R (n + 1) v)) = _
  simp only [koszulComplex, ChainComplex.of_d, ModuleCat.hom_ofHom,
    koszulBoundary_wedge, map_sum, map_smul, smul_eq_mul]

private theorem linearCombination_mapRange
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : Fin r → A) (v : Fin r →₀ A) :
    Finsupp.linearCombination S (algebraMap A S ∘ f)
      (v.mapRange (algebraMap A S) (map_zero _)) =
      algebraMap A S (Finsupp.linearCombination A f v) := by
  classical
  simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype]

private theorem coefficientDegreeMap_comm
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] (r n : ℕ)
    (f : Fin r → A) :
    coefficientDegreeMap A S r n f ≫
      (ModuleCat.restrictScalars (algebraMap A S)).map
        (ModuleCat.ofHom (koszulDualBoundary S r n (algebraMap A S ∘ f))) =
      ModuleCat.ofHom (koszulDualBoundary A r n f) ≫
        coefficientDegreeMap A S r (n + 1) f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (koszulComplex A r f).X n ⟶ ModuleCat.of A A at x
  apply ModuleCat.hom_ext
  apply ((Finsupp.basisSingleOne : Module.Basis (Fin r) S
    (Fin r →₀ S)).exteriorPower (n + 1)).ext
  intro s
  let v : Fin (n + 1) → (Fin r →₀ A) :=
    (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)) ∘
      Set.powersetCard.ofFinEmbEquiv.symm s
  have hb : ((Finsupp.basisSingleOne : Module.Basis (Fin r) S
      (Fin r →₀ S)).exteriorPower (n + 1)) s =
      exteriorPower.ιMulti S (n + 1)
        (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _)) := by
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, v,
      Finsupp.coe_basisSingleOne, Function.comp_def]
  rw [hb]
  change (koszulDualBoundary S r n (algebraMap A S ∘ f)
      (ModuleCat.ofHom (coefficientFunctional A S r n x.hom))).hom _ =
    coefficientFunctional A S r (n + 1) (koszulDualBoundary A r n f x).hom _
  erw [coefficientFunctional_eval, koszulDualBoundary_wedge,
    koszulDualBoundary_wedge A r n f x v]
  simp only [ModuleCat.hom_ofHom, linearCombination_mapRange,
    map_mul, map_pow, map_neg, map_one, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  erw [← coefficientFunctional_eval A S r n x.hom (v ∘ i.succAbove)]
  rfl

/-- The coefficient extension cochain map with its evaluation formula.
Source: Stacks Project, Tag 0BQZ, finite free Koszul computation.
(blueprint: new-lem-sc-koszul-coefficient-extension-chi)

Proof: Write e_J for the increasing standard basis wedges of degree n. For a
functional x, define its extension by sending e_J over S to the image of x(e_J).
The exterior basis makes this a unique S-linear functional, and the assignment
is A-linear in x. Expanding any wedge in that basis expresses its coefficients
as minors of the vector-coordinate matrix. Ring maps preserve these minors,
which proves the evaluation formula. On a basis wedge the contraction is the
alternating sum of f(i) times the wedge omitting i. Applying A -> S to this
formula gives contraction for the image sequence. The signed dual differential
is precomposition with this contraction times (-1)^(n+1); the ring map preserves
that sign. Thus the degreewise extensions commute with every differential and
form chi. For n > r both exterior terms are zero; for n = 0 the single empty
basis wedge gives scalar extension A -> S. No regularity or localization assumption
is needed for this component. -/
theorem exists_koszul_coefficient_extension_chi
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (S : Type u) [CommRing S] [Algebra A S] :
  ∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f))),
  ∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v)) := by
  refine ⟨CochainComplex.ofHom (fun n ↦ coefficientDegreeMap A S r n f) ?_, ?_⟩
  · intro n
    simpa only [Functor.mapHomologicalComplex_obj_d, koszulDualComplex,
      CochainComplex.of_d] using coefficientDegreeMap_comm A S r n f
  · intro n x v
    exact coefficientFunctional_eval A S r n x.hom v

end ExteriorAlgebra
