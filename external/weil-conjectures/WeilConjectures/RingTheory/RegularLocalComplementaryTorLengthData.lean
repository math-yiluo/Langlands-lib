/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Length
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Auxiliary Tor and length data for complementary regular local quotients.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-tor-length-data)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace RingTheory

/-- The Tor and length conclusions follow from a finite free Koszul resolution
whose tensor homology is concentrated in degree zero. This statement isolates
that derived-category calculation from the explicit Koszul construction.
Source: Stacks Project, `intersection.tex`, Tag 0B1I.
(blueprint: new-d3-regular-local-complementary-tor-length-data)

Proof:
1. The Koszul terms are free, hence projective, and `ε` is a quasi-isomorphism to
   `A/I` in degree zero, so `(K, ε)` is a projective resolution of `A/I`. By
   `def-weil-pbc-tor-modules`, `Tor'_i(A/I, A/J)` is the `i`-th homology of
   `K ⊗ A/J`, which is `koszulComplexTensor A r g (A/J)`; `hpositive` gives
   `Tor'_i = 0` for `i > 0`.
2. In degree zero, `fromLeftDerivedZero` is an isomorphism because `- ⊗ A/J` is
   right exact. Multiplication identifies `A/I ⊗ A/J` with `A/(I ⊔ J)`, which is
   `A/m`, the residue field, by `htrans`; this is `eTensor`, with
   `(a+I) ⊗ (b+J) ↦ residue (a b)`. Put `eTor = fromLeftDerivedZero ≫ eTensor`.
3. Every `A`-submodule of the residue field is a subspace over it, since `A`
   surjects onto it; so its length is one (`def-weil-pbc-module-length`), and the
   zero modules `Tor'_i`, `i > 0`, have length zero. All lengths are finite and the
   alternating sum over `0 ≤ i ≤ r` is `1`.
-/
theorem regularLocal_complementary_tor_length_data
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (r : ℕ) (I J : Ideal A) (g : Fin r → A)
    (hspan : I = Ideal.span (Set.range g))
    (hpositive : ∀ n : ℕ, 0 < n →
      IsZero ((ExteriorAlgebra.koszulComplexTensor A r g
        (A ⧸ J)).homology n))
    (hfinite : ∀ n : ℕ, Module.Free A
      ((ExteriorAlgebra.koszulComplex A r g).X n))
    (haug : ∃ ε : ExteriorAlgebra.koszulComplex A r g ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ I)),
      QuasiIso ε)
    (htrans : I ⊔ J = IsLocalRing.maximalIdeal A) :
    (∀ i : ℕ, 0 < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J)))) ∧
    (∃ eTensor : ModuleCat.of A ((A ⧸ I) ⊗[A] (A ⧸ J)) ≅
        ModuleCat.of A (IsLocalRing.ResidueField A),
      ∃ eTor : (((Tor' (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (IsLocalRing.ResidueField A),
        (∀ a b : A, eTensor.hom
          (Ideal.Quotient.mk I a ⊗ₜ[A] Ideal.Quotient.mk J b) =
            IsLocalRing.residue A (a * b)) ∧
        eTor.hom = (Functor.fromLeftDerivedZero
          ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J)))).app
            (ModuleCat.of A (A ⧸ I)) ≫ eTensor.hom) ∧
    (∀ i : ℕ, Module.length A
      (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J))) ≠ ⊤) ∧
    (∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ i *
      (Module.length A
        (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J)))).toNat) = 1 := by
  obtain ⟨ε, hε⟩ := haug
  have _ : I = Ideal.span (Set.range g) := hspan
  let P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)) :=
    { complex := ExteriorAlgebra.koszulComplex A r g
      π := ε
      quasiIso := hε }
  have hproj : ∀ n, Projective (P.complex.X n) := by
    intro n
    have : Module.Free A ((ExteriorAlgebra.koszulComplex A r g).X n) := hfinite n
    dsimp [P]
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis A _)
  have htor : ∀ i : ℕ, 0 < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J))) := by
    intro i hi
    let F := (tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J))
    let e := (P.isoLeftDerivedObj F i)
    change IsZero ((F.leftDerived i).obj (ModuleCat.of A (A ⧸ I)))
    apply IsZero.of_iso ?_ e
    have hc : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex =
        ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J) := by
      dsimp [P, ExteriorAlgebra.koszulComplexTensor,
        ExteriorAlgebra.koszulComplex]
      rw [ChainComplex.map_chain_complex_of]
      rfl
    rw [HomologicalComplex.homologyFunctor_obj, hc]
    exact hpositive i hi
  let q₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ I) J
  let q₂ := DoubleQuot.quotQuotEquivQuotSup I J
  let q₃ := Ideal.quotientEquivAlgOfEq A htrans
  let q₂₃ := q₂.trans q₃.toRingEquiv
  let q := q₁.symm.toRingEquiv.trans q₂₃
  let qlin : (A ⧸ I) ⊗[A] (A ⧸ J) →ₗ[A]
      A ⧸ IsLocalRing.maximalIdeal A :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := by
        intro a x
        have hqa : q (algebraMap A _ a) = algebraMap A _ a := by
          change q₂₃ (q₁.symm (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : A))) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a
          rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
          simp only [one_smul]
          change q₃ (q₂ (DoubleQuot.quotQuotMk I J a)) = _
          rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
          rw [Ideal.quotientEquivAlgOfEq_mk]
        rw [Algebra.smul_def, Algebra.smul_def, q.map_mul, hqa]
        simp }
  let qlinEquiv := LinearEquiv.ofBijective qlin ⟨q.injective, q.surjective⟩
  let eTensor : ModuleCat.of A ((A ⧸ I) ⊗[A] (A ⧸ J)) ≅
      ModuleCat.of A (IsLocalRing.ResidueField A) :=
    by
      simpa only [IsLocalRing.ResidueField] using
        qlinEquiv.toModuleIso
  have hetensor : ∀ a b : A, eTensor.hom
      (Ideal.Quotient.mk I a ⊗ₜ[A] Ideal.Quotient.mk J b) =
        IsLocalRing.residue A (a * b) := by
    intro a b
    change q (Ideal.Quotient.mk I a ⊗ₜ[A] Ideal.Quotient.mk J b) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (a * b)
    change q₂₃ (q₁.symm
      (Ideal.Quotient.mk I a ⊗ₜ[A] Ideal.Quotient.mk J b)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
    have hq₂ (x : A) : q₂ (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J)
        (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk (I ⊔ J) x := by
      change DoubleQuot.quotQuotEquivQuotSup I J
        (DoubleQuot.quotQuotMk I J x) = _
      exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I J x
    rw [show q₂₃ = q₂.trans q₃.toRingEquiv by rfl]
    simp only [RingEquiv.trans_apply]
    rw [show (algebraMap A A) b = b by simp]
    change q₃.toRingEquiv (q₂ (Ideal.Quotient.mk
      (Ideal.map (Ideal.Quotient.mk I) J) (Ideal.Quotient.mk I (b * a)))) = _
    rw [hq₂ (b * a)]
    simp [q₃, mul_comm]
  let F := (tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J))
  have : PreservesFiniteColimits F := by
    dsimp [F]
    have : PreservesColimits (tensorLeft (ModuleCat.of A (A ⧸ J))) := inferInstance
    have : PreservesColimits (tensorRight (ModuleCat.of A (A ⧸ J))) :=
      preservesColimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A (A ⧸ J)))
    infer_instance
  let eTor : (((Tor' (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
      (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (IsLocalRing.ResidueField A) := by
    change (F.leftDerived 0).obj (ModuleCat.of A (A ⧸ I)) ≅ _
    exact (Functor.leftDerivedZeroIsoSelf F).app (ModuleCat.of A (A ⧸ I)) ≪≫ eTensor
  have hetor : eTor.hom = (Functor.fromLeftDerivedZero F).app
      (ModuleCat.of A (A ⧸ I)) ≫ eTensor.hom := by
    rfl
  have : IsSimpleModule A (IsLocalRing.ResidueField A) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := IsLocalRing.ResidueField A) (M := IsLocalRing.ResidueField A)
      IsLocalRing.residue_surjective).mpr inferInstance
  have hlen0 : Module.length A
      (((Tor' (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J))) = 1 := by
    rw [eTor.toLinearEquiv.length_eq]
    exact Module.length_eq_one A (IsLocalRing.ResidueField A)
  have hlenpos : ∀ i : ℕ, 0 < i → Module.length A
      (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J))) = 0 := by
    intro i hi
    let M := (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
      (ModuleCat.of A (A ⧸ J)))
    have : Subsingleton M := ModuleCat.subsingleton_of_isZero (htor i hi)
    exact Module.length_eq_zero
  have hlenfinite : ∀ i : ℕ, Module.length A
      (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J))) ≠ ⊤ := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · rw [hlen0]
      simp
    · have hi' : 0 < i := Nat.pos_of_ne_zero hi
      rw [hlenpos i hi']
      simp
  have hsum : (∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ i *
      (Module.length A
        (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J)))).toNat) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [hlen0]
    · intro b hb hne
      have hb' : 0 < b := Nat.pos_of_ne_zero hne
      rw [hlenpos b hb']
      simp
    · simp
  exact ⟨htor, ⟨eTensor, eTor, hetensor, hetor⟩, hlenfinite, hsum⟩

end RingTheory
