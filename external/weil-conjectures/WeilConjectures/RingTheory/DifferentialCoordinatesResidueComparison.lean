/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Injectivity of the residue differential comparison for differential coordinates

Source: Stacks Project, More on Algebra, Tag 07E6, proof.
-/

@[expose] public section

set_option autoImplicit false
universe u v
namespace Algebra

open scoped _root_.TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- The polynomial-localization differential comparison is injective when its residue
coordinates become a differential basis in an intermediate residue field.
Source: Stacks Project, More on Algebra, Tag 07E6, the assertion that the residue
comparison for A₀ is an isomorphism.
(blueprint: lem-weil-pbc-differential-coordinates-residue-comparison).

Proof: Put R = k[y], p = φ⁻¹(m_A), B = R_p and K₀ = κ(B).
The map R → κ(A) has kernel p, so it embeds R/p in κ(A) and extends to its fraction
field K₀. The images of the variables lie in F, so the extension lands in F.
Polynomial differentials form the free R-module on dX_i; localization and scalar
extension give a K₀-basis of K₀ tensor_B Ω[B/k] on 1 tensor dX_i.
A relation in the kernel of the residue comparison maps under Ω[K₀/k] → Ω[F/k]
to a relation among da_i. Since b_i = da_i is an F-basis and K₀ → F is injective,
each coefficient is zero. The basis in the source then makes the relation zero.
This covers m = 0, when the source module is zero. No geometric regularity,
characteristic condition, or finiteness of F is needed. -/
theorem injective_residue_differential_comparison_of_basis
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A]
    (F : IntermediateField k (IsLocalRing.ResidueField A))
    (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] A)
    (a : Fin m → F)
    (ha : ∀ i : Fin m, (a i : IsLocalRing.ResidueField A) =
      IsLocalRing.residue A (φ (MvPolynomial.X i)))
    (b : Module.Basis (Fin m) F (KaehlerDifferential k F))
    (hb : ∀ i : Fin m, b i = KaehlerDifferential.D k F (a i)) :
    let p := (IsLocalRing.maximalIdeal A).comap φ.toRingHom
    Function.Injective (KaehlerDifferential.mapBaseChange k
      (Localization.AtPrime p) (IsLocalRing.ResidueField (Localization.AtPrime p))) := by
  classical
  dsimp only
  let R := MvPolynomial (Fin m) k
  let p := (IsLocalRing.maximalIdeal A).comap φ.toRingHom
  let B := Localization.AtPrime p
  let K₀ := IsLocalRing.ResidueField B
  let f : R →ₐ[k] F := MvPolynomial.aeval a
  have hf : (F.val : F →ₐ[k] IsLocalRing.ResidueField A).comp f =
      (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)).comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [f] using ha i
  have hunit (y : p.primeCompl) : IsUnit (f y) := by
    apply isUnit_iff_ne_zero.mpr
    intro hy
    have hfy := AlgHom.congr_fun hf y.val
    have hz : IsLocalRing.residue A (φ y.val) = 0 := by
      have hfy' : (f y.val : IsLocalRing.ResidueField A) =
          IsLocalRing.residue A (φ y.val) := hfy
      rw [← hfy']
      change (f y.val : IsLocalRing.ResidueField A) = 0
      rw [hy]
      rfl
    exact y.2 ((IsLocalRing.residue_eq_zero_iff _).mp hz)
  let g : B →ₐ[k] F := IsLocalization.liftAlgHom hunit
  have hg (x : R) : g (algebraMap R B x) = f x := IsLocalization.lift_eq hunit x
  have hlocal : IsLocalHom g.toRingHom := by
    constructor
    intro x hx
    by_contra hn
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective p.primeCompl x
    change IsLocalization.mk' B r s = x at hrs
    have hr : r ∈ p := by
      apply (IsLocalization.AtPrime.mk'_mem_maximal_iff B p r s).mp
      rw [hrs]
      exact hn
    have hfr : f r = 0 := by
      apply Subtype.ext
      have h := AlgHom.congr_fun hf r
      change (f r : IsLocalRing.ResidueField A) = 0
      exact h.trans ((IsLocalRing.residue_eq_zero_iff _).mpr hr)
    have he : g x = 0 := by
      rw [← hrs]
      change IsLocalization.lift hunit (IsLocalization.mk' B r s) = 0
      rw [IsLocalization.lift_mk']
      have hfr' : f.toRingHom r = 0 := hfr
      rw [hfr', zero_mul]
    exact (isUnit_iff_ne_zero.mp hx) he
  let ρ := IsLocalRing.ResidueField.lift g.toRingHom
  let : Algebra K₀ F := ρ.toAlgebra
  have hρ (x : B) : algebraMap K₀ F (IsLocalRing.residue B x) = g x := rfl
  have : IsScalarTower k K₀ F := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply k B K₀]
    change algebraMap k F x = algebraMap K₀ F (IsLocalRing.residue B (algebraMap k B x))
    rw [hρ]
    exact (g.commutes x).symm
  let : Algebra B F := g.toRingHom.toAlgebra
  have : IsScalarTower k B F := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : IsScalarTower B K₀ F := IsScalarTower.of_algebraMap_eq fun x ↦ (hρ x).symm
  let bB := (KaehlerDifferential.mvPolynomialBasis k (Fin m)).ofIsLocalizedModule
    B p.primeCompl (KaehlerDifferential.map k k R B)
  let bK := bB.baseChange K₀
  let t : K₀ ⊗[B] KaehlerDifferential k B →ₗ[K₀] KaehlerDifferential k F :=
    (KaehlerDifferential.map k k B F).liftBaseChange K₀
  have hbase (i : Fin m) : bK i =
      1 ⊗ₜ[B] KaehlerDifferential.D k B (algebraMap R B (MvPolynomial.X i)) := by
    rw [Module.Basis.baseChange_apply, Module.Basis.ofIsLocalizedModule_apply]
    change 1 ⊗ₜ[B] KaehlerDifferential.map k k R B
      (KaehlerDifferential.mvPolynomialBasis k (Fin m) i) = _
    rw [KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
  have ht (i : Fin m) : t (bK i) = b i := by
    rw [hbase]
    simp only [t, LinearMap.liftBaseChange_tmul, one_smul]
    change (KaehlerDifferential.map k k B F)
      (KaehlerDifferential.D k B (algebraMap R B (MvPolynomial.X i))) = b i
    rw [KaehlerDifferential.map_D]
    change KaehlerDifferential.D k F (g (algebraMap R B (MvPolynomial.X i))) = b i
    rw [hg]
    rw [show f (MvPolynomial.X i) = a i from MvPolynomial.aeval_X a i]
    exact (hb i).symm
  have hti : Function.Injective t := by
    apply LinearMap.injective_of_linearIndependent bK.span_eq
    have hi : LinearIndependent K₀ (fun i ↦ b i) :=
      b.linearIndependent.restrict_scalars' K₀
    have he : (fun i ↦ t (bK i)) = (fun i ↦ b i) := funext ht
    change LinearIndependent K₀ (fun i ↦ t (bK i))
    rw [he]
    exact hi
  have hcomm : (KaehlerDifferential.map k k K₀ F).comp
      (KaehlerDifferential.mapBaseChange k B K₀) = t := by
    apply bK.ext
    intro i
    rw [LinearMap.comp_apply, hbase]
    simp only [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
      one_smul, t, LinearMap.liftBaseChange_tmul]
    change KaehlerDifferential.D k F
        (algebraMap K₀ F (IsLocalRing.residue B (algebraMap R B (MvPolynomial.X i)))) =
      KaehlerDifferential.D k F (g (algebraMap R B (MvPolynomial.X i)))
    exact congrArg (KaehlerDifferential.D k F) (hρ _)
  intro x y hxy
  apply hti
  rw [← hcomm]
  exact congrArg (KaehlerDifferential.map k k K₀ F) hxy

end Algebra
