/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.GeometricallyRegularH1Injective
import WeilConjectures.RingTheory.TransitivityGamma
import WeilConjectures.RingTheory.DifferentialCoordinatesResidueComparison
import WeilConjectures.RingTheory.LocalCotangentComparisonNaturality
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Cotangent independence from differential coordinates

Source: Stacks Project, More on Algebra, Tag 07E6, proof before the final application
of Algebra, Tags 07DY and 00NQ.
-/

@[expose] public section

set_option autoImplicit false
universe u v
namespace Algebra

set_option backward.isDefEq.respectTransparency false in
private noncomputable def residueCotangentEquiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    let P := Extension.ofSurjective (Algebra.ofId R (IsLocalRing.ResidueField R))
      IsLocalRing.residue_surjective
    P.Cotangent ≃ₗ[IsLocalRing.ResidueField R] IsLocalRing.CotangentSpace R := by
  let P := Extension.ofSurjective (Algebra.ofId R (IsLocalRing.ResidueField R))
    IsLocalRing.residue_surjective
  have hp : P.ker = IsLocalRing.maximalIdeal R :=
    show RingHom.ker (IsLocalRing.residue R) = _ from IsLocalRing.ker_residue
  exact (P.cotangentEquivCotangentKer.trans
    (Ideal.Cotangent.equivOfEq P.ker (IsLocalRing.maximalIdeal R) hp)).extendScalarsOfSurjective
      IsLocalRing.residue_surjective

set_option backward.isDefEq.respectTransparency false in
private theorem residueCotangentEquiv_mk
    (R : Type*) [CommRing R] [IsLocalRing R] :
    let P := Extension.ofSurjective (Algebra.ofId R (IsLocalRing.ResidueField R))
      IsLocalRing.residue_surjective
    ∀ x : P.ker, residueCotangentEquiv R (Extension.Cotangent.mk x) =
      (IsLocalRing.maximalIdeal R).toCotangent
        ⟨x.val, (IsLocalRing.residue_eq_zero_iff _).mp x.2⟩ := by
  intro P x
  simp only [residueCotangentEquiv, LinearEquiv.extendScalarsOfSurjective_apply,
    LinearEquiv.trans_apply, Extension.cotangentEquivCotangentKer_apply,
    Extension.Cotangent.val_mk, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A residue differential basis preserves independence of cotangent classes from the
polynomial localization after extending coefficients to the target residue field.
Source: Stacks Project, More on Algebra, Tag 07E6, proof, the differential comparison
and the commutative square, before extending a regular system of parameters.
(blueprint: lem-weil-pbc-differential-coordinates-cotangent-independent).

Proof: Write R = k[y], p = φ⁻¹(m), A₀ = R_p, and K₀ for the residue field of A₀.
The restriction equation for ψ identifies its residue-field map with the embedding
of Frac(R/p) in K. Its image lies in F because the residue images of the variables
lie in F. Polynomial differentials and localization identify Ω[A₀/k] with a free
module on dy_i. The residue comparison Ω[A₀/k] ⊗ K₀ → Ω[K₀/k] is surjective.
A relation among d(y_i) in Ω[K₀/k] maps to a relation in Ω[F/k]; the supplied basis
makes every coefficient zero. Thus this comparison is an isomorphism.
The ring A₀ is geometrically regular: after a finite purely inseparable field
extension it is a localization of a polynomial ring over that field, hence regular.
Proposition 07E5 gives injectivity of H₁(L[K₀/k]) → m₀/m₀². Jacobi-Zariski and the
isomorphic residue differential comparison give surjectivity, hence an isomorphism.
The right-hand comparison sends the class of z tensored with c to c times the class
of ψ(z). The square with bottom H₁(L[K/k]) → m/m² commutes as follows. The two
composites from the presentation k[K₀] to A[K] factor respectively through A₀[K₀]
and k[K]. They induce the same map on H₁ by independence of presentation morphisms
and compatibility with composition. The surjection-to-conormal equivalences are
compatible with these maps: choose a section of A → K agreeing on K₀ with ψ of a
section of A₀ → K₀. Evaluation of a relation then gives ψ of its old evaluation,
so its conormal class maps to the class of ψ(z). Tensoring yields the square.
Its top is an isomorphism; its left is injective by 07E2 and its bottom by 07E5
for A. Thus its right is injective, because every source element comes from the
top and equality of its images forces equality along the left and bottom.
An independent family of classes in m₀/m₀² stays independent under field scalar
extension. The injective right-hand map therefore takes it to independent cotangent
classes in m/m², proving the assertion. Arbitrary independent sets are allowed: the
same argument applies to each finite relation. Empty sets and an empty differential
basis are included; no finiteness of K over k is assumed. -/
theorem linearIndepOn_of_residue_differential_basis
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (pchar : ℕ) [Fact pchar.Prime] [CharP k pchar]
    (hreg : IsGeometricallyRegular k A)
    (F : IntermediateField k (IsLocalRing.ResidueField A)) (hF : F.FG)
    (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] A)
    (a : Fin m → F)
    (ha : ∀ i : Fin m, (a i : IsLocalRing.ResidueField A) =
      IsLocalRing.residue A (φ (MvPolynomial.X i)))
    (b : Module.Basis (Fin m) F (KaehlerDifferential k F))
    (hb : ∀ i : Fin m, b i = KaehlerDifferential.D k F (a i)) :
    let p := (IsLocalRing.maximalIdeal A).comap φ.toRingHom
    ∀ (ψ : Localization.AtPrime p →+* A) [IsLocalHom ψ],
      ψ.comp (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime p)) =
        φ.toRingHom →
      ∀ s : Set (IsLocalRing.maximalIdeal (Localization.AtPrime p)),
        LinearIndepOn (IsLocalRing.ResidueField (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)).toCotangent s →
        LinearIndepOn (IsLocalRing.ResidueField A)
          (fun x : IsLocalRing.maximalIdeal (Localization.AtPrime p) ↦
            (IsLocalRing.maximalIdeal A).toCotangent
            ⟨ψ x, map_nonunit ψ x x.2⟩) s := by
  classical
  have _hF := hF
  intro p ψ _ hψ s hs
  let B := Localization.AtPrime p
  let K₀ := IsLocalRing.ResidueField B
  let K := IsLocalRing.ResidueField A
  let : Algebra B A := ψ.toAlgebra
  have : IsLocalHom (algebraMap B A) := ‹IsLocalHom ψ›
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap k A r = ψ (algebraMap k B r)
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k) B]
    exact (φ.commutes r).symm.trans
      (RingHom.congr_fun hψ (algebraMap k (MvPolynomial (Fin m) k) r)).symm
  let P₀ := Extension.ofSurjective (Algebra.ofId B K₀) IsLocalRing.residue_surjective
  let P := Extension.ofSurjective (Algebra.ofId A K) IsLocalRing.residue_surjective
  let c₀ := P₀.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k B K₀ K₀)
  let c := P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)
  have hw : Function.Injective (KaehlerDifferential.mapBaseChange k B K₀) :=
    injective_residue_differential_comparison_of_basis k A F m φ a ha b hb
  have hc₀ : Function.Surjective c₀ := by
    intro y
    let z := P₀.h1CotangentEquivCotangent.symm y
    have hz : H1Cotangent.δ k B K₀ z = 0 := by
      apply hw
      rw [map_zero]
      exact (H1Cotangent.exact_δ_mapBaseChange k B K₀).apply_apply_eq_zero z
    obtain ⟨x, hx⟩ := (H1Cotangent.exact_map_δ k B K₀ z).mp hz
    refine ⟨x, ?_⟩
    change P₀.h1CotangentEquivCotangent ((H1Cotangent.map k B K₀ K₀) x) = y
    rw [hx]
    exact P₀.h1CotangentEquivCotangent.apply_symm_apply y
  obtain ⟨μ, hμ, hcomm⟩ := exists_localCotangentComparison_naturality k B A
  have hc : Function.Injective c :=
    (isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular
      k A pchar hreg).2
  have hleft := (transitivityGamma k K₀ K).1
  have hμinj : Function.Injective μ := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := LinearMap.baseChange_surjective K hc₀ x
    obtain ⟨y', rfl⟩ := LinearMap.baseChange_surjective K hc₀ y
    have he : (μ.comp (c₀.baseChange K)) x' = (μ.comp (c₀.baseChange K)) y' := hxy
    rw [hcomm] at he
    exact congrArg (c₀.baseChange K) (hleft (hc he))
  let q₀ := residueCotangentEquiv B
  let q := residueCotangentEquiv A
  let v : s → P₀.Cotangent := fun x ↦ q₀.symm
    ((IsLocalRing.maximalIdeal B).toCotangent x.val)
  have hv : LinearIndependent K₀ v := hs.linearIndependent.map' q₀.symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr q₀.symm.injective)
  have hvt := Module.Flat.linearIndependent_one_tmul (S := K) hv
  have hli := (hvt.map' μ (LinearMap.ker_eq_bot.mpr hμinj)).map' q.toLinearMap
    (LinearMap.ker_eq_bot.mpr q.injective)
  change LinearIndependent K (fun x : s ↦ q (μ (_root_.TensorProduct.tmul K₀ (1 : K) (v x)))) at hli
  change LinearIndependent K _
  convert hli using 1
  ext x
  symm
  let z : P₀.ker := ⟨x.val.val, by
    change IsLocalRing.residue B x.val.val = 0
    exact (IsLocalRing.residue_eq_zero_iff _).mpr x.val.2⟩
  have hz : q₀ (Extension.Cotangent.mk z) =
      (IsLocalRing.maximalIdeal B).toCotangent x.val := residueCotangentEquiv_mk B z
  have hvz : v x = Extension.Cotangent.mk z := by
    apply q₀.injective
    exact (q₀.apply_symm_apply _).trans hz.symm
  change q (μ (_root_.TensorProduct.tmul K₀ (1 : K) (v x))) = _
  rw [hvz, hμ, one_smul, residueCotangentEquiv_mk]
  rfl


end Algebra
