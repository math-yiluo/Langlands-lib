/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GeometricallyRegularH1Injective
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra
set_option linter.unusedVariables false in
/-- The localized prime-power quotient has the Artinian-local and cotangent-finiteness
properties needed to apply the Popescu directed-subalgebra theorem.
(blueprint: lem-weil-pbc-popescu-flat-coordinates-setup)

Source: Stacks Project, Tag 07FH, first paragraph of the proof, and Tag 07E5.

Proof: Write L = Localization.AtPrime q and J = qL. Localization makes L Noetherian
and local with maximal ideal J. For every finite purely inseparable extension k'/k,
the algebra k' tensor L is the localization of k' tensor Λ at the image of Λ minus q.
Geometric regularity of Λ makes the latter regular; localization preserves regularity.
Thus L is geometrically regular. Since k is a field of characteristic p > 0, p is prime,
so Tag 07E5 applies and gives an injective K-linear map H1Cotangent k K into J/J²,
where K is the residue field of L. The ideal J is finitely generated because L is
Noetherian. The classes of any finite generating set span J/J² over K, so this space
is finite dimensional. An injective linear map into it makes H1Cotangent k K finite.

Because n ≥ 1, J^n is contained in the proper maximal ideal J and has radical J.
Consequently B = L/J^n is nonzero and local: the unique maximal ideal is the image of J.
It is Noetherian as a quotient of L. Every prime ideal of B pulls back to a prime of L
containing J^n, hence containing J, and must therefore pull back to J. Thus B has
Krull dimension zero and is Artinian by the Noetherian dimension-zero criterion.
The quotient map L → B followed by the residue map has kernel J. The third
isomorphism theorem therefore gives a k-algebra isomorphism from the residue field of B
to K. Functoriality of H1Cotangent along this isomorphism and its inverse gives inverse
semilinear maps on H1Cotangent; transport a finite K-generating set along these maps.
This proves the stated finiteness over the residue field of B. The existential witnesses
hArt and hLoc are proofs of properties of the already constructed quotient, not choices
of ring data. -/
theorem popescu_flat_coordinates_setup
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ hArt : IsArtinianRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n),
      ∃ hLoc : IsLocalRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n),
      IsLocalRing.maximalIdeal (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
        (q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) ∧
      Module.Finite (IsLocalRing.ResidueField
        (Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
        (H1Cotangent k (IsLocalRing.ResidueField
          (Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) := by
  let L := Localization.AtPrime q
  let J : Ideal L := q.map (algebraMap Λ L)
  have hJ : J = IsLocalRing.maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
  have hpow : J ^ n ≤ J := Ideal.pow_le_self (by omega)
  have hproper : J ^ n ≠ ⊤ := by
    intro h
    have := hpow
    rw [h, hJ] at this
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top (top_le_iff.mp this)
  let B := L ⧸ J ^ n
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (J ^ n)) Ideal.Quotient.mk_surjective
  have hmax : IsLocalRing.maximalIdeal B = J.map (Ideal.Quotient.mk (J ^ n)) := by
    exact (IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (J ^ n)) Ideal.Quotient.mk_surjective).symm.trans
        (congrArg (Ideal.map (Ideal.Quotient.mk (J ^ n))) hJ.symm)
  have hArt : IsArtinianRing B := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    rw [Ideal.minimalPrimes, Set.mem_ofPred]
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simpa [← hJ] using hpow
    · intro P hP hle
      have hrad := Ideal.radical_mono hP.2
      rw [J.radical_pow (by omega), hJ, (IsLocalRing.maximalIdeal.isMaximal L).isPrime.radical,
        hP.1.radical] at hrad
      exact hrad
  have hlocalreg : IsGeometricallyRegular k L := by
    refine ⟨inferInstance, ?_⟩
    intro k' _ _ _ _
    let : IsRegularRing (TensorProduct k k' Λ) := hreg.2 k'
    let f : TensorProduct k k' Λ →ₐ[k] TensorProduct k k' L :=
      Algebra.TensorProduct.map (AlgHom.id k k') (IsScalarTower.toAlgHom k Λ L)
    let : Algebra (TensorProduct k k' Λ) (TensorProduct k k' L) := f.toAlgebra
    have : IsScalarTower k' (TensorProduct k k' Λ) (TensorProduct k k' L) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change x ⊗ₜ[k] (1 : L) = f (x ⊗ₜ[k] (1 : Λ))
        simp [f]
    let M := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := k) (A := k'))
    have : IsLocalization M (TensorProduct k k' L) :=
      IsLocalization.tensorProduct_tensorProduct_right k k' q.primeCompl L (by
        ext x
        change f (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] (algebraMap Λ L x)
        simp [f])
    apply RingTheory.isRegularRing_of_localization
      (TensorProduct k k' Λ) (TensorProduct k k' L) M (algebraMap _ _)
    · exact IsLocalization.map_units _
    · intro y
      obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj M y
      obtain ⟨u, hu⟩ := (IsLocalization.map_units (TensorProduct k k' L) s).exists_right_inv
      refine ⟨r, s, u, ?_, hu, ?_⟩
      · exact isUnit_iff_exists_inv.mpr
          ⟨algebraMap _ _ s.1, by rw [mul_comm]; exact hu⟩
      · calc
          y = y * (algebraMap (TensorProduct k k' Λ) (TensorProduct k k' L) s.1 * u) := by
            rw [hu, mul_one]
          _ = algebraMap _ _ r * u := by rw [← mul_assoc, hs]
    · intro r hr
      obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists M (TensorProduct k k' L)
        (x := r) (y := 0)).mp (by simpa using hr)
      exact ⟨s, by simpa using hs⟩
  have : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k (Nat.ne_of_gt hp)⟩
  let K := IsLocalRing.ResidueField L
  let P := Extension.ofSurjective (Algebra.ofId L K) IsLocalRing.residue_surjective
  have hinj :=
    (isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular
      k L p hlocalreg).2
  have hfinite : Module.Finite K (H1Cotangent k K) := by
    have hfg : P.ker.FG := by
      change (RingHom.ker (algebraMap L K)).FG
      exact IsNoetherian.noetherian _
    have : Module.Finite K P.Cotangent := Extension.Cotangent.finite hfg
    exact Module.Finite.of_injective
      (P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k L K K)) hinj
  refine ⟨hArt, inferInstance, hmax, ?_⟩
  let fB : L →ₐ[k] B := IsScalarTower.toAlgHom k L B
  have : IsLocalHom fB.toRingHom :=
    IsLocalHom.of_surjective fB.toRingHom Ideal.Quotient.mk_surjective
  have : IsLocalHom fB := ⟨fun a ha ↦ isUnit_of_map_unit fB.toRingHom a ha⟩
  let fK : K →ₐ[k] IsLocalRing.ResidueField B := IsLocalRing.ResidueField.mapAlgHom fB
  have hfK : Function.Surjective fK := by
    intro x
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨IsLocalRing.residue L a, rfl⟩
  let e : K ≃ₐ[k] IsLocalRing.ResidueField B := AlgEquiv.ofBijective fK
    ⟨fK.injective, hfK⟩
  let : Algebra K (IsLocalRing.ResidueField B) := e.toRingHom.toAlgebra
  have : IsScalarTower k K (IsLocalRing.ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : Module.Finite K (H1Cotangent k (IsLocalRing.ResidueField B)) :=
    Module.Finite.of_surjective
      (H1Cotangent.map k k K (IsLocalRing.ResidueField B)) (H1Cotangent.mapEquiv k _ _ e).surjective
  exact Module.Finite.of_restrictScalars_finite K (IsLocalRing.ResidueField B) _

end Algebra
