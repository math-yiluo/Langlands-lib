/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

import WeilConjectures.FieldTheory.SeparablyGeneratedDifferentialsDimension
import WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra


/-- Conormal decomposition with an explicit finite function-space summand.
Source: Stacks Project, Algebra, proof of Lemma Tag 00TV, using Tags 00TU and 00RT.
(blueprint: lem-weil-pbc-regular-local-fibre-finrank-add-fin-fun)

Proof: put R = S_q and K = kappa(q). Finite type makes R Noetherian and K finitely
 generated as a field. Identify the cotangent space with the kernel ideal's cotangent,
and extend its conormal map from R-scalars to K-scalars using the surjective residue map.
The separable-residue lemma makes this map injective; Mathlib's conormal sequence makes
its image the kernel of the surjective map to Omega[K/k]. Localization of differentials
and tensor cancellation identify the middle term with K tensor_S Omega[S/k], which is
finite dimensional. Rank-nullity therefore gives the sum of the two outer dimensions.
Transport the separating transcendence basis from the top intermediate field to K,
use its cardinality and hr to reindex it by Fin r, and apply the existing differential
basis dimension theorem. Its dimension is r, also the dimension of Fin r -> K. -/
theorem fibre_finrank_eq_cotangent_finrank_add_fin_fun
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField)
    (r : ℕ) (hr : Algebra.trdeg k q.ResidueField = (r : Cardinal.{v})) :
    Module.finrank q.ResidueField (q.ResidueField ⊗[S] KaehlerDifferential k S) =
      Module.finrank q.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime q)) +
        Module.finrank q.ResidueField (Fin r → q.ResidueField) := by
  classical
  let R := Localization.AtPrime q
  let K := q.ResidueField
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R ‹_›
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k S K
  have hfg : (⊤ : IntermediateField k K).FG := IntermediateField.fg_top k K
  have hsurj : Function.Surjective (algebraMap R K) := IsLocalRing.residue_surjective
  let e := Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
    (RingHom.ker (algebraMap R K)) IsLocalRing.ker_residue.symm
  let f : IsLocalRing.CotangentSpace R →ₗ[K] K ⊗[R] KaehlerDifferential k R :=
    LinearMap.extendScalarsOfSurjective hsurj
      ((KaehlerDifferential.kerCotangentToTensor k R K).comp e.toLinearMap)
  let g := KaehlerDifferential.mapBaseChange k R K
  have hf : Function.Injective f := separable_residue_cotangent_injective k R hfg hsep
  have hg : Function.Surjective g :=
    KaehlerDifferential.mapBaseChange_surjective k R K hsurj
  have hex : Function.Exact f g := by
    intro x
    change g x = 0 ↔ ∃ y, KaehlerDifferential.kerCotangentToTensor k R K (e y) = x
    rw [KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R K hsurj x]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨e.symm y, by simpa using hy⟩,
      fun ⟨y, hy⟩ ↦ ⟨e y, hy⟩⟩
  have : Algebra.FormallyEtale S R := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let eloc := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S R
  let efib : K ⊗[R] KaehlerDifferential k R ≃ₗ[K]
      K ⊗[S] KaehlerDifferential k S :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) eloc.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S R K K
        (KaehlerDifferential k S))
  have : Module.Finite K (K ⊗[R] KaehlerDifferential k R) :=
    Module.Finite.equiv efib.symm
  have hker : LinearMap.range f = LinearMap.ker g := by
    ext x
    exact (hex x).symm
  have hdim := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, ← hker,
    LinearMap.finrank_range_of_inj hf] at hdim
  have hres : Module.finrank K (KaehlerDifferential k K) = r := by
    obtain ⟨s, hs, hseps⟩ := hsep ⊤ hfg
    let etop : (⊤ : IntermediateField k K) ≃ₐ[k] K := IntermediateField.topEquiv
    let y : s → K := etop ∘ ((↑) : s → (⊤ : IntermediateField k K))
    have hy : IsTranscendenceBasis k y := etop.isTranscendenceBasis hs
    have hcard : Cardinal.mk s = (r : Cardinal.{v}) := by
      have hc : Cardinal.mk s = Algebra.trdeg k K := by
        simpa using hy.lift_cardinalMk_eq_trdeg
      exact hc.trans hr
    obtain ⟨ei⟩ := Cardinal.mk_eq_nat_iff.mp hcard
    let x : Fin r → K := y ∘ ei.symm
    have hx : IsTranscendenceBasis k x := hy.comp_equiv ei.symm
    let F := IntermediateField.adjoin k s
    have hF : F.map etop.toAlgHom = IntermediateField.adjoin k (Set.range x) := by
      rw [IntermediateField.adjoin_map]
      congr 1
      rw [show Set.range x = Set.range y from EquivLike.range_comp y ei.symm]
      exact ((Set.range_comp _ _).trans (congrArg (Set.image etop)
        Subtype.range_coe_subtype)).symm
    let eF : F ≃ₐ[k] IntermediateField.adjoin k (Set.range x) :=
      (IntermediateField.equivMap F etop.toAlgHom).trans (IntermediateField.equivOfEq hF)
    have : Algebra.IsSeparable F (⊤ : IntermediateField k K) := hseps
    have hxs : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K := by
      apply Algebra.IsSeparable.of_equiv_equiv eF.toRingEquiv etop.toRingEquiv
      ext a
      rfl
    obtain ⟨_, _, hd⟩ :=
      KaehlerDifferential.exists_basis_differentials_of_separating_transcendenceBasis
        hfg hsep x hx hxs
    exact_mod_cast hd.trans hr
  rw [← efib.finrank_eq, ← hdim, hres]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Nat.add_comm]
  rfl

/-- The residue-field fibre of the differentials has dimension equal to the embedding
dimension plus the residue-field transcendence degree.
Source: Stacks Project, Algebra, proof of Lemma Tag 00TV, using Tag 00TU.
(blueprint: lem-weil-pbc-regular-local-fibre-finrank-comparison).

Proof:
Put R = S_q and K = kappa(q). Finite type over k makes R Noetherian and K finitely
generated as a field. Its maximal ideal m is finitely generated, so m/m^2 is finite
dimensional over K. The quotient conormal sequence
m/m^2 -> K tensor_R Omega[R/k] -> Omega[K/k] -> 0 is right exact.
Separability of K/k makes the first map injective by Tag 00TU. A separating
transcendence basis of K/k has r elements by hr; its differentials form a basis
 of Omega[K/k], since the remaining algebraic extension is finite separable.
Thus the outer terms are finite dimensional, and short-exact-sequence dimension
additivity gives dimension of the middle term equal to dim_K(m/m^2) + r.
Localization of differentials gives Omega[R/k] = R tensor_S Omega[S/k]. Tensor
associativity identifies K tensor_R Omega[R/k] with K tensor_S Omega[S/k].
The canonical residue-field identification identifies m/m^2 with the cotangent
space of R, including its K scalar action. Transporting finranks proves the formula.
-/
theorem fibre_finrank_eq_cotangent_finrank_add
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField)
    (r : ℕ) (hr : Algebra.trdeg k q.ResidueField = (r : Cardinal.{v})) :
    Module.finrank q.ResidueField (q.ResidueField ⊗[S] KaehlerDifferential k S) =
      Module.finrank q.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime q)) + r := by
  rw [fibre_finrank_eq_cotangent_finrank_add_fin_fun k S q hsep r hr]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end Algebra
