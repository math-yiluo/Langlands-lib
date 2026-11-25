/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.Mathlib.Algebra.Algebra.Pi

/-!
# Points of étale algebras over a separably closed field

An étale algebra `A` over a separably closed field `K` is a finite product of copies of `K`, so
its `K`-algebra homomorphisms to any field extension `L` of `K` are the projections onto the
factors; in particular there are exactly `dim_K A` of them.

## Main statements

- `Algebra.Etale.finrank_eq_natCard_primeSpectrum`: `dim_K A` is the number of primes of `A`.
- `Algebra.Etale.natCard_algHom_eq_finrank`: `#(A →ₐ[K] L) = dim_K A`.
- `Algebra.Etale.iff_subsingleton_kaehlerDifferential_of_field`: a finite algebra over a field
  is étale if and only if its module of Kähler differentials vanishes.
- `Algebra.Etale.of_finite_of_isSeparable`: a finite separable field extension is étale.
- `Algebra.Etale.of_isReduced_of_perfectField`: a finite reduced algebra over a perfect field is
  étale.
- `Algebra.Etale.of_forall_finrank_localization_eq_one`: a finite algebra over a field whose
  local rings at maximal ideals are one-dimensional is étale.
- `RingHom.Etale.of_comp_of_field`: a subextension of a finite separable field extension is
  finite separable.
-/

@[expose] public section

universe u v

open Module

namespace Algebra.Etale

variable (K : Type u) (A : Type u) [Field K] [IsSepClosed K] [CommRing A] [Algebra K A]
  [Algebra.Etale K A]

omit [IsSepClosed K] in
include K in
/-- An étale algebra over a field has finitely many primes. -/
theorem finite_primeSpectrum : Finite (PrimeSpectrum A) := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  infer_instance

/-- An étale algebra over a separably closed field `K` has `K`-dimension the number of its
primes. -/
theorem finrank_eq_natCard_primeSpectrum : finrank K A = Nat.card (PrimeSpectrum A) := by
  have := finite_primeSpectrum K A
  have := Fintype.ofFinite (PrimeSpectrum A)
  rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- The `K`-algebra homomorphism `A →ₐ[K] L` given by the factor of `A ≃ₐ[K] Π_p K` at a
prime `p` of `A`, followed by the inclusion `K → L`. -/
noncomputable def algHomOfPrimeSpectrum (L : Type v) [Field L] [Algebra K L]
    (p : PrimeSpectrum A) : A →ₐ[K] L :=
  (Algebra.ofId K L).comp ((Pi.evalAlgHom K (fun _ ↦ K) p).comp
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toAlgHom)

theorem algHomOfPrimeSpectrum_injective (L : Type v) [Field L] [Algebra K L] :
    Function.Injective (algHomOfPrimeSpectrum K A L) := by
  classical
  intro p q h
  by_contra hpq
  have := congr($h ((Algebra.FormallyEtale.equivPiOfIsSepClosed K A).symm (Pi.single p 1)))
  simp [algHomOfPrimeSpectrum, Ne.symm hpq] at this

/-- An étale algebra `A` over a separably closed field `K` has exactly `dim_K A` algebra
homomorphisms to any field extension `L` of `K`. -/
theorem natCard_algHom_eq_finrank (L : Type v) [Field L] [Algebra K L] :
    Nat.card (A →ₐ[K] L) = finrank K A := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  refine le_antisymm (card_algHom_le_finrank K A L) ?_
  have := finite_primeSpectrum K A
  rw [finrank_eq_natCard_primeSpectrum]
  exact Nat.card_le_card_of_injective _ (algHomOfPrimeSpectrum_injective K A L)

attribute [local instance] Ideal.Quotient.field in
/-- A finite reduced algebra over a perfect field is étale: it is a finite product of finite,
hence separable, field extensions. -/
theorem of_isReduced_of_perfectField (K A : Type*) [Field K] [PerfectField K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.Etale K A := by
  have : IsArtinianRing A := .of_finite K A
  have (I : MaximalSpectrum A) : Algebra.FormallyEtale K (A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyEtale.iff_isSeparable]
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨.of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm,
    FinitePresentation.of_finiteType.mp inferInstance⟩

/-- A finite algebra over a field `K` all of whose local rings at maximal ideals are
one-dimensional is étale: it is a finite product of copies of `K`. -/
theorem of_forall_finrank_localization_eq_one {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A]
    (h : ∀ m : MaximalSpectrum A, finrank K (Localization.AtPrime m.asIdeal) = 1) :
    Algebra.Etale K A := by
  have : IsArtinianRing A := .of_finite K A
  have : Finite (MaximalSpectrum A) :=
    Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective
  have (m : MaximalSpectrum A) : Algebra.FormallyEtale K (Localization.AtPrime m.asIdeal) := by
    have : Module.Finite K (Localization.AtPrime m.asIdeal) :=
      .of_surjective (IsScalarTower.toAlgHom K A _).toLinearMap
        (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
    have hinj : Function.Injective (Algebra.linearMap K (Localization.AtPrime m.asIdeal)) :=
      (algebraMap K _).injective
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [h, Module.finrank_self])).1 hinj
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId K _) ⟨hinj, hsurj⟩)
  exact ⟨.of_equiv ((MaximalSpectrum.toPiLocalizationEquiv A).restrictScalars K).symm,
    FinitePresentation.of_finiteType.mp inferInstance⟩

end Algebra.Etale

namespace Algebra.Etale

/-- A finite algebra `A` over a field `K` is étale if and only if `Ω[A⁄K] = 0`.

Part of blueprint `proposition-multiplication-n--2`. A finite `K`-algebra is of finite
presentation, and over a field formally unramified algebras of finite type are formally
étale. -/
theorem iff_subsingleton_kaehlerDifferential_of_field {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] :
    Algebra.Etale K A ↔ Subsingleton Ω[A⁄K] := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  have : Algebra.FormallyUnramified K A := ⟨h⟩
  exact ⟨.of_formallyUnramified_of_field K A,
    FinitePresentation.of_finiteType.mp inferInstance⟩

/-- A finite separable field extension is étale. -/
theorem of_finite_of_isSeparable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : Algebra.Etale K L :=
  ⟨.of_isSeparable K L, FinitePresentation.of_finiteType.mp inferInstance⟩

end Algebra.Etale

/-- If the composite `K → L → M` of field homomorphisms is étale, that is, `M` is finite separable
over `K`, then so is `K → L`. -/
theorem RingHom.Etale.of_comp_of_field {K L M : Type*} [Field K] [Field L] [Field M]
    (f : K →+* L) (g : L →+* M) (h : (g.comp f).Etale) : f.Etale := by
  algebraize [f, g.comp f]
  let φ : L →ₐ[K] M := { toRingHom := g, commutes' := fun _ ↦ rfl }
  have : Algebra.IsSeparable K M := (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  have : Module.Finite K M := Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom _ _ φ
  have : Module.Finite K L := Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
  exact RingHom.etale_algebraMap.mpr .of_finite_of_isSeparable

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.RingTheory.Etale.Field`) -/

/-- If `A` is an étale algebra over a field `k` and `φ : A →ₐ[k] B` is an algebra homomorphism
to a local ring `B`, then every element of the image of `φ` is separable over `k`. -/
lemma IsSeparable.of_algHom_etale_to_isLocalRing (k : Type u) [Field k] (A : Type u)
    [CommRing A] [Algebra k A] [Algebra.Etale k A] (B : Type u) [CommRing B] [Algebra k B]
    [IsLocalRing B] (φ : A →ₐ[k] B) (a : A) : IsSeparable k (φ a) := by
  nontriviality B
  have : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  obtain ⟨I, _, Ai, hfield, halg, e, hprop⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := A)).mp inferInstance
  let : ∀ i, Field (Ai i) := hfield
  let : ∀ i, Algebra k (Ai i) := halg
  classical
  let ψ : (∀ i, Ai i) →ₐ[k] B := φ.comp e.symm
  obtain ⟨j, hj, hothers⟩ := ψ.exists_pi_single_eq_one_of_isLocalRing
  let τ := ψ.piFactor j hj hothers
  have hφa : φ a = τ (e a j) := by
    rw [← ψ.eq_piFactor_apply j hj hothers (e a)]
    exact (congrArg φ (e.symm_apply_apply a)).symm
  rw [hφa]
  have : Algebra.IsSeparable k (Ai j) := (hprop j).2
  have hb_sep : IsSeparable k (e a j) := Algebra.IsSeparable.isSeparable k _
  refine hb_sep.of_dvd <| minpoly.dvd k _ ?_
  rw [Polynomial.aeval_algHom_apply]
  simp [minpoly.aeval]
