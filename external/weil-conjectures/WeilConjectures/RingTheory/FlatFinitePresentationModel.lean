/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent

/-! # A flat finite presentation has a flat Noetherian model

Source: Stacks Project, Algebra, Tag 02JO (1), with the top ring as its own module.
(blueprint: lem-weil-pbc-flat-finite-presentation-model).
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace RingHom

-- Descend flatness on the compact spectrum, then descend the unit-ideal cover.
private theorem exists_flat_tensor_model
    {A₀ A B₀ : Type u} [CommRing A₀] [CommRing A] [CommRing B₀]
    [Algebra A₀ A] [Algebra A₀ B₀] [IsNoetherianRing A₀]
    [Algebra.FinitePresentation A₀ B₀] [Module.Flat A (A ⊗[A₀] B₀)] :
    ∃ T : Subalgebra A₀ A, T.FG ∧ Module.Flat T (T ⊗[A₀] B₀) := by
  classical
  open PrimeSpectrum in
  obtain ⟨T, hT, hflat⟩ :=
    exists_fg_forall_flat_localization_tensor_of_isCompact
      (R₀ := A₀) (S₀ := B₀) (A := A) (K := Set.univ) isCompact_univ
  have : Algebra.FiniteType A₀ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A₀ T
  let U := {q : PrimeSpectrum (T ⊗[A₀] B₀) |
    Module.Flat T (Localization.AtPrime q.asIdeal)}
  have hU : IsOpen U := PrimeSpectrum.isOpen_setOf_flat_localization
  let J : Ideal (T ⊗[A₀] B₀) := Ideal.span
    {g | (PrimeSpectrum.basicOpen g : Set _) ⊆ U}
  have hJ : J.map (Algebra.TensorProduct.map T.val (AlgHom.id A₀ B₀)) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let q : PrimeSpectrum (T ⊗[A₀] B₀) := PrimeSpectrum.comap
      (Algebra.TensorProduct.map T.val (AlgHom.id A₀ B₀)).toRingHom ⟨m, hm.isPrime⟩
    have hq : q ∈ U := hflat _ trivial
    obtain ⟨_, ⟨g, rfl⟩, hg, hgU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq hU
    exact hg (hle (Ideal.mem_map_of_mem _ (Ideal.subset_span hgU)))
  obtain ⟨T', hTT', hT', hJ'⟩ :=
    Subalgebra.exists_map_tensorProduct_inclusion_eq_top hT J hJ
  exact ⟨T', hT', Algebra.FinitePresentation.flat_tensorProduct_of_map_eq_top
    hTT' U (fun _ hq ↦ hq) hJ'⟩

-- Approximate the presentation over the integers and enlarge its base until it is flat.
private theorem exists_flat_model_same_universe
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] [Module.Flat A B] :
    ∃ (P Q : Type u) (_ : CommRing P) (_ : CommRing Q)
      (_ : Algebra P Q) (_ : Algebra P A),
      Algebra.FinitePresentation ℤ P ∧ Algebra.FinitePresentation P Q ∧
      (algebraMap P Q).Flat ∧
      ∃ e : A ⊗[P] Q ≃+* B,
        e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap A B := by
  classical
  obtain ⟨A₀, B₀, _, _, _, _, hA₀, hB₀, hpush⟩ :=
    Algebra.FinitePresentation.exists_fg_subalgebra_isPushout A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let e₀ : A ⊗[A₀] B₀ ≃ₐ[A] B := Algebra.IsPushout.equiv A₀ A B₀ B
  have : Module.Flat A (A ⊗[A₀] B₀) := Module.Flat.of_linearEquiv e₀.toLinearEquiv
  have : Algebra.FinitePresentation A₀ B₀ := hB₀
  obtain ⟨T, hT, hflat⟩ := exists_flat_tensor_model (A₀ := A₀) (A := A) (B₀ := B₀)
  let := Algebra.IsPushout.tensorProductAlgebra A₀ T A B₀ B
  have := Algebra.IsPushout.isScalarTower_tensorProductAlgebra A₀ T A B₀ B
  have := Algebra.IsPushout.tensorProduct A₀ T A B₀ B
  have hfin : Algebra.FiniteType ℤ T :=
    .trans (S := A₀) inferInstance ((Subalgebra.fg_iff_finiteType T).mp hT)
  let e : A ⊗[T] (T ⊗[A₀] B₀) ≃ₐ[A] B :=
    Algebra.IsPushout.equiv T A (T ⊗[A₀] B₀) B
  refine ⟨T, T ⊗[A₀] B₀, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp hfin, inferInstance,
    RingHom.flat_algebraMap_iff.mpr hflat, e.toRingEquiv, ?_⟩
  ext a
  exact e.commutes a

-- Transport the model and its comparison along arbitrary ring equivalences.
private theorem exists_flat_model_of_equiv.{w}
    {R : Type u} {S : Type v} {A B : Type w} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (f : R →+* S) (hfp : f.FinitePresentation) (hflat : f.Flat)
    (eA : A ≃+* R) (eB : B ≃+* S) :
    ∃ (P Q : Type w) (_ : CommRing P) (_ : CommRing Q)
      (_ : Algebra P Q) (_ : Algebra P R),
      Algebra.FinitePresentation ℤ P ∧ Algebra.FinitePresentation P Q ∧
      (algebraMap P Q).Flat ∧
      ∃ e : R ⊗[P] Q ≃+* S,
        e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom) = f := by
  let f' : A →+* B := eB.symm.toRingHom.comp (f.comp eA.toRingHom)
  have hfp' : f'.FinitePresentation :=
    (FinitePresentation.of_bijective eB.symm.bijective).comp
      (hfp.comp (FinitePresentation.of_bijective eA.bijective))
  have hflat' : f'.Flat :=
    (Flat.of_bijective eA.bijective).comp hflat |>.comp
      (Flat.of_bijective eB.symm.bijective)
  let : Algebra A B := f'.toAlgebra
  have : Algebra.FinitePresentation A B := hfp'
  have : Module.Flat A B := hflat'
  obtain ⟨P, Q, hP, hQ, hPQ, hPA, hfinP, hfinQ, hflatPQ, e, he⟩ :=
    exists_flat_model_same_universe (A := A) (B := B)
  let : Algebra P R := (eA.toRingHom.comp (algebraMap P A)).toAlgebra
  let eR : R ≃ₐ[P] A :=
    { eA.symm with
      commutes' := fun p ↦ by simp [RingHom.algebraMap_toAlgebra] }
  let e' : R ⊗[P] Q ≃+* S :=
    (((Algebra.TensorProduct.congr (S := P) eR
      (AlgEquiv.refl : Q ≃ₐ[P] Q)).toRingEquiv).trans e).trans eB
  refine ⟨P, Q, hP, hQ, hPQ, inferInstance, hfinP, hfinQ, hflatPQ, e', ?_⟩
  ext r
  have h := DFunLike.congr_fun he (eA.symm r)
  change e (eA.symm r ⊗ₜ[P] 1) = eB.symm (f (eA (eA.symm r))) at h
  rw [eA.apply_symm_apply] at h
  change eB (e (eA.symm r ⊗ₜ[P] 1)) = f r
  rw [h, eB.apply_symm_apply]

/-- A flat finitely presented ring map comes by base change from a flat map between
finitely presented integer algebras.
(blueprint: lem-weil-pbc-flat-finite-presentation-model)

Source: Stacks Project, Algebra, Tag 02JO (1), specialized to the module equal to
its top ring; the construction is Tag 00R0 and the local criterion is Tag 00R6.

Proof: approximate the given finite presentation by the same generators and
relations over finitely generated integer subalgebras of R. Their rings P and Q
are Noetherian, their transition squares are pushouts, and their colimits are R
and S. For each model the locus in Spec Q where Q is flat over P is open by
Tag 00RC. Its inverse image at any later model is contained in the later flat
locus, since localization commutes with base change and flatness is preserved by
base change and localization. For every prime of S, localize the approximation
at its contractions. The local rings are Noetherian; the localized top module is
cyclic, and transition rings are localizations of base changes. Tag 00R6 applied
to this system and the flat localized limit makes that prime lie in the inverse
image of one model's flat locus. These inverse images are directed open subsets
covering Spec S. Quasi-compactness gives a model whose flat locus pulls back to
all of Spec S. Write its closed complement as V(J). The image of J generates
the unit ideal in S. A finite unit-ideal relation descends to a later model,
including its coefficients and its equality to 1. Persistence of the flat loci
therefore makes the later model flat at every prime. The local criterion for
flatness makes P → Q flat. The original approximation supplies the displayed
base-change isomorphism and its compatibility with f. Both P and Q are finite
type over Noetherian rings, hence finitely presented over their stated bases.
-/
theorem exists_flat_finitePresentation_model
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hfp : f.FinitePresentation) (hflat : f.Flat) :
    ∃ (P Q : Type (max u v)) (_ : CommRing P) (_ : CommRing Q)
      (_ : Algebra P Q) (_ : Algebra P R),
      Algebra.FinitePresentation ℤ P ∧ Algebra.FinitePresentation P Q ∧
      (algebraMap P Q).Flat ∧
      ∃ e : R ⊗[P] Q ≃+* S,
        e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom) = f := by
  exact exists_flat_model_of_equiv (A := ULift.{v} R) (B := ULift.{u} S)
    f hfp hflat ULift.ringEquiv ULift.ringEquiv

end RingHom
