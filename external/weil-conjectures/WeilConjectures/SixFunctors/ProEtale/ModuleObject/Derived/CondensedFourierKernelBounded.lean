/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-! Bounded constructibility of the condensed Fourier kernels.

Source: Fourier specialization paragraph of `proposition-fourier-inversion`
(blueprint: proposition-fourier-inversion), using `lemma-artin-schreier-character-sheaf`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

-- The recorded statement binds `hp` and `hk`, which the proof does not use.
set_option linter.unusedVariables false in
/-- Every displayed condensed Fourier kernel placed in degree zero is bounded
constructible, including the noninvertible-cardinality branch of its definition.

Source: latest blueprint Fourier specialization in `lem-fd-kernel-composition.md`,
`lemma-artin-schreier-character-sheaf`, and the actual projector definition of
`lemma-artin-schreier-character-sheaf--1` (blueprint: lem-fd-fourier-kernel-bounded).

Proof: if the finite-field cardinality is invertible in the scalar coefficient ring,
lemma-artin-schreier-character-sheaf gives a cover on which the kernel is the regular module.
Identify the regular module with the free module of rank one; local freeness gives finite
presentation on the trivial stratification, hence constructibility. The degree-zero
single functor then gives bounded constructibility. If the cardinality is not a unit,
Ring.inverse is zero, so every term of the character projector vanishes. Its image
is zero; pullback preserves zero and a zero sheaf is constructible. No characteristic
relation between the two fields is needed for this second branch. -/
theorem condensedFourierKernel_boundedConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (p : ℕ) [Fact p.Prime]
    (hΛ : ∃ (l : ℕ) (_hl : Fact l.Prime), l ≠ p ∧ ((∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} l))))
    (hp : IsUnit (p : MonObj.Γ Λ))
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    {S V W : Scheme.{u}} [S.Over (Spec (.of k))]
    [V.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))]
    [QuasiCompact (W ↘ Spec (.of k))] [IsSeparated (W ↘ Spec (.of k))]
    (π : V ⟶ S) (π' : W ⟶ S)
    [(pullback π π').Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) :
    boundedConstructible (condensedRingObj Λ (pullback π π'))
      ((DerivedCategory.singleFunctor _ 0).obj
        (condensedFourierKernel Λ k₀ π π' ψ b)) := by
  classical
  obtain ⟨l, hl, _, hCoeff⟩ := hΛ
  have had : IsAdmissibleCoefficient Λ :=
    ⟨l, hl, Or.inr (Or.inr (Or.inr hCoeff))⟩
  by_cases hq : IsUnit (Fintype.card k₀ : MonObj.Γ Λ)
  · obtain ⟨_, ⟨U, hU⟩, _, _, _⟩ :=
      Etale.prop_kernel_lisse.2.2.2 Λ k₀ hq had (pullback π π') ψ ψ b
    let L := condensedFourierKernel Λ k₀ π π' ψ b
    have hfree : IsLocallyFree (condensedRingObj Λ (pullback π π')) L := by
      apply (isLocallyFree_iff L).2
      refine ⟨U, fun i ↦ ⟨1, ?_⟩⟩
      exact ⟨(hU i).some ≪≫
        (biproductUniqueIso (fun _ : Fin 1 ↦
          Mod.regular (condensedRingObj Λ (U.X i)))).symm⟩
    exact boundedConstructible_singleFunctor_zero_obj _ _
      hfree.isConstructibleModuleObject
  · let A₁ := AffineSpace PUnit (Spec (.of k₀))
    have : PreservesFiniteColimits (upperStarFromPoint A₁) := by
      let : pointUpperStar.{u}.IsLeftAdjoint :=
        pointUpperStarLowerStarAdjunction.isLeftAdjoint
      unfold upperStarFromPoint
      infer_instance
    have : PreservesBinaryBiproducts (upperStarFromPoint A₁) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have : (upperStarFromPoint A₁).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    have hzero (R : Sheaf (Scheme.ProEt.topology A₁) Ab.{u + 1}) [MonObj R] :
        Mod.regularLift (Mod.regular R) 0 = 0 := by
      apply Mod.regular_hom_ext
      rw [Mod.one_comp_regularLift]
      simp
    have hz : condensedArtinSchreierProjector Λ k₀ ψ = 0 := by
      apply End.ext
      simp [condensedArtinSchreierProjector, Ring.inverse_non_unit _ hq, hzero]
    have hi : IsZero (condensedArtinSchreierSheaf Λ k₀ ψ) := by
      apply IsZero.of_mono_eq_zero (image.ι (condensedArtinSchreierProjector Λ k₀ ψ).asHom)
      apply (cancel_epi (factorThruImage (condensedArtinSchreierProjector Λ k₀ ψ).asHom)).mp
      simpa using congrArg End.asHom hz
    apply boundedConstructible_singleFunctor_zero_obj
    exact isConstructibleModuleObject_of_isZero _
      ((upperStar Λ
        (AffineSpace.homOfVector ((pullback π π') ↘ Spec (.of k₀)) fun _ ↦ b)).map_isZero hi)

end AlgebraicGeometry.ProEtale.CondensedRing
