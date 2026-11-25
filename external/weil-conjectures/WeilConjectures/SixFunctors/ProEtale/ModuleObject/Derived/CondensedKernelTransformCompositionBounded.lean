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

/-! Bounded constructibility needed by condensed kernel-transform composition.

Source: boundedness clauses in the statement of `proposition-fourier-inversion`
(blueprint: proposition-fourier-inversion).

The statement isolates the three boundedness assertions used to lift the ambient
comparison: the convolution kernel is bounded constructible and both sides preserve
bounded constructible inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The convolution is bounded constructible and both kernel functors preserve
bounded constructible objects.

Source: latest blueprint `lem-fd-kernel-composition.md`, the bounded kernel hypotheses
and the convolution membership assertion (blueprint: lem-fd-kernel-composition-bounded).

Proof in words: pull both kernels to T. Pullback preserves constructibility and boundedness;
the coefficient-family finite-Tor comparison makes their derived tensor bounded
constructible. Compact-support direct image along r13 gives the first assertion.
For either transform, apply the same pullback and tensor preservation to an arbitrary
bounded constructible input and the fixed kernel, then compact-support preservation
along the second projection. Integer shifts preserve the bounded constructible
predicate. The two preservation statements are independent of the comparison of the
functors; empty schemes and zero kernels are included by preservation of zero. -/
theorem condensedKernelTransform_comp_bounded
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
    {S V V' V'' : Scheme.{u}} [S.Over (Spec (.of k))]
    [V.Over (Spec (.of k))] [V'.Over (Spec (.of k))]
    [V''.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (V' ↘ Spec (.of k))]
    [QuasiCompact (V' ↘ Spec (.of k))] [IsSeparated (V' ↘ Spec (.of k))]
    [LocallyOfFiniteType (V'' ↘ Spec (.of k))]
    [QuasiCompact (V'' ↘ Spec (.of k))] [IsSeparated (V'' ↘ Spec (.of k))]
    (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)
    (c₁₂ : Compactification (pullback.snd π π'))
    (c₂₃ : Compactification (pullback.snd π' π''))
    (c₁₃ : Compactification (pullback.snd π π''))
    (c₁₃conv : Compactification (pullback.tripleProj₁₃ π π' π''))
    (𝒦 : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback π π'))
      Ab.{u + 1}) (condensedRingObj Λ (pullback π π'))))
    (𝒦' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback π' π''))
      Ab.{u + 1}) (condensedRingObj Λ (pullback π' π''))))
    (h𝒦 : boundedConstructible (condensedRingObj Λ (pullback π π')) 𝒦)
    (h𝒦' : boundedConstructible (condensedRingObj Λ (pullback π' π'')) 𝒦')
    (a b : ℤ) :
    boundedConstructible (condensedRingObj Λ (pullback π π''))
      ((rightDerivedLowerShriekOfCompactification Λ c₁₃conv).obj
        ((tensorRight ((upperStar Λ
          (pullback.snd (pullback.snd π π') (pullback.fst π' π''))).leftDerivedFunctor.obj
            𝒦')).obj
          ((upperStar Λ
            (pullback.fst (pullback.snd π π') (pullback.fst π' π''))).leftDerivedFunctor.obj
            𝒦))) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ V) K →
      boundedConstructible (condensedRingObj Λ V')
        (((upperStar Λ (pullback.fst π π')).leftDerivedFunctor ⋙ tensorRight 𝒦 ⋙
          rightDerivedLowerShriekOfCompactification Λ c₁₂ ⋙ shiftFunctor _ a).obj K)) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ V') K →
      boundedConstructible (condensedRingObj Λ V'')
        (((upperStar Λ (pullback.fst π' π'')).leftDerivedFunctor ⋙ tensorRight 𝒦' ⋙
          rightDerivedLowerShriekOfCompactification Λ c₂₃ ⋙ shiftFunctor _ b).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
