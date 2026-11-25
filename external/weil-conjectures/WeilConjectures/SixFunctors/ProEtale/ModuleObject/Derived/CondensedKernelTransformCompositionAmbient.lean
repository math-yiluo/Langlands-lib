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

/-! Ambient comparison required by condensed kernel-transform composition.

This is the compact-support base-change, projection-formula, tensor-coherence and
compact-support-composition calculation on the triple fibre product.
Source: the ambient comparison paragraph of `proposition-fourier-inversion`
(blueprint: proposition-fourier-inversion).

The remaining proof is the full six-functor coherence calculation described by the
source paragraph; it is split from the bounded restriction and Fourier specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Comparison of the two kernel functors after restricting their input to bounded
constructible complexes, with bounded constructible kernels.

Source: latest blueprint `lem-fd-kernel-composition.proof.md`, first two paragraphs
(blueprint: lem-fd-kernel-composition-ambient).

Proof in words: write T = X12 ×_{V'} X23 and use compact-support base change for
q1^* Rp2,! to replace it by Rr23,! r12^*. Pull r12^* through tensor using its strong
monoidal structure. Apply the projection formula for r23 to move K' inside this
compact-support image. Apply compact-support composition to q2 r23. On the other
side, apply the projection formula for r13 to the convolution and the input pullback.
Use r12 p1 = r13 s1 and the pullback compositor. Tensor associativity and symmetry
identify both resulting integrands, and compact-support composition identifies both
pushforwards. Every comparison is natural in the input. Finally commute the first
shift through the second transform and combine the two shifts by shiftFunctorAdd.
The comparison is restricted from the start, so no comparison on arbitrary unbounded
input objects is asserted. -/
theorem condensedKernelTransform_comp_ambient
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
    {S V V' V'' : Scheme.{u}}
    [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [V'.Over (Spec (.of k))] [V''.Over (Spec (.of k))]
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
    Nonempty (
      (boundedConstructible (condensedRingObj Λ V)).ι ⋙
      (((upperStar Λ (pullback.fst π π')).leftDerivedFunctor ⋙ tensorRight 𝒦 ⋙
        rightDerivedLowerShriekOfCompactification Λ c₁₂ ⋙ shiftFunctor _ a) ⋙
      ((upperStar Λ (pullback.fst π' π'')).leftDerivedFunctor ⋙ tensorRight 𝒦' ⋙
        rightDerivedLowerShriekOfCompactification Λ c₂₃ ⋙ shiftFunctor _ b)) ≅
      (boundedConstructible (condensedRingObj Λ V)).ι ⋙
      (upperStar Λ (pullback.fst π π'')).leftDerivedFunctor ⋙
        tensorRight ((rightDerivedLowerShriekOfCompactification Λ c₁₃conv).obj
          ((tensorRight ((upperStar Λ
            (pullback.snd (pullback.snd π π') (pullback.fst π' π''))).leftDerivedFunctor.obj
              𝒦')).obj
            ((upperStar Λ
              (pullback.fst (pullback.snd π π') (pullback.fst π' π''))).leftDerivedFunctor.obj
              𝒦))) ⋙
        rightDerivedLowerShriekOfCompactification Λ c₁₃ ⋙ shiftFunctor _ (a + b)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
