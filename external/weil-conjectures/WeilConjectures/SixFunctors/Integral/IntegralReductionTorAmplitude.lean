/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.SixFunctors.Integral.IntegralReductionResidueHomology
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResidueTorTestGeneral

/-!
# Residue support controls the Tor amplitude of every finite reduction

For an arbitrary object `K` of the derived category of the completed coefficient ring,
cohomological support of the residue reduction in `[a,b]` gives Tor amplitude `[a,b]` of
every finite reduction. No constructibility or completeness of `K` is needed.

Source: Weil conjectures blueprint, `lemma-bounds-finite-reductions--2` (blueprint:
lemma-bounds-finite-reductions--2).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- If the cohomological support of the residue reduction of `K` lies in `[a,b]`, then every
finite reduction of `K` has Tor amplitude in `[a,b]`. The index `n` denotes exponent `n+1`.

Source: Weil conjectures blueprint, `lemma-bounds-finite-reductions--2`
(blueprint: lemma-bounds-finite-reductions--2).

Proof: represent the finite reduction by a cochain complex with a K-flat resolution. The
coefficient comparison `integralReduction_residue_homology_zero_iff` identifies its residue
derived tensor cohomology with the cohomology of the residue reduction of `K`, which vanishes
outside `[a,b]`. The pro-etale residue Tor test gives amplitude `[a,b]`. -/
theorem scalarReductionDerivedExtension_torAmplitude_of_residue_support
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (a b : ℤ) (hab : a ≤ b)
    (hres : ∀ i : ℤ, i ∈ proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) → a ≤ i ∧ i ≤ b)
    (n : ℕ) :
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let : HasDerivedCategory C := scalarReductionTargetDerived l E X n
  have := Localization.essSurj (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)
  let e : DerivedCategory.Q.obj L ≅ (scalarReductionDerivedExtension.{u, u} l E X n).obj K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso _
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := R) L
  have ht := (proEtale_torAmplitude_iff_residue_tensor' l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) X L P f hf hP a b hab).2
  have htor : HasProEtaleTorAmplitude X A (DerivedCategory.Q.obj L) a b := by
    apply ht
    intro i hi
    apply (integralReduction_residue_homology_zero_iff l E X K n L P e f hf hP i).2
    by_contra hz
    have hb := hres i hz
    omega
  refine ⟨htor.1, ?_⟩
  intro L' P' hL' f' hf' hP' M i hi
  obtain ⟨e'⟩ := hL'
  exact htor.2 L' P' ⟨e' ≪≫ e.symm⟩ f' hf' hP' M i hi

end WeilConjectures
