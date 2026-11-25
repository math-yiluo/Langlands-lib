/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.Integral.IntegralReductionResidueHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResidueTorTest
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-!
# Residue reduction controls integral Tor amplitude

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`lemma-bounds-finite-reductions--2`, order 2133 (blueprint: lemma-bounds-finite-reductions--2).

The finite reduction API uses index `n` for exponent `n+1`. In particular index `0`
is the residue reduction. Equality of the object predicates states equality of the
corresponding full subcategories of the same completed integral derived category.
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

private noncomputable def residueTestDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{u} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ULift.{u} (ZMod p)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod p)) }

/-- Bounds on residue cohomology give the same Tor interval at every finite level,
and the integral constructible and integral finite-Tor full subcategories coincide.
This does not identify constructibility with site-perfectness.

Source: blueprint order 2133 (blueprint: lemma-bounds-finite-reductions--2).
Proof:
1. Represent each finite reduction by a cochain complex and choose a K-flat resolution.
Transport its constructibility along the representative isomorphism. The coefficient
comparison `integralReduction_residue_homology_zero_iff` identifies its residue cohomology with
that of the first reduction. The support hypothesis makes it zero outside [a,b].
The pro-etale residue Tor test gives amplitude [a,b]; transport it to the reduction.
2. The common cohomology interval in the definition of integral constructibility gives
one interval for every reduction, exactly the integral finite-Tor condition.
3. The reverse inclusion is definitional, and extensionality gives equality of predicates.
-/
theorem integral_residue_tor
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      sfIntegralConstructible l E X K →
      ∀ a b : ℤ, a ≤ b →
        (∀ i : ℤ,
          i ∈ proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) → a ≤ i ∧ i ≤ b) →
        ∀ n : ℕ,
          HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b) ∧
      sfIntegralConstructible l E X =
        finiteTorConstructibleIntegral l E X := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  have finiteLevel
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
      (hK : sfIntegralConstructible l E X K)
      (a b : ℤ) (hab : a ≤ b)
      (hres : ∀ i : ℤ, i ∈ proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) → a ≤ i ∧ i ≤ b)
      (n : ℕ) :
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b := by
    obtain ⟨_, r, s, hrs, hlevels⟩ := hK
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := proEtaleConstantRing X A
    let C := proEtaleRingModules X R
    have := Localization.essSurj (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (.up ℤ))
    let L := (DerivedCategory.Q (C := C)).objPreimage
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)
    let e := (DerivedCategory.Q (C := C)).objObjPreimageIso
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (R := R) L
    have hcon : intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X (DerivedCategory.Q.obj L) := by
      let := Padic.finite_coefficientExtensionRing l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
      have hclosed := (proEtale_bounded_constructible_isTriangulated X A).1
      let W : ObjectProperty (proEtaleDerivedCategory X A) :=
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X
      have : W.IsClosedUnderIsomorphisms := hclosed
      exact W.prop_of_iso e.symm (hlevels n).1
    have ht := (proEtale_torAmplitude_iff_residue_tensor (residueTestDatum.{u} D.p D.prime) l _hl
      E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X L P f hf hP hcon a b hab).2
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
  refine ⟨finiteLevel, ?_⟩
  funext K
  apply propext
  constructor
  · intro hK
    refine ⟨hK, ?_⟩
    have hK0 := hK
    obtain ⟨_, a, b, hab, hlevels⟩ := hK0
    exact ⟨a, b, hab, fun n ↦ finiteLevel K hK a b hab
      (fun i hi ↦ (hlevels 0).2 hi) n⟩
  · exact fun hK ↦ hK.1

end WeilConjectures
