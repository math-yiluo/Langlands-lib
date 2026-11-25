/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientPresentations
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing

/-! # Coefficient and section transport for the native adic realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The coefficient part of the native realization, before any derived functor is built.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-coefficient-system). -/
structure CoefficientSystem where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X

/-- The normalized coefficient presentations and exact section transport exist.

Source: Bhatt--Scholze, Lemma 6.8.2; native realization proof steps 1--2
(blueprint: lem-sf-locally-finite-adic-coefficient-system).

Proof in words: multiplication of native functions is pointwise and commutative.
An internal module has the same abelian sheaf with the action restricted to constants;
the inverse action is obtained by balancing the constant scalar action with the native
coefficient action. The unit and balancing axioms make these constructions inverse.
Compose this equivalence with the internal-to-section-module equivalence. It preserves
finite limits and colimits, and therefore is additive. For a finite coefficient field,
take the constant finite-quotient to continuous-function isomorphisms, fixing every
constant section. Taking their inverse limit gives the completed integral comparison;
its projections are the residue maps by construction. Localizing at the uniformizer
identifies the integral localization with continuous rational functions, and integral
inclusion is pointwise. Postcomposition with the specified embedding gives rational
inclusion into the native function sheaf. Its values are locally finite, since the
coefficient field is finite dimensional. Every normalization is pointwise. For E ≤ L,
compose with each finite residue projection to check compatibility of integral maps;
then use the inverse-limit universal property and equality of embedded rational
functions. The empty site object has its zero ring and satisfies the same formulas.
-/
theorem coefficientSystem_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (CoefficientSystem l X) := by
  let e := ProEtale.padicAlgClSheafIsoAdicConstantSheaf X l
  haveI : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (ProEtale.padicAlgClSheafToAdicConstantSheaf X l))
  letI : IsCommMonObj (abRing l X) := by
    constructor
    apply (cancel_epi (e.hom ⊗ₘ e.hom)).mp
    rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
      ← IsMonHom.mul_hom, ← Category.assoc, IsCommMonObj.mul_comm]
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  haveI : (sections l X).IsEquivalence := by
    unfold sections
    infer_instance
  haveI : PreservesFiniteLimits (sections l X) := inferInstance
  haveI : PreservesFiniteColimits (sections l X) := inferInstance
  haveI : (sections l X).Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨coefficient, scalar⟩ := coefficientPresentations_exists l X
  exact ⟨{ coefficient := coefficient, coefficient_scalar := scalar }⟩

end WeilConjectures.LocallyFiniteAdicRealization
