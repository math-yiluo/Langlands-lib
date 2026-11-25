/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctorData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralTensorConstructible
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.CondensedFiniteIntegralTensorModel
import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingConstructible
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting

/-! # Essential image descent for a normalized locally finite adic functor

Source: Bhatt--Scholze, Proposition 6.8.14(1),(2), using the existing condensed
filtered two-colimit; native realization proof steps 3 and 7.
(blueprint: lem-sf-locally-finite-adic-functor-descent-image)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

/-- Bounded adic constructibility is exactly the essential image of the normalized functor.

Proof in words: identify bounded native constructible objects with the condensed module
category using the internal-module and section-module equivalences and the finite-field
local-freeness theorems. The object clause of
`constructibleCocone_isFilteredTwoColimit` descends a condensed object to a finite field.
Essential surjectivity of the finite-field realization lifts that model to a source object,
and tensor transitivity identifies its normalized image with the original object. In the
other direction, finite realization and scalar extension preserve bounded constructibility.
The argument includes the zero object and empty strata.
(blueprint: lem-sf-locally-finite-adic-functor-descent-image)
-/
theorem normalizedFunctor_descent_image
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
      ∃ A, Nonempty (D.J.obj A ≅ K) := by
  letI := D.commutative
  letI := D.sectionsAdditive
  letI := D.sectionsLimits
  letI := D.sectionsColimits
  letI : (ProEtale.AdicSheaf.forgetAb l X).IsEquivalence :=
    ProEtale.nativeScalarForgetting_isEquivalence l X
  haveI : (sections l X).IsEquivalence := by
    unfold sections
    infer_instance
  let S := (sections l X).mapDerivedCategory
  let F := ProEtale.NativeEncoding.derivedEncoding l X
  intro K
  constructor
  · intro hK
    have hc := ProEtale.NativeEncoding.encoding_boundedConstructible l X K hK
    obtain ⟨E, M, ⟨e⟩⟩ := ProEtale.constructibleCocone_essSurjObj X l ⟨F.obj K, hc⟩
    have em : (ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj M.obj ≅ F.obj K :=
      (ObjectProperty.ι (ProEtale.boundedConstructible
        (ProEtale.padicAlgClRingObj X l))).mapIso e
    obtain ⟨L, ⟨eL⟩⟩ := condensedFinite_integralTensor_model l X E (D.coefficient E) M
    have ex : F.inv.obj
        ((ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj M.obj) ≅ K :=
      F.inv.mapIso em ≪≫ (F.asEquivalence.unitIso.app K).symm
    refine ⟨(GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L),
      ⟨S.preimageIso ((D.integral E).app L ≪≫ eL ≪≫ S.mapIso ex)⟩⟩
  · rintro ⟨⟨E, ⟨L⟩⟩, ⟨e⟩⟩
    exact nativeIntegralTensor_constructible l X E (D.coefficient E) L K
      (S.mapIso e.symm ≪≫ (D.integral E).app L)

end WeilConjectures.LocallyFiniteAdicRealization
