/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctorData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicFunctorDescentHom
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicFunctorDescentImage

/-! # LocallyFiniteAdicFunctorDescent

Source: Bhatt--Scholze, Section 6.8; native realization proof
(blueprint: lem-sf-locally-finite-adic-functor-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
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

/-- Object and derived-Hom descent for an already constructed normalized functor.
This statement constructs no functor, coefficient map, scalar comparison, or small model.

Source: Bhatt--Scholze, Proposition 6.8.14(1),(2), using the existing condensed
filtered two-colimit; steps 3, 6 and 7 of the native realization proof
(blueprint: lem-sf-locally-finite-adic-functor-descent).

Proof in words: identify the native coefficient with the finite-field-valued condensed
coefficient by sheafification. Internal-module and section-module equivalences preserve
the underlying sheaves and exact sequences, hence all derived Homs. On each Noetherian
stratum the finite-field and algebraic-closure local-freeness theorems identify finite
presentation with the native finite-free constructible models. Globalize the local
stratifications using a finite open subcover: replace U_i by U_i minus the preceding
opens and restrict each given stratification to that locally closed piece. Boundedness
is unchanged. The integral comparison of D, localization, and its common_field equation
identify its restriction to every finite stage with the finite-field realization
followed by native scalar extension, naturally on all fractional arrows. The finite
realizations give bijections on all derived Homs. Their transition maps agree by the
normalization, so the source Hom colimit is the Hom colimit of the condensed system.
The Hom-surjectivity and eventual-injectivity clauses of
constructibleCocone_isFilteredTwoColimit identify this colimit with the ambient native
derived Hom. This proves both injectivity and surjectivity of D.J.map. For the image,
every source object comes from a finite stage and its image has bounded constructible
cohomology because finite realization and scalar extension preserve that property.
Conversely, transport a native bounded constructible object to the condensed category,
descend it by the object clause of the two-colimit theorem, and lift its finite model
through the finite-field realization equivalence and the raw coefficient comparison.
Tensor transitivity and the integral comparison give an isomorphism of its D.J-image
with the original object. This proves the reverse implication. Using shifted targets
in the same Hom argument proves the assertion in every derived degree. Empty schemes
and zero complexes are included in the finite-stage comparisons and descent.
-/
theorem normalizedFunctor_descent
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    (∀ K L, Function.Bijective (D.J.map : (K ⟶ L) → (D.J.obj K ⟶ D.J.obj L))) ∧
      (∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
        ∃ A, Nonempty (D.J.obj A ≅ K)) := by
  exact ⟨normalizedFunctor_descent_hom l X D,
    normalizedFunctor_descent_image l X D⟩

end WeilConjectures.LocallyFiniteAdicRealization
