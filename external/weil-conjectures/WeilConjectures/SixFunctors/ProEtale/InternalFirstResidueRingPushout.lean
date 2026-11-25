/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueRingIso
import WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueSheafPushout

/-! # The first-residue pushout of the actual coefficient rings -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

/-- The first constant and continuous quotient maps form a pushout of ring sheaves.

Source: blueprint integral-models proof (1)--(2), Stacks Tags 093M and 099L;
finite constant coefficient comparison, Stacks Tag 09C1.
(auxiliary; not a blueprint node).

Proof: put A = O_E and k = A/(pi). The quotient topology on k is discrete since
(pi) is open. Constant k-valued functions give a locally bijective map from the
constant ring presheaf to the continuous-function sheaf: cover a profinite object
by the finitely many clopen fibres of a function. On an empty object use the empty
cover for local injectivity. Sheafification therefore gives a ring isomorphism;
e is its inverse. Naturality of constant functions identifies the integral residue
square, including the transport by pointComparison between the two equal integral
topologies. Identify the continuous integral sheaf with the inverse limit of the
positive constant quotients, using the projection-normalized integral comparison.
The quotient of that completed ring by the image of (pi) is its first constant
quotient, by flat_and_quotients. Thus the constant-to-completed square with the
first quotient is a ring-sheaf pushout. Transport this square through section-ring
reconstruction and precomposition with AsSmall. Equivalences preserve its universal
property. The assertion includes the zero ring of sections on empty objects and
the empty scheme; it asserts no sectionwise surjectivity on the original site.
No module tensor functor, flatness assertion, or derived category is part of this
ring-level statement. -/
theorem internal_first_residue_ring_pushout
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    let a := IntegralModelsStacks.scalarMap l E X ≫
      coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
    ∃ e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
        Mon.mk (IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E 1)),
      IsPushout (IntegralModelsStacks.smallMap X a)
        (IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X))
        (IntegralModelsStacks.smallMap X
          (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X)) (𝟙 _) := by
  dsimp only
  let e := firstResidueIso l E
  refine ⟨e, internal_first_residue_sheaf_pushout l E X e ?_⟩
  have h := congrArg ((upperStarFromPoint X).map)
    (firstResidueIso_normalization l E)
  dsimp only [e, IntegralModelsStacks.scalarMap, IntegralModelsStacks.residueMap,
    coefficientMap, AdicCompletion.quotient]
  simpa only [Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry.ProEtale
