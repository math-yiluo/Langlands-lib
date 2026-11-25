/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedScalarAssociatorLocalizationTransport

/-! # Localization of a normalized completed scalar associator -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- A finite-Tor scalar associator with the prescribed ordinary realization localizes
to the intrinsic rational scalar associator.
Source: exceptional coefficient construction, scalar normalization paragraph; the
ordinary/completed comparison of Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12
(blueprint: lem-sf-normalized-scalar-associator-localization).

Proof: identify each supplied scalar functor with the restriction of the completed
scalar extension using faithfulness of the full inclusion and the three functor
equalities. The three inverse-realization normalizations identify the supplied sigma
maps with the quotient-completion comparisons. To compare the ordinary models, choose
flat-term K-flat resolutions. Both ordinary scalar functors compute change of rings
along the same completed coefficient map; their tensor sections and adjunction units
give the comparison. In these models both completion maps have the quotient tensor
maps as unshifted Roos coordinates and zero shifted coordinate. The uniqueness of
descent therefore identifies these comparisons with sfIntegralOrdinaryComparison.
The associator normalization, after cancelling the direct completion comparison,
now becomes exactly the conjugation formula specifying sfIntegralScalarComp: inverse
completion for the second map, ordinary extension of inverse completion for the first,
ordinary balanced associativity, and direct completion. The ordinary associators agree
because on a double pure tensor both send c tensor (b tensor x) to c*j(b) tensor x;
the tensor universal property and descent through resolutions prove equality.
The existing CompletedLineTensor.canonical_restriction also gives the identification
of this fixed completed associator with the intrinsic one. Faithfulness of the integral
inclusion identifies the restricted components. Finally
apply raw localization to this equality. The defining component specification of
sfRationalScalarComp identifies its component with this localized integral component.
The argument includes identity embeddings and repeated fields and never reflects
equality through localization. -/
theorem normalized_scalar_associator_localization
    (E L M : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (T : Scheme.{max u v})
    (A : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T)
    (B : Scalar.{u, v} l Ω (s := .integral L) (t := .integral M)
      (PurCompactSupport.completedChange l L.carrier M.carrier j) T)
    (D : Scalar.{u, v} l Ω (s := .integral E) (t := .integral M)
      (PurCompactSupport.completedChange l E.carrier M.carrier (j.comp i)) T)
    (hA : A.functor ⋙ (finiteTorConstructibleIntegral l L.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T)
    (hB : B.functor ⋙ (finiteTorConstructibleIntegral l M.carrier T).ι =
      (finiteTorConstructibleIntegral l L.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l L.carrier M.carrier j T)
    (hD : D.functor ⋙ (finiteTorConstructibleIntegral l M.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier M.carrier (j.comp i) T)
    (nA : ∀ K, HEq (A.realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i T).app K.obj))
    (nB : ∀ K, HEq (B.realization.inv.app K)
      ((completedScalarComparison l L.carrier M.carrier j T).app K.obj))
    (nD : ∀ K, HEq (D.realization.inv.app K)
      ((completedScalarComparison l E.carrier M.carrier (j.comp i) T).app K.obj))
    (α : ScalarComposition.{u, v} l Ω
      (PurCompactSupport.completedMap_composition l E.carrier L.carrier i M.carrier j)
      T A B D)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((sfRationalScalarComp l E.carrier L.carrier i T 0
      (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
        ((rationalization.{u, v} l Ω E T).obj K))
      ((rationalization.{u, v} l Ω M T).map (α.iso.hom.app K)) := by
  have hc := (sfRationalScalarComp_existsUnique l E.carrier L.carrier i T 0
      (Fact.out : l.Prime).ne_zero M.carrier j).exists.choose_spec
    ((rationalization.{u, v} l Ω E T).obj K)
  have ht := normalized_scalar_associator_localization_transport l Ω E L M i j T A B D
    hA hB hD nA nB nD α K
  exact hc.trans ht.symm

end WeilConjectures.ConstructibleExceptionalCoefficients
