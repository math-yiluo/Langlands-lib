/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedRationalLeftComposition
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedRationalLeftIdentity

/-! # Normalized coefficient comparisons: one component of the coherence argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u v w z
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Localization transports the normalized integral left coefficient laws.
Source: exceptional inverse-image coefficient construction, rationalization paragraph;
the rational-arrow localization argument, Steps 1--4
(blueprint: lem-sf-normalized-rational-left-laws).

Proof: identify the restricted completed scalar functors through their full inclusions.
The normalization of their realizations identifies the supplied scalar associators and
unitors with the intrinsic completed associators and unitors. Apply the normalized ring
compact-support scalar cocycle to the completed coefficient changes. Every intrinsic
integral constructible object has uniform residue Tor amplitude because l is invertible
on the geometric finite-field base. Thus its unchanged representative belongs to the
recorded finite-Tor category. Use the raw-localization argument of
rational_left_coefficient_localization on the integral functor on these representatives.
Only its singleton integral-arrow case is needed for the localized associator and unitor;
localizedAction supplies this directly. The component normalization identifies q with
the localized integral q. Localization preserves composition and identity, yielding the
two displayed LEFT laws. This argument includes identities and repeated fields and uses
no reflection of equality by localization. -/
theorem normalized_rational_left_laws (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) :
    (∀ (c : Compactification f) (E L M : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
      (K : C.{u, v} l Ω X (.rational E)),
      (rationalScalar.{u, v} l Ω L M j Y).map
          ((F.rationalComparison c E L i).q.hom.app K) ≫
        (F.rationalComparison c L M j).q.hom.app
          ((rationalScalar.{u, v} l Ω E L i X).obj K) ≫
        (R.operation c (.rational M)).F.map
          ((sfRationalScalarComp l E.carrier L.carrier i X 0
            (Fact.out : l.Prime).ne_zero M.carrier j).hom.app K) =
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          ((R.operation c (.rational E)).F.obj K) ≫
        (F.rationalComparison c E M (j.comp i)).q.hom.app K) ∧
    (∀ (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.rational E)),
      (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app K ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0
            (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).F.obj K)) := by
  constructor
  · exact normalized_rational_left_composition l Ω D hl R F
  · exact normalized_rational_left_identity l Ω D hl R F

end WeilConjectures.ConstructibleExceptionalCoefficients
