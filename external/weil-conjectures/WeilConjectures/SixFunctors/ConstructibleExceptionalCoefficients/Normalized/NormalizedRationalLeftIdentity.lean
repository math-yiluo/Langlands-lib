/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedIntegralScalarUnit
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.RationalScalarObjectTransport
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms
import WeilConjectures.SixFunctors.NormalizedRingCompactScalar.NormalizedRingCompactScalarCocycle

/-! # Identity law for normalized rational left coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic

universe u v w z
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem map_heq {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) {W X Y Z : A} (hW : W = Y) (hX : X = Z)
    {a : W ⟶ X} {b : Y ⟶ Z} (h : HEq a b) : HEq (G.map a) (G.map b) := by
  subst Y Z
  exact heq_of_eq (congrArg G.map (eq_of_heq h))

private theorem app_heq {A B : Type*} [Category A] [Category B]
    {G H : A ⥤ B} (η : G ⟶ H) {K M : A} (h : K = M) :
    HEq (η.app K) (η.app M) := by
  subst M
  rfl

private theorem comp_heq {A : Type*} [Category A]
    {W W' X X' Y Y' : A} (hW : W = W') (hX : X = X') (hY : Y = Y')
    {a : W ⟶ X} {a' : W' ⟶ X'} {b : X ⟶ Y} {b' : X' ⟶ Y'}
    (ha : HEq a a') (hb : HEq b b') : HEq (a ≫ b) (a' ≫ b') := by
  subst W' X' Y'
  cases ha
  cases hb
  rfl

private theorem ring_identity (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {s : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
    (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _)
    (A : Operation.{u, v} l Ω X Y (s.stage l))
    (r : LeftRealization.{u, v} l Ω c s A)
    (SX : Scalar.{u, v} l Ω (s := s) (t := s) a X)
    (SY : Scalar.{u, v} l Ω (s := s) (t := s) a Y)
    (q : @CounitComparison l _ Ω _ _ _ X Y (s.stage l) (s.stage l)
      A A SX.functor SY.functor SX.commShift SY.commShift)
    (hn : CounitQNormalized.{u, v} l Ω c a SX SY r r q)
    (uX : ScalarIdentity.{u, v} l Ω h X SX)
    (uY : ScalarIdentity.{u, v} l Ω h Y SY)
    (K : C.{u, v} l Ω X (s.stage l)) :
    (@CounitComparison.q l _ Ω _ _ _ X Y (s.stage l) (s.stage l)
      A A SX.functor SY.functor SX.commShift SY.commShift q).hom.app K ≫
        A.F.map (uX.iso.hom.app K) = uY.iso.hom.app (A.F.obj K) := by
  let : SX.functor.CommShift ℤ := SX.commShift
  let : SY.functor.CommShift ℤ := SY.commShift
  let B : NormalizedRingCompactScalar.Support.{u, v} l Ω c s := ⟨A.F, r⟩
  let BX : NormalizedRingCompactScalar.Scalar.{u, v} l Ω (s := s) (t := s) a X :=
    ⟨SX.functor, SX.realization⟩
  let BY : NormalizedRingCompactScalar.Scalar.{u, v} l Ω (s := s) (t := s) a Y :=
    ⟨SY.functor, SY.realization⟩
  have hq : NormalizedRingCompactScalar.Normalized.{u, v} l Ω c a B B BX BY q.q := by
    intro M
    exact hn M
  exact (NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle
    l Ω c D hl).identity a h B BX BY q.q hq
      ⟨uX.iso, fun M ↦ uX.normalized M⟩ ⟨uY.iso, fun M ↦ uY.normalized M⟩ K

/--
The normalized rational left comparison satisfies the scalar identity law.
Source: exceptional inverse-image coefficient construction, rationalization paragraph;
the rational-arrow localization argument, Steps 1--4
(blueprint: lem-sf-normalized-rational-left-laws).

The proof transports the integral identity equation through the specified rational
localization. The localized action formula identifies the localized integral unit arrow
with the displayed rational scalar unit, and localization preserves composition and
identities.
-/
theorem normalized_rational_left_identity (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) :
    ∀ (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.rational E)),
      (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app K ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0
            (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).F.obj K) := by
  intro c E K
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    sfCompactSupportScalarResidueUnit l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) X
  have htor := (integral_residue_tor D l hl E.carrier X).2
  let J : C.{u, v} l Ω X (.integral E) := ⟨K.obj.obj, htor ▸ K.obj.property⟩
  change (F.rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app
      ((rationalization.{u, v} l Ω E X).obj J) ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app
            ((rationalization.{u, v} l Ω E X).obj J)) = _
  let a : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.integral E).coefficients l) :=
    PurCompactSupport.completedChange l E.carrier E.carrier (AlgHom.id (Padic l) E.carrier)
  have h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _ :=
    PurCompactSupport.completedMap_identity l E.carrier
  let ha : Allowed l (s := .integral E) (t := .integral E) a :=
    Allowed.integral E E (AlgHom.id (Padic l) E.carrier)
  let SX := R.scalar (s := .integral E) (t := .integral E) a ha true
  let SY := R.scalar (s := .integral E) (t := .integral E) a ha false
  let : SX.functor.CommShift ℤ := SX.commShift
  let : SY.functor.CommShift ℤ := SY.commShift
  let uX := R.scalarIdentity (s := .integral E) a h ha true
  let uY := R.scalarIdentity (s := .integral E) a h ha false
  have hi := ring_identity l Ω D hl c (s := .integral E) a h (R.operation c (.integral E))
    (R.left c (.integral E)) SX SY
    (R.comparison c (s := .integral E) (t := .integral E) a ha)
    (R.comparison_normalized c (s := .integral E) (t := .integral E) a ha) uX uY J
  have hloc := congrArg (rationalization.{u, v} l Ω E Y).map hi
  rw [Functor.map_comp] at hloc
  have hx := normalized_integral_scalar_unit l Ω E X SX
    (R.integralScalar_eq E E (AlgHom.id (Padic l) E.carrier) true)
    (R.integralScalar_normalized E E (AlgHom.id (Padic l) E.carrier) true) h uX J
  have hy := normalized_integral_scalar_unit l Ω E Y SY
    (R.integralScalar_eq E E (AlgHom.id (Padic l) E.carrier) false)
    (R.integralScalar_normalized E E (AlgHom.id (Padic l) E.carrier) false) h uY
    ((R.operation c (.integral E)).F.obj J)
  have ho := (F.rationalAction c E).1
  have hSX := rational_scalar_object_transport l Ω E X SX.functor
    (R.integralScalar_eq E E (AlgHom.id (Padic l) E.carrier) true) J
  have hSY := rational_scalar_object_transport l Ω E Y SY.functor
    (R.integralScalar_eq E E (AlgHom.id (Padic l) E.carrier) false)
    ((R.operation c (.integral E)).F.obj J)
  have hmap := (map_heq (R.operation c (.rational E)).F hSX rfl hx.symm).trans
    ((F.rationalAction c E).2 _ _ (uX.iso.hom.app J))
  have hq := F.rational_normalized c E E (AlgHom.id (Padic l) E.carrier) J
  have hleft := comp_heq
    ((congrArg (rationalScalar l Ω E E (AlgHom.id (Padic l) E.carrier) Y).obj
      (ho J)).trans hSY)
    ((congrArg (R.operation c (.rational E)).F.obj hSX).trans (ho (SX.functor.obj J)))
    (ho J) hq hmap
  have hright := (app_heq
    (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom (ho J)).trans
    hy.symm
  exact eq_of_heq (hleft.trans ((heq_of_eq hloc).trans hright.symm))

end WeilConjectures.ConstructibleExceptionalCoefficients
