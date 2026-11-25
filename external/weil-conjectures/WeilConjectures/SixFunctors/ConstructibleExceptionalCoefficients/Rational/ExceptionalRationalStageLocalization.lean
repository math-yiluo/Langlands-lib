/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.RingStageAssembly.ExceptionalRingStageAssemblyData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ExceptionalScalarMateLocalization
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # Raw rational localization of the supplied integral stages

This is the localization part of field-stage completion. It constructs no closed operation.
The scalar comparisons are normalized against the supplied ring-stage comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftAdditive Operation.rightAdditive
  Operation.leftShift Operation.rightShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Rational operations and scalar mates obtained before common-field descent.
There are no closed operations or common-field comparisons in this record.
Source: Zheng, Construction 6.2, and the raw-localization part of coefficient step 5
(blueprint: lem-sf-rational-stage-localization). -/
structure RationalStageAssembly (A : RingStageAssembly.{u, v} l Ω D hl (f := f)) where
  operation (c : Compactification f) (E : FieldStage.{max u v} l) :
    Operation.{u, v} l Ω X Y (.rational E)
  left (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c E).F ≅
      sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
        c E.carrier
  localization (c : Compactification f) (E : FieldStage.{max u v} l) :
    CounitFieldComparison.{u, v} l Ω (A.operation c (.integral E)) (operation c E)
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  localization_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (localization c E).q.hom.app K ≫
        (left c E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((A.integralLeft c E).hom.app K)
  scalar (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    CounitFieldComparison.{u, v} l Ω (operation c E) (operation c L)
      (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y)
  scalar_normalized (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((scalar c E L i).q.hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω L Y).map
        ((Scalar.counitQ.{u, v} l Ω
          (A.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (A.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (A.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))
  action (c : Compactification f) (E : FieldStage.{max u v} l) :
    localizedAction (A.operation c (.integral E)).F (operation c E).F
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  shiftX (c d : Compactification f) (E : FieldStage.{max u v} l) :
    (localization c E).shiftX = (localization d E).shiftX
  shiftY (c d : Compactification f) (E : FieldStage.{max u v} l) :
    (localization c E).shiftY = (localization d E).shiftY
  identity (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((localization c E).q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω E Y).obj ((A.operation c (.integral E)).F.obj K)))

/-- Insert rational data into the completed ring record, for any later closed operations.
This only rearranges existing fields and makes no choice of functors or morphisms.
Source: coefficient construction step 5
(blueprint: lem-sf-rational-stage-localization). -/
def RationalStageAssembly.fields
    {A : RingStageAssembly.{u, v} l Ω D hl (f := f)}
    (P : RationalStageAssembly.{u, v} l Ω D hl A)
    (closed : ∀ _c : Compactification f, Operation.{u, v} l Ω X Y .closed) :
    CoefficientConstructionFields.{u, v} l Ω D hl
      (A.complete l Ω D hl P.operation closed P.left) where
  rationalizationComparison := P.localization
  rationalization_normalized := P.localization_normalized
  rationalComparison := P.scalar
  rational_normalized := P.scalar_normalized
  rationalAction := P.action

private def rawLeftRealization
    (c : Compactification f) (E : FieldStage.{max u v} l)
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (e : F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) :
    rawRationalFunctor l Ω E X Y F hX ≅
      sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
        c E.carrier := by
  letI : (rawRationalFunctor l Ω E X Y F hX).Additive :=
    ⟨by intros; exact map_add _ _ _⟩
  letI : (sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier).Additive :=
    ⟨by intros; exact map_add _ _ _⟩
  refine NatIso.ofComponents
    (fun K ↦ (sfRationalConstructibleLocalization l E.carrier Y).mapIso
      (e.app ((integralRepresentative l Ω E X hX).obj K.obj))) ?_
  intro K L h
  induction h using TensorProduct.inductionOn with
  | tmul a h =>
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ _)
        (((fullIntegralFunctor l Ω E X Y F hX).mapLinearMap
          (Padic.coefficientExtensionIntegers l E.carrier)).baseChange
            (Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) (a ⊗ₜ h)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (sfCompactSupportFiniteHomMap l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
          c E.carrier K L (a ⊗ₜ h)) (1 ⊗ₜ _)
    dsimp only [sfCompactSupportFiniteHomMap]
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ _) (a ⊗ₜ (fullIntegralFunctor l Ω E X Y F hX).map h) =
      ScalarLocalization.composition _ _ _ _ _ _
        (a ⊗ₜ (sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier).map h) (1 ⊗ₜ _)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one]
    exact congrArg (a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier] ·)
      (e.hom.naturality ((integralRepresentative l Ω E X hX).map h))
  | add h g hh hg =>
    change (rawRationalFunctor l Ω E X Y F hX).map (h + g) ≫ _ =
      _ ≫ (sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier).map (h + g)
    rw [Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hh, hg]

private theorem rawLeftRealization_normalized
    (c : Compactification f) (E : FieldStage.{max u v} l)
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (e : F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier)
    (K : C.{u, v} l Ω X (.integral E)) :
    (rawLeftRealization l Ω D hl c E F hX e).hom.app
        ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map (e.hom.app K) := rfl

/-- Localize the supplied linear integral adjunctions, with their actual raw object and
arrow action. This statement has no common-field or algebraically closed output.
Source: Zheng, Construction 6.2; coefficient construction step 5, localization part;
`lem-sf-field-stage-completion`, steps 1--3
(blueprint: lem-sf-rational-stage-localization).

Proof: map the prime unit from the finite base field to each residue field and apply
integral_residue_tor. For each supplied integral operation construct the rational left
and right functors explicitly by base change of their integral Hom maps; localize the
adjunction and its exact structures with exists_integral_adjunction_raw_localization.
The endpoint localization shifts are fixed without reference to compactification.
Construct the left realization componentwise as Q(A.integralLeft). On pure tensors,
naturality is the tensor of integral naturality, and tensor induction proves naturality
on every arrow. Since localization q is identity, its normalized equation is precisely
this component formula. Localize each supplied integral scalar mate by
exists_integral_scalar_mate_localization, using the actual ambient scalar equalities.
The component formula gives scalar_normalized. Finally, the raw functor has the old
localized object and sends 1 tensor h to 1 tensor F(h), which proves localizedAction.
No common-field descent, scalar coherence, or closed operation enters this argument. -/
theorem exists_rational_stage_localization
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (_leftLinear : ∀ (c : Compactification f) (E : FieldStage.{max u v} l),
      (A.operation c (.integral E)).F.Linear (Padic.coefficientExtensionIntegers l E.carrier))
    (_rightLinear : ∀ (c : Compactification f) (E : FieldStage.{max u v} l),
      (A.operation c (.integral E)).G.Linear (Padic.coefficientExtensionIntegers l E.carrier)) :
    Nonempty (RationalStageAssembly.{u, v} l Ω D hl A) := by
  classical
  let leftAdditive (c : Compactification f) (E : FieldStage.{max u v} l) :
      (A.operation c (.integral E)).F.Additive := (A.operation c (.integral E)).leftAdditive
  let rightAdditive (c : Compactification f) (E : FieldStage.{max u v} l) :
      (A.operation c (.integral E)).G.Additive := (A.operation c (.integral E)).rightAdditive
  let leftLinear (c : Compactification f) (E : FieldStage.{max u v} l) := _leftLinear c E
  let rightLinear (c : Compactification f) (E : FieldStage.{max u v} l) := _rightLinear c E
  have tor (T : Scheme.{max u v}) [T.Over (Spec (.of D.k))]
      (E : FieldStage.{max u v} l) :
      sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T := by
    have primeUnit : IsUnit (l : Γ(T, ⊤)) := by
      let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (T ↘ Spec (.of D.k)).appTop
      simpa only [map_natCast] using (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom
    let residueInvertible (t : T) : Invertible (l : T.residueField t) :=
      (show IsUnit (l : T.residueField t) from by
        simpa only [map_natCast] using
          ((primeUnit.map (T.presheaf.germ ⊤ t trivial).hom).map (T.residue t).hom)).invertible
    exact (integral_residue_tor D l hl E.carrier T).2
  have localize (c : Compactification f) (E : FieldStage.{max u v} l) :=
    exists_integral_adjunction_raw_localization l Ω E (A.operation c (.integral E))
      (tor X E) (tor Y E)
  choose R q hq hb hsX hsY using localize
  have scalars (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :=
    exists_integral_scalar_mate_localization l Ω E L i
      (A.operation c (.integral E)) (A.operation c (.integral L))
      (R c E) (R c L) (q c E) (q c L) (hq c E) (hb c E) (hq c L) (hb c L)
      (hsX c E) (hsY c E) (hsX c L) (hsY c L)
      (A.scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) true)
      (A.scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) false)
      (A.integralScalar_eq E L i true) (A.integralScalar_eq E L i false)
      (A.comparison c (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i))
  choose scalar hscalar hscalarShiftX hscalarShiftY using scalars
  refine ⟨{
    operation := fun c E ↦ (R c E).operation l Ω E
    left := fun c E ↦ rawLeftRealization l Ω D hl c E
      (A.operation c (.integral E)).F (tor X E) (A.integralLeft c E)
    localization := q
    localization_normalized := ?_
    scalar := scalar
    scalar_normalized := hscalar
    action := ?_
    shiftX := fun c d E ↦ (hsX c E).trans (hsX d E).symm
    shiftY := fun c d E ↦ (hsY c E).trans (hsY d E).symm
    identity := hq }⟩
  · intro c E K
    let e := rawLeftRealization l Ω D hl c E
      (A.operation c (.integral E)).F (tor X E) (A.integralLeft c E)
    have hcomp :=
      congrArg (fun z ↦ z ≫ e.hom.app ((rationalization.{u, v} l Ω E X).obj K))
        (eq_of_heq (hq c E K))
    exact hcomp.trans ((Category.id_comp _).trans
      (rawLeftRealization_normalized l Ω D hl c E
        (A.operation c (.integral E)).F (tor X E) (A.integralLeft c E) K))
  · intro c E
    constructor
    · intro K
      rfl
    · intro K L h
      apply heq_of_eq
      change ((fullIntegralFunctor l Ω E X Y (A.operation c (.integral E)).F
          (tor X E)).mapLinearMap (Padic.coefficientExtensionIntegers l E.carrier)).baseChange
            (Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier))
              (1 ⊗ₜ _) = 1 ⊗ₜ _
      change (1 : Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier))
          ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier]
            (fullIntegralFunctor l Ω E X Y (A.operation c (.integral E)).F (tor X E)).map
              ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).map h) = _
      rfl

end WeilConjectures.ConstructibleExceptionalCoefficients
