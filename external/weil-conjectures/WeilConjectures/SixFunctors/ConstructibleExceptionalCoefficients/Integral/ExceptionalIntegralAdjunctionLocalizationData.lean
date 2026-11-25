/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData

/-! # Literal tensor data for integral adjunction localization

Source: Zheng, Constructions 6.1 and 6.2. The data fix the tensor object and arrow maps
before an adjunction and compatible exact structures are localized onto those functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (E : FieldStage.{max u v} l) (X Y : Scheme.{max u v})

/-- Change only the membership proof of an integral representative.
Source: the full-subcategory step of Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def integralRepresentative
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    sfIntegralConstructibleCategory l E.carrier X ⥤ C.{u, v} l Ω X (.integral E) where
  obj K := ⟨K.obj, h ▸ K.property⟩
  map f := ObjectProperty.homMk f.hom

/-- Extend the domain of an integral functor by the literal full inclusions.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def fullIntegralFunctor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    sfIntegralConstructibleCategory l E.carrier X ⥤ sfIntegralConstructibleCategory l E.carrier Y :=
  integralRepresentative l Ω E X h ⋙ F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y

/-- The proof-changing representative functor is additive.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralRepresentativeAdditive (h) :
    (integralRepresentative l Ω E X h).Additive where
  map_add := by intros; rfl

/-- The proof-changing representative functor is integral-linear.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralRepresentativeLinear (h) :
    (integralRepresentative l Ω E X h).Linear (Padic.coefficientExtensionIntegers l E.carrier) where
  map_smul := by intros; rfl

/-- The literal full integral inclusion is additive.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralInclusionAdditive (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{w} l) (X : Scheme.{w}) :
    (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).Additive where
  map_add := by intros; rfl

/-- The literal full integral inclusion is integral-linear.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralInclusionLinear (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{w} l) (X : Scheme.{w}) :
    (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).Linear
      (Padic.coefficientExtensionIntegers l E.carrier) where
  map_smul := by intros; rfl

/-- The full-domain functor is additive, since both inclusions are literal.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance fullIntegralFunctorAdditive
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] (h) : (fullIntegralFunctor l Ω E X Y F h).Additive := by
  dsimp only [fullIntegralFunctor]
  infer_instance

/-- The full-domain functor preserves integral scalar multiplication.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance fullIntegralFunctorLinear
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)] (h) :
    (fullIntegralFunctor l Ω E X Y F h).Linear
      (Padic.coefficientExtensionIntegers l E.carrier) := by
  dsimp only [fullIntegralFunctor]
  infer_instance

/-- Tensor extension of a linear functor preserves identities and composition.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
theorem rawTensorFunctorLaws
    {R : Type*} [CommRing R] {B C : Type*} [Category B] [Category C]
    [Preadditive B] [Preadditive C] [Linear R B] [Linear R C]
    (p : R) (F : B ⥤ C) [F.Additive] [F.Linear R] :
    (∀ K : B, (F.mapLinearMap R).baseChange (Localization.Away p)
      (1 ⊗ₜ[R] 𝟙 K) = 1 ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : B) (a : Localization.Away p ⊗[R] (K ⟶ L))
        (b : Localization.Away p ⊗[R] (L ⟶ M)),
      (F.mapLinearMap R).baseChange (Localization.Away p)
        (ScalarLocalization.composition R B p K L M b a) =
      ScalarLocalization.composition R C p (F.obj K) (F.obj L) (F.obj M)
        ((F.mapLinearMap R).baseChange (Localization.Away p) b)
        ((F.mapLinearMap R).baseChange (Localization.Away p) a)) := by
  constructor
  · intro K
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 K) = _
    rw [F.map_id]
  · intro K L M a b
    induction b using TensorProduct.inductionOn with
    | tmul b g =>
      induction a using TensorProduct.inductionOn with
      | tmul a h =>
        rw [ScalarLocalization.composition_tmul]
        change (b * a) ⊗ₜ[R] F.map (h ≫ g) =
          ScalarLocalization.composition R C p (F.obj K) (F.obj L) (F.obj M)
            (b ⊗ₜ[R] F.map g) (a ⊗ₜ[R] F.map h)
        rw [ScalarLocalization.composition_tmul, F.map_comp]
      | add a a' ha ha' => simp [map_add, ha, ha']
    | add b b' hb hb' => simp [map_add, hb, hb']

/-- The rational functor sends each tensor to the tensor of the integral image.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def rawRationalFunctor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    C.{u, v} l Ω X (.rational E) ⥤ C.{u, v} l Ω Y (.rational E) := by
  let H := fullIntegralFunctor l Ω E X Y F h
  have : H.Additive := fullIntegralFunctorAdditive l Ω E X Y F h
  have : H.Linear (Padic.coefficientExtensionIntegers l E.carrier) :=
    fullIntegralFunctorLinear l Ω E X Y F h
  exact {
    obj := fun K ↦ ⟨H.obj K.obj⟩
    map := fun f ↦ (H.mapLinearMap (Padic.coefficientExtensionIntegers l E.carrier)).baseChange
      (Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) f
    map_id := fun K ↦ (rawTensorFunctorLaws _ H).1 K.obj
    map_comp := fun f g ↦ (rawTensorFunctorLaws _ H).2 _ _ _ f g }

/-- Canonical endpoint shift on raw rationalization, chosen without an operation.
Source: the inherited shifts of the two full coefficient subcategories
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
@[instance_reducible]
def integralRationalizationShift : (rationalization.{u, v} l Ω E X).CommShift ℤ := by
  letI : (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).CommShift ℤ :=
    Functor.CommShift.ofComp
      (show PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        (sfIntegralConstructible l E.carrier X).ι ≅
          (finiteTorConstructibleIntegral l E.carrier X).ι from Iso.refl _) ℤ
  infer_instance

/-- Only the adjunction and exact structures on the two explicitly constructed functors.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
structure RawLocalizedAdjunction
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y =
      finiteTorConstructibleIntegral l E.carrier Y) where
  adjunction : rawRationalFunctor l Ω E X Y A.F hX ⊣ rawRationalFunctor l Ω E Y X A.G hY
  [leftShift : (rawRationalFunctor l Ω E X Y A.F hX).CommShift ℤ]
  [rightShift : (rawRationalFunctor l Ω E Y X A.G hY).CommShift ℤ]
  leftExact : (rawRationalFunctor l Ω E X Y A.F hX).IsTriangulated
  rightExact : (rawRationalFunctor l Ω E Y X A.G hY).IsTriangulated
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ

variable {X Y}

/-- Package the exact structures; both functor data are the explicit tensor extensions.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def RawLocalizedAdjunction.operation
    {A : Operation.{u, v} l Ω X Y (.integral E)}
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)] {hX hY}
    (R : RawLocalizedAdjunction l Ω E X Y A hX hY) :
    Operation.{u, v} l Ω X Y (.rational E) where
  F := rawRationalFunctor l Ω E X Y A.F hX
  G := rawRationalFunctor l Ω E Y X A.G hY
  adjunction := R.adjunction
  leftAdditive := ⟨by intros; exact map_add _ _ _⟩
  rightAdditive := ⟨by intros; exact map_add _ _ _⟩
  leftShift := R.leftShift
  rightShift := R.rightShift
  leftExact := R.leftExact
  rightExact := R.rightExact
  unitShift := R.unitShift
  counitShift := R.counitShift

/-- The literal tensor extension agrees with rationalization on integral arrows.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def rawRationalComparison
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    F ⋙ rationalization.{u, v} l Ω E Y ≅
      rationalization.{u, v} l Ω E X ⋙ rawRationalFunctor l Ω E X Y F hX :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end WeilConjectures.ConstructibleExceptionalCoefficients
