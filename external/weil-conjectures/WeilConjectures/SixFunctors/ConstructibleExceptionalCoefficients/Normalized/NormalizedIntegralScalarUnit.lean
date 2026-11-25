/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedIntegralScalarUnitUnderlying

/-! # Normalized integral scalar identity under rationalization -/

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

private theorem faithful_heq {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) [G.Faithful] {W X Y Z : A} (hW : W = Y) (hX : X = Z)
    (a : W ⟶ X) (b : Y ⟶ Z) (ha : HEq (G.map a) (G.map b)) : HEq a b := by
  subst Y Z
  exact heq_of_eq (G.map_injective (eq_of_heq ha))

/-- A multiplication-normalized restricted unit localizes to the specified rational unit.
Source: exceptional coefficient construction, integral-to-rational identity paragraph;
scalar extension composition, identity clause
(blueprint: lem-sf-normalized-integral-scalar-unit).

Proof: the integral normalization theorem identifies the underlying unit arrows.
The functor equality hS identifies their source objects. Full-subcategory faithfulness
lifts the underlying comparison to the intrinsic integral category. Apply raw
rational localization, then use the component characterization in
sfRationalScalarUnit_existsUnique. The integral representative is unchanged,
including at the zero object. -/
theorem normalized_integral_scalar_unit
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral E)
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)) T)
    (hS : S.functor ⋙ RingStage.inclusion.{u, v} l Ω T (.integral E) =
      RingStage.inclusion.{u, v} l Ω T (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T)
    (hχ : ∀ K : C.{u, v} l Ω T (.integral E),
      HEq (S.realization.inv.app K)
        ((completedScalarComparison l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T).app K.obj))
    (h : ∀ W : Scheme.{max u v},
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)).map W = 𝟙 _)
    (e : ScalarIdentity.{u, v} l Ω h T S)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((rationalization.{u, v} l Ω E T).map (e.iso.hom.app K))
      ((sfRationalScalarUnit l E.carrier T 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((rationalization.{u, v} l Ω E T).obj K)) := by
  let I := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  let J := I.obj K
  have ho : (S.functor.obj K).obj =
      (integralScalarExtensionOfUniverses l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier) T).obj K.obj := Functor.congr_obj hS K
  have ho' : I.obj (S.functor.obj K) =
      (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
        E.carrier E.carrier (AlgHom.id (Padic l) E.carrier) T).obj J :=
    ObjectProperty.FullSubcategory.ext ho
  have hu := normalized_integral_scalar_unit_underlying l Ω E T S hS hχ h e K
  have he' : HEq (I.map (e.iso.hom.app K))
      ((sfIntegralScalarUnit l E.carrier T 0 (Fact.out : l.Prime).ne_zero).hom.app J) :=
    faithful_heq (sfIntegralConstructible l E.carrier T).ι ho' rfl _ _ hu
  have hrat := (sfRationalScalarUnit_existsUnique l E.carrier T 0
    (Fact.out : l.Prime).ne_zero).exists.choose_spec
    ((rationalization.{u, v} l Ω E T).obj K)
  have hmap := map_heq (sfRationalConstructibleLocalization l E.carrier T)
    ho' rfl he'
  exact hmap.trans hrat.symm

end WeilConjectures.ConstructibleExceptionalCoefficients
