/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all WeilConjectures.SmoothPurity.Scalar.ScalarShiftNormalization

/-! # The canonical scalar square on intrinsic integral stages -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

private theorem normalized_shift_square
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D) (S : D ⥤ D)
    {U V : C} {Z W B A : D}
    (q : U ≅ V) (r : R.obj V ≅ S.obj Z) (e : Z ≅ W)
    (d : R.obj U ≅ B) (a : B ⟶ A) (p : A ≅ S.obj W)
    (hU : U = V) (hZ : Z = W) (hB : R.obj U = B) (hA : A = S.obj W)
    (hq : HEq q.hom (𝟙 U)) (hp : HEq p.hom (𝟙 A))
    (he : HEq e.hom (𝟙 Z)) (hd : HEq d.hom (𝟙 (R.obj U)))
    (hr : HEq r.hom a) :
    R.map q.hom ≫ r.hom ≫ S.map e.hom = d.hom ≫ a ≫ p.hom := by
  subst V
  subst W
  subst B
  subst A
  have hq' : q.hom = 𝟙 U := eq_of_heq hq
  have hp' : p.hom = 𝟙 (S.obj Z) := eq_of_heq hp
  have he' : e.hom = 𝟙 Z := eq_of_heq he
  have hd' : d.hom = 𝟙 (R.obj U) := eq_of_heq hd
  rw [hq', hp', he', hd', R.map_id, S.map_id]
  simpa only [Category.id_comp, Category.comp_id] using eq_of_heq hr

private theorem eqToIso_app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) (K : C) :
    HEq ((eqToIso h).hom.app K) (𝟙 (F.obj K)) := by
  cases h
  rfl

section
universe r c h
private theorem tensor_hom_heq {R : Type r} [CommRing R]
    {C : Type c} [Category.{h} C] [Preadditive C] [Linear R C]
    (p : R) {α : Type (max r h)} (f : α) {K L : C}
    (g : Localization.Away p ⊗[R] (K ⟶ L)) (h : HEq f g) :
    HEq f (show (ScalarLocalization.mk (R := R) (p := p) K ⟶
      ScalarLocalization.mk (R := R) (p := p) L) from g) := h
end

attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfRationalTriangulationDatum
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (T : Scheme.{u}) (a b : AlgebraicallyClosedCoefficients.Index l Ω) (h : a ≤ b)

/-- Localization of the canonical intrinsic integral scalar shift agrees with the canonical
rational scalar shift. Source: Zheng, Constructions 6.2 and 6.6
(blueprint: lem-sf-canonical-stage-scalar-shift).

Proof: the object and pure tensor formulas identify both composite functors. Their identity
comparison commutes with shift one: the two localization comparisons are identities, and the
rational scalar comparison is the localization of the integral one. Integer shift coherence
extends this equation to all integers. -/
theorem canonical_stage_scalar_shift :
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω a
    let L := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω b
    let S := GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T a b h
    let R := sfRationalScalarExtension l E T 0
      (Fact.out : l.Prime).ne_zero L
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h)
    let QE := sfRationalConstructibleLocalization l E T
    let QL := sfRationalConstructibleLocalization l L T
    letI : QE.CommShift ℤ := sfRationalLocalizationCommShift l E T
    letI : QL.CommShift ℤ := sfRationalLocalizationCommShift l L T
    letI : S.CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω T a b h
    letI : R.CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T a b h
    ∃ e : QE ⋙ R ≅ S ⋙ QL,
      (∀ K, HEq (e.hom.app K) (𝟙 (R.obj (QE.obj K)))) ∧ e.hom.CommShift ℤ := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω a
  let L := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω b
  let i := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h
  let S := GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T a b h
  let R := sfRationalScalarExtension l E T 0
      (Fact.out : l.Prime).ne_zero L
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h)
  let QE := sfRationalConstructibleLocalization l E T
  let QL := sfRationalConstructibleLocalization l L T
  letI : QE.CommShift ℤ := sfRationalLocalizationCommShift l E T
  letI : QL.CommShift ℤ := sfRationalLocalizationCommShift l L T
  letI : S.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω T a b h
  letI : R.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T a b h
  have hf : QE ⋙ R = S ⋙ QL := by
    apply Functor.hext
    · intro K
      exact sfRationalScalarExtension_obj l E T 0
        (Fact.out : l.Prime).ne_zero L i _
    · intro K K' f
      have hh := sfRationalScalarExtension_map_tmul l E T 0
        (Fact.out : l.Prime).ne_zero L i K K' f 1
      simp only [map_one] at hh
      dsimp only [QE, QL, R, S, GeneralAlgebraicallyClosedCoefficients.integralTransition,
        Functor.comp_map, sfRationalConstructibleLocalization, ScalarLocalization.localization]
      dsimp only [E, L, i, Functor.comp_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization,
        ScalarLocalization.category,
        GeneralAlgebraicallyClosedCoefficients.stageCategory] at hh ⊢
      exact tensor_hom_heq (Padic.coefficientExtensionUniformizer l L)
        _ _ hh
  let e := eqToIso hf
  refine ⟨e, eqToIso_app_heq hf, ?_⟩
  apply commShift_of_one
  constructor
  ext K
  simp only [Functor.commShiftIso_comp_hom_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  have oE (J : sfIntegralConstructibleCategory l E T) :
      QE.obj (J⟦(1 : ℤ)⟧) = (QE.obj J)⟦(1 : ℤ)⟧ :=
    (Functor.congr_obj
      (sfRationalTriangulationDatum l E T).choose_spec.choose_spec.1 (QE.obj J)).symm
  have oL (J : sfIntegralConstructibleCategory l L T) :
      QL.obj (J⟦(1 : ℤ)⟧) = (QL.obj J)⟦(1 : ℤ)⟧ :=
    (Functor.congr_obj
      (sfRationalTriangulationDatum l L T).choose_spec.choose_spec.1 (QL.obj J)).symm
  exact normalized_shift_square R (shiftFunctor _ (1 : ℤ))
    ((QE.commShiftIso (1 : ℤ)).app K)
    ((R.commShiftIso (1 : ℤ)).app (QE.obj K)) (e.app K) (e.app (K⟦(1 : ℤ)⟧))
    (QL.map ((S.commShiftIso (1 : ℤ)).hom.app K))
    ((QL.commShiftIso (1 : ℤ)).app (S.obj K))
    (oE K) (Functor.congr_obj hf K) (Functor.congr_obj hf (K⟦(1 : ℤ)⟧))
    (oL (S.obj K))
    ((sfRationalTriangulationDatum l E T).choose_spec.choose_spec.2.choose_spec.choose_spec.1 K)
    ((sfRationalTriangulationDatum l L T).choose_spec.choose_spec.2.choose_spec.choose_spec.1
      (S.obj K))
    (eqToIso_app_heq hf K) (eqToIso_app_heq hf (K⟦(1 : ℤ)⟧))
    ((GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      l Ω T a b h).exists.choose_spec (QE.obj K))

end WeilConjectures
