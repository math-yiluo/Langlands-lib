/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import Mathlib.Algebra.CharP.CharAndCard

/-! # Normalization of rational tensor and pullback comparisons

The canonical scalar localization carries the integral tensor and pullback maps
into the rational ones. This is the common normalization calculation for the
proper and open projection mates.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-rational-pullback-tensor-localization-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

section ProjectionTransport
universe a b a' b' ha hb ha' hb'
variable {A : Type a} [Category.{ha} A] {B : Type b} [Category.{hb} B]
  {A' : Type a'} [Category.{ha'} A'] {B' : Type b'} [Category.{hb'} B']

private theorem prodEqToHom {C : Type a} [Category.{ha} C]
    {D : Type b} [Category.{hb} D] {X X' : C} {Y Y' : D}
    (p : X = X') (q : Y = Y') :
    Prod.mkHom (eqToHom p) (eqToHom q) = eqToHom (Prod.ext p q) := by
  subst X' Y'
  rfl

private theorem normalizedTensorSquare
    {F : A ⥤ B} {F' : A' ⥤ B'} (c : A ⥤ A') (d : B ⥤ B')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (hF : F ⋙ d = c ⋙ F') (hA : TA ⋙ c = c.prod c ⋙ TA')
    (hB : TB ⋙ d = d.prod d ⋙ TB') (M N : A)
    (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N)))
    (hm : HEq (d.map mu) mu') :
    d.map mu ≫ (eqToIso hB).hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom ((eqToIso hF).hom.app M) ((eqToIso hF).hom.app N)) =
      (eqToIso hF).hom.app (TA.obj (M, N)) ≫
        F'.map ((eqToIso hA).hom.app (M, N)) ≫ mu' := by
  simp only [eqToIso.hom, eqToHom_app, prodEqToHom, eqToHom_map]
  apply eq_of_heq
  simpa only [Category.assoc, eqToHom_trans, comp_eqToHom_heq_iff,
    eqToHom_comp_heq_iff, heq_comp_eqToHom_iff, heq_eqToHom_comp_iff] using hm

private theorem mapHEq (F : A ⥤ B) {X Y X' Y' : A}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X' Y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

end ProjectionTransport

/-- Localization of the prescribed integral tensor is the prescribed rational
bifunctor on integral inputs, including its morphism action.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-pullback-tensor-localization-square). -/
theorem rationalProjectionTensorFunctorEq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (X : SixFunctorSpace D) :
    Functor.uncurry.obj (H.integralTensor X) ⋙
        sfRationalConstructibleLocalization C.l E X.obj.left =
      (sfRationalConstructibleLocalization C.l E X.obj.left).prod
          (sfRationalConstructibleLocalization C.l E X.obj.left) ⋙
        Functor.uncurry.obj (H.rationalTensor X) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.obj.hom.appTop ≫
      X.obj.left.Γevaluation x).hom
    (Eq.mp (congrArg IsUnit (map_natCast φ C.l))
      ((isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
          C.different.symm)).map φ)).invertible
  rw [H.integralTensorNormalization X, H.rationalTensorNormalization X]
  let V := sfRationalConstructibleLocalization C.l E X.obj.left
  let I := constructibleIntegralTensor C.l E X.obj.left
  let R := (rationalDerivedTensor_existsUnique C.l E X.obj.left).exists.choose
  have hs := (rationalDerivedTensor_existsUnique C.l E X.obj.left).exists.choose_spec
  have ho : ∀ MN, (I ⋙ V).obj MN = ((V.prod V) ⋙ R).obj MN := by
    intro MN
    exact (hs.1 ((V.obj MN.1), (V.obj MN.2))).symm
  have hm : ∀ {MN PQ} (a : MN ⟶ PQ),
      HEq ((I ⋙ V).map a) (((V.prod V) ⋙ R).map a) := by
    intro MN PQ a
    rcases MN with ⟨M, N⟩
    rcases PQ with ⟨P, Q⟩
    rcases a with ⟨a₁, a₂⟩
    obtain ⟨b, hb, htmul⟩ := hs.2 (V.obj M) (V.obj P) (V.obj N) (V.obj Q)
    change HEq (V.map (I.map (Prod.mkHom a₁ a₂)))
      (R.map (Prod.mkHom (V.map a₁) (V.map a₂)))
    have he := htmul a₁ a₂ 1 1
    simp only [one_mul] at he
    have hv : HEq (V.map (I.map (Prod.mkHom a₁ a₂)))
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer C.l E))
          ⊗ₜ[Padic.coefficientExtensionIntegers C.l E]
            (constructibleIntegralTensor C.l E X.obj.left).map (Prod.mkHom a₁ a₂)) := by
      rfl
    exact hv.trans (((heq_of_eq (hb (V.map a₁) (V.map a₂))).trans he).symm)
  have he : I ⋙ V = (V.prod V) ⋙ R := by
    refine CategoryTheory.Functor.ext ho ?_
    intro MN PQ a
    exact (conj_eqToHom_iff_heq _ _ (ho MN) (ho PQ)).2 (hm a)
  change Functor.uncurry.obj (Functor.curry.obj I) ⋙ V =
    (V.prod V) ⋙ Functor.uncurry.obj (Functor.curry.obj R)
  rw [Functor.uncurry_obj_curry_obj, Functor.uncurry_obj_curry_obj]
  exact he

/-- The shared tensor endpoint comparison, constructed from the proved functor equality.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-rational-pullback-tensor-localization-square). -/
def rationalProjectionTensorComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (X : SixFunctorSpace D) :=
  eqToIso (rationalProjectionTensorFunctorEq H X)

attribute [local irreducible] sfRationalTriangulationDatum sfIntegralConstructible
  ScalarLocalization.composition

private theorem rationalProjectionPullFunctorEq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] :
    H.integral.pull f ⋙ sfRationalConstructibleLocalization C.l E X.obj.left =
      sfRationalConstructibleLocalization C.l E Y.obj.left ⋙ H.rational.pull f := by
  rw [H.integralPullback f, H.rationalPullback f]
  have hs := (rationalDerivedPullback_existsUnique C.l E f.hom.left).exists.choose_spec
  refine Functor.hext (fun K ↦ (hs.2.1 _).symm) ?_
  intro K L a
  exact (hs.2.2 K L a 1).symm

private theorem rationalProjectionPullComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] :
    (H.rationalization.directAdjunction f).left =
      eqToIso (rationalProjectionPullFunctorEq H f) := by
  apply Iso.ext
  ext K
  simp only [eqToIso.hom, eqToHom_app]
  exact eq_of_heq ((H.rationalModelNormalization.2.1 f K).trans
    (eqToHom_heq_id_dom _ _ _).symm)

/-- The canonical tensor comparison commutes with pullback for any pair of supplied
integral and rational tensor-pullback isomorphisms normalized to the canonical maps.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-rational-pullback-tensor-localization-square).

Proof: identify the integral source and target objects using the prescribed
pullback and tensor normalizations. Map the integral normalization through scalar
localization. The defining formula for canonicalRationalPullbackTensor identifies
its hom on localized inputs with this mapped integral hom. The prescribed
pullback comparison is the identity on these integral models, hence is the
isomorphism of the proved pullback functor equality. Transport the heterogeneous
hom equality through that functor equality and the two tensor functor equalities.
This produces the displayed square without any faithfulness or nonzero-input
assumptions. -/
theorem rationalProjectionPullTensorSquare
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    (mu : (Functor.postcompose₂.obj (H.integral.pull f)).obj (H.integralTensor Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (H.integral.pull f)).obj
        (H.integral.pull f)).obj (H.integralTensor X))
    (mu' : (Functor.postcompose₂.obj (H.rational.pull f)).obj (H.rationalTensor Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (H.rational.pull f)).obj
        (H.rational.pull f)).obj (H.rationalTensor X))
    (M N : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (hi : HEq ((mu.hom.app M).app N)
      (canonicalIntegralPullbackTensor C.l E f.hom.left M N).hom)
    (hr : HEq ((mu'.hom.app
        ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj M)).app
          ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj N))
      (canonicalRationalPullbackTensor C.l E f.hom.left
        ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj M)
        ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj N)).hom) :
    (sfRationalConstructibleLocalization C.l E X.obj.left).map
        ((mu.hom.app M).app N) ≫
      (rationalProjectionTensorComparison H X).hom.app
        ((H.integral.pull f).obj M, (H.integral.pull f).obj N) ≫
      (Functor.uncurry.obj (H.rationalTensor X)).map
        (Prod.mkHom ((H.rationalization.directAdjunction f).left.hom.app M)
          ((H.rationalization.directAdjunction f).left.hom.app N)) =
    (H.rationalization.directAdjunction f).left.hom.app
        (((H.integralTensor Y).obj M).obj N) ≫
      (H.rational.pull f).map ((rationalProjectionTensorComparison H Y).hom.app (M, N)) ≫
      ((mu'.hom.app
        ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj M)).app
          ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj N)) := by
  let V := sfRationalConstructibleLocalization C.l E X.obj.left
  have hs : (H.integral.pull f).obj (((H.integralTensor Y).obj M).obj N) =
      (constructibleIntegralPullback C.l E f.hom.left).obj
        ((constructibleIntegralTensor C.l E Y.obj.left).obj (M, N)) := by
    rw [H.integralPullback f, H.integralTensorNormalization Y]
    rfl
  have ht : ((H.integralTensor X).obj ((H.integral.pull f).obj M)).obj
        ((H.integral.pull f).obj N) =
      (constructibleIntegralTensor C.l E X.obj.left).obj
        ((constructibleIntegralPullback C.l E f.hom.left).obj M,
          (constructibleIntegralPullback C.l E f.hom.left).obj N) := by
    rw [H.integralPullback f, H.integralTensorNormalization X]
    rfl
  have hi := mapHEq V hs ht hi
  have hcan := (canonicalRationalPullbackTensor_existsUnique C.l E f.hom.left
    ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj M)
    ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj N)).exists.choose_spec
  change HEq (canonicalRationalPullbackTensor C.l E f.hom.left
      ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj M)
      ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj N)).hom
    (V.map (canonicalIntegralPullbackTensor C.l E f.hom.left M N).hom) at hcan
  rw [rationalProjectionPullComparison H f]
  have h := normalizedTensorSquare _ _ _ _ _ _ (rationalProjectionPullFunctorEq H f)
    (rationalProjectionTensorFunctorEq H Y) (rationalProjectionTensorFunctorEq H X)
    M N _ _ (hi.trans (hr.trans hcan).symm)
  simpa only [rationalProjectionTensorComparison, Functor.uncurry_obj_obj] using h

end WeilConjectures
