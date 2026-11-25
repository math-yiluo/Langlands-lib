/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackCounitCompatibility

/-! # Normalization of completed scalar pullback in whole-system coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph, scalar compatibility of the pullback comparisons
(blueprint: lem-sf-integral-scalar-pullback-completion-normalization).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem counit_coordinates
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B) (L : B ⥤ A)
    (adj : R ⊣ L) {X Y : A} {P Q : B}
    (a : X ≅ L.obj P) (b : Y ≅ L.obj Q) (c : P ≅ Q) (f : X ⟶ Y)
    (h : R.map f ≫ (R.map b.hom ≫ adj.counit.app Q) =
      (R.map a.hom ≫ adj.counit.app P) ≫ c.hom) :
    f ≫ b.hom ≫ L.map c.inv = a.hom := by
  have hf : f ≫ b.hom = a.hom ≫ L.map c.hom := by
    apply (adj.homEquiv X Q).symm.injective
    simp only [Adjunction.homEquiv_counit, R.map_comp, Category.assoc]
    have hn := adj.counit.naturality c.hom
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn]
    simpa only [Category.assoc] using h
  rw [← Category.assoc, hf]
  simp only [Category.assoc, ← L.map_comp, Iso.hom_inv_id, L.map_id, Category.comp_id]

private theorem counit_coordinate_map
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B) (L : B ⥤ A)
    (ε : L ⋙ R ⟶ 𝟭 B) {X : A} {P Q : B} (a : X ≅ L.obj P) (t : P ⟶ Q) :
    R.map (a.hom ≫ L.map t) ≫ ε.app Q = (R.map a.hom ≫ ε.app P) ≫ t := by
  rw [R.map_comp, Category.assoc]
  have hn := ε.naturality t
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, Category.assoc]

/-- The specified tensor-and-completion comparison has the prescribed lambda/mu
coordinates for any representative-normalized comparison system.

Source: the Weil-structures paragraph of
literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md;
Stacks 099N and the scalar tower calculation of
lem-pur-scalar-extension-tower-coherence
(blueprint: lem-sf-integral-scalar-pullback-completion-normalization).

Proof: apply integralScalarPullbackCounit_compatibility. Naturality of the
reduction/limit counit identifies the coordinates of a realization followed by
L(t) with its original counit coordinates followed by t. Applied to the two
primitive realizations and their scalarized pullback and pulled-back scalar
counits, this rewrites the whole-system square as equality of the adjunction
mates of alpha followed by the target realization and lambda followed by
L(kappa). Injectivity of the adjunction Hom equivalence identifies these two
ambient arrows. Compose with L(kappa inverse) and cancel. By definition the
target realization followed by L(kappa inverse) is mu, which proves the claim.
All operations are on entire systems; no separate finite evaluation is used. -/
theorem integralScalarPullbackCompletion_normalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj K.obj)) :
    (scalarPullbackCompleted l E L ι f K.obj K.property.1 hF).hom ≫
        (integralComparisonMu l E L ι C f K).hom =
      (integralComparisonLambda l E L ι C f K).hom := by
  let R := ((C.coefficient L).system X).reduction
  let LL := coefficientSequenceLimit l L X
  let ε := ((C.coefficient L).system X).adjunction.counit
  let U := integralComparisonDerivedSequencePullback l L f
  let S := integralComparisonDerivedSequenceScalar l E L ι X
  let δE := @asIso _ _ _ _ _ ((C.coefficient E).effective f K)
  let δS := @asIso _ _ _ _ _ ((C.scalar E L ι).effective Y K)
  let a := ((C.scalar E L ι).model X).realization.app
    ((integralDerivedPullback l E f).obj K.obj)
  let b := ((C.coefficient L).pullback f).realization.app
    ((integralScalarExtension l E L ι Y).obj K.obj)
  let c := (integralComparisonSystemScalarPullback l E L ι f).app
    (((C.coefficient E).system Y).reduction.obj K.obj)
  have h := integralScalarPullbackCounit_compatibility l E L ι C f K hF
  have h' : R.map (scalarPullbackCompleted l E L ι f K.obj K.property.1 hF).hom ≫
        (R.map (b ≪≫ LL.mapIso (U.mapIso δS)).hom ≫ ε.app _) =
      (R.map (a ≪≫ LL.mapIso (S.mapIso δE)).hom ≫ ε.app _) ≫ c.hom := by
    rw [show (b ≪≫ LL.mapIso (U.mapIso δS)).hom =
      b.hom ≫ LL.map (U.map δS.hom) from rfl]
    rw [show (a ≪≫ LL.mapIso (S.mapIso δE)).hom =
      a.hom ≫ LL.map (S.map δE.hom) from rfl]
    rw [counit_coordinate_map R LL ε b, counit_coordinate_map R LL ε a]
    simpa only [R, LL, ε, U, S, a, b, c, δE, δS, asIso_hom, Iso.app_hom,
      Functor.comp_obj, Functor.id_obj,
      integralComparisonPullbackCounit, integralComparisonScalarCounit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc] using h
  have hn := counit_coordinates R LL ((C.coefficient L).system X).adjunction
    (a ≪≫ LL.mapIso (S.mapIso δE)) (b ≪≫ LL.mapIso (U.mapIso δS)) c
    (scalarPullbackCompleted l E L ι f K.obj K.property.1 hF).hom h'
  simpa only [integralComparisonMu, integralComparisonLambda, a, b, c, LL, U, S,
    δE, δS, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] using hn

end WeilConjectures
