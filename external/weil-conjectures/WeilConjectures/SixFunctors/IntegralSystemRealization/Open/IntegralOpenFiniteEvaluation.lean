/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenScalarUnitSquare

/-! # Finite evaluation of the open reduction mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem assemble
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {J : A ⥤ B} {P : B ⥤ A} {j : C ⥤ D} {p : D ⥤ C}
    {L : E ⥤ F} {R : F ⥤ E}
    (a : J ⊣ P) (b : j ⊣ p) (c : L ⊣ R)
    {SX : A ⥤ C} {SY : B ⥤ D} {EX : C ⥤ E} {EY : D ⥤ F}
    {TX : A ⥤ E} {TY : B ⥤ F}
    (rX : SX ⋙ EX ≅ TX) (rY : SY ⋙ EY ≅ TY)
    (α : P ⋙ SX ⟶ SY ⋙ p) (d : p ⋙ EX ⟶ EY ⋙ R)
    (m : SX ⋙ j ⟶ J ⋙ SY) (v : j ⋙ EY ≅ EX ⋙ L)
    (q : P ⋙ TX ⟶ TY ⋙ R) (t : J ⋙ TY ⟶ TX ⋙ L)
    (hm : ∀ K, SX.map (a.unit.app K) ≫ α.app (J.obj K) =
      b.unit.app (SX.obj K) ≫ p.map (m.app K))
    (hv : ∀ M, EX.map (b.unit.app M) ≫ d.app (j.obj M) =
      c.unit.app (EX.obj M) ≫ R.map (v.inv.app M))
    (hs : ∀ H, EX.map (α.app H) ≫ d.app (SY.obj H) ≫ R.map (rY.hom.app H) =
      rX.hom.app (P.obj H) ≫ q.app H)
    (ht : ∀ K, TX.map (a.unit.app K) ≫ q.app (J.obj K) ≫ R.map (t.app K) =
      c.unit.app (TX.obj K)) (K : A) :
    EY.map (m.app K) ≫ rY.hom.app (J.obj K) ≫ t.app K =
      v.hom.app (SX.obj K) ≫ L.map (rX.hom.app K) := by
  apply (cancel_epi (v.inv.app (SX.obj K))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (c.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hv (SX.obj K))]
  have hn := d.naturality (m.app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← EX.map_comp_assoc, ← hm K, EX.map_comp_assoc,
    reassoc_of% (hs (J.obj K))]
  have hr := rX.hom.naturality (a.unit.app K)
  simp only [Functor.comp_map] at hr
  rw [reassoc_of% hr, ht K]
  simpa only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] using
    c.unit.naturality (rX.hom.app K)

/-- Open scalar comparison in the published finite constant-ring coordinates.
Source: Stacks 03DI and 0E8I; open mate of fix-prop-coherence
(blueprint: lem-sf-integral-open-finite-evaluation). -/
@[irreducible] def openFiniteReduction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    ringedOpen l E j ⋙ scalarReductionDerivedExtension l E Y n ⟶
      scalarReductionDerivedExtension l E X n ⋙
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory :=
  letI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).1
  letI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  letI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  Functor.whiskerLeft _ (PurCompactSupport.finiteReductionIso l E Y n).inv ≫
    PurCompactSupport.openComparison
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) j ≫
    Functor.whiskerLeft _
      (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finiteOpenIso l E n j)).hom ≫
    Functor.whiskerRight (PurCompactSupport.finiteReductionIso l E X n).hom _

/-- Evaluating the open reduction mate gives the canonical open scalar comparison.
This assertion involves no proper image, total-limit projection or inverse
reconstruction unit.
Source: Stacks 03DI, 07A7 and 0E8I; fix-prop-coherence.proof.md, preservation
of adjunction units and counits; Step 2 of integral support projection transport
(blueprint: lem-sf-integral-open-finite-evaluation).

Proof: evaluate the whole-system K-flat equation model.model for j. The ordinary
comparison is the conjugate of ordinary.comparison; its sectionwise projection
equation identifies the evaluated pullback comparison with quotient/pullback
interchange. On a flat-term K-flat representative both maps send a pure tensor
to the same pulled-back section tensored with its quotient coefficient. Thus the
localized pullback square is the specified finite scalar/pullback square.
Take inverse open-adjunction mates of this square. By the definition of
model.openReduction and OpenEvaluation.transpose, its two horizontal composites
are the evaluation of model.openReduction followed by reductionEvaluation, and
openEvaluation followed by open image of reductionEvaluation. The coefficient
mate on the remaining side is PurCompactSupport.openComparison. The adjunction
uniqueness defining finiteReductionIso and finiteOpenIso preserves the actual
units, so transporting that mate gives openFiniteReduction, with precisely the
orientations displayed below. The mate equivalence and the triangle identities
give the equality before any limit or completeness argument. For an empty open
this is the same zero extension calculation, with no nonemptiness requirement. -/
theorem integralOpenFiniteEvaluation (o : Operations l E)
    (model : RealizationModel l E o) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : Integral l E X) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Y n).map ((model.openReduction l E j).app K) ≫
      ((calculus l E Y).reductionEvaluation n).hom.app ((ringedOpen l E j).obj K) ≫
      (openFiniteReduction l E j n).app K =
    ((o.openEvaluation j).evaluation n).hom.app ((calculus l E X).reduction.obj K) ≫
      (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
          (((calculus l E X).reductionEvaluation n).hom.app K) := by
  apply assemble (ringedOpenAdj l E j) (o.extension j).adj (finiteOpenAdj l E j n)
    ((calculus l E X).reductionEvaluation n) ((calculus l E Y).reductionEvaluation n)
    (model.reductionPull j).hom (pullbackTensorDerivedEvaluation l E j n).hom
    (model.openReduction l E j) ((o.openEvaluation j).evaluation n)
    (integralFiniteScalarPull l E j n).hom (openFiniteReduction l E j n)
  · intro H
    exact unit_mateEquiv_symm (ringedOpenAdj l E j) (o.extension j).adj
      (model.reductionPull j).hom H
  · intro M
    have h := unit_mateEquiv_symm (o.extension j).adj (finiteOpenAdj l E j n)
      (pullbackTensorDerivedEvaluation l E j n).hom M
    rw [(o.openEvaluation j).transpose n] at h
    exact h
  · intro H
    exact integralReductionPullFiniteSquare l E o model j H n
  · intro H
    simpa only [openFiniteReduction, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, coefficientFiniteDerivedExtension, Functor.comp_obj,
      Functor.id_obj, PurCompactSupport.reduction] using integralOpenScalarUnitSquare l E j H n

end WeilConjectures.IntegralSystemRealization
