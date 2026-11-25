/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.IntegralSystemCompositorNormalization
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOpenBaseChangeEvaluation
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization

/-! # Exact localization of the integral system pullback square

(blueprint: lem-weil-integral-system-square-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FrobeniusExchange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheafTransition ProEtale.VaryingRing.coefficientTransition
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  integralComparisonSequencePullback
attribute [local irreducible] constantSheaf
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
private abbrev squareRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
private abbrev squareQuotient (n : ℕ) : squareRings l E (n + 1) ⟶ squareRings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift

/-- Both named derived inverse images localize the same chosen ordinary pullback. -/
private theorem integralSystemPull_eq_varying {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonDerivedSequencePullback l E f =
      ProEtale.VaryingRing.G (squareRings l E) (squareQuotient l E) f := by
  unfold integralComparisonDerivedSequencePullback ProEtale.VaryingRing.G
    integralComparisonSequencePullback ProEtale.VaryingRing.pull
  rfl

/-- Invertibility of an inverse mate is unchanged by choosing other left adjoints. -/
private theorem inverseMateIsoOfAnyAdj
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F Q : A ⥤ B} {P : B ⥤ A} {F' Q' : C ⥤ D} {P' : D ⥤ C}
    (a : F ⊣ P) (qa : Q ⊣ P) (b : F' ⊣ P') (qb : Q' ⊣ P')
    (E : A ⥤ C) (E' : B ⥤ D) (d : P ⋙ E ≅ E' ⋙ P')
    (hi : IsIso ((mateEquiv qa qb).symm d.hom)) :
    IsIso ((mateEquiv a b).symm d.hom) := by
  let α := ((mateEquiv qa qb).symm d.hom)
  let e := @asIso _ _ _ _ α hi
  let q := e.symm
  have hq (N : A) : E.map (qa.unit.app N) ≫ d.hom.app (Q.obj N) ≫
      P'.map (q.hom.app N) = qb.unit.app (E.obj N) := by
    rw [← Category.assoc, unit_mateEquiv_symm qa qb d.hom N, Category.assoc,
      ← P'.map_comp]
    change qb.unit.app (E.obj N) ≫ P'.map
      (e.hom.app N ≫ e.inv.app N) = _
    rw [e.hom_inv_id_app N]
    exact (congrArg (fun z ↦ qb.unit.app (E.obj N) ≫ z) (P'.map_id _)).trans
      (Category.comp_id _)
  exact ProEtale.VaryingRing.inverseMateIsoOfUnit a b E E' d.hom
    (isoWhiskerRight (a.leftAdjointUniq qa) E' ≪≫ q ≪≫
      isoWhiskerLeft E (b.leftAdjointUniq qb).symm)
    (ProEtale.VaryingRing.transportedUnit a qa b qb E E' d q hq)

/-- Transport inverse-mate invertibility across equal functor coordinates, without
unfolding either the given adjunction or the localized square. -/
private theorem inverseMateIsoOfFunctorEqualities
    {A B : Type u} [Category A] [Category B] {F : A ⥤ B}
    {P Q : B ⥤ A} {E H : A ⥤ A} {E' H' : B ⥤ B}
    (hp : P = Q) (he : E = H) (he' : E' = H') (a : F ⊣ P)
    (d : P ⋙ E ⟶ E' ⋙ P) (d' : Q ⋙ H ⟶ H' ⋙ Q) (hd : HEq d d')
    (hi : ∀ b : F ⊣ Q, IsIso ((mateEquiv b b).symm d')) :
    IsIso ((mateEquiv a a).symm d) := by
  subst Q
  subst H
  subst H'
  cases hd
  exact hi a

/-- Cartesian open base change remains invertible for any adjunction on the
same derived pullback functor. -/
private theorem varyingInverseOpenMate_isIso
    (R : ℕ → CommRingCat.{u + 1}) (q : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (gU : U ⟶ U) (gX : X ⟶ X) (sq : IsPullback gU j j gX)
    {F : ProEtale.VaryingRing.Derived R q U ⥤ ProEtale.VaryingRing.Derived R q X}
    (a : F ⊣ ProEtale.VaryingRing.G R q j) :
    IsIso ((mateEquiv a a).symm
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleSquareG R q gU j j gX sq.w)).inv) := by
  have hm := ProEtale.VaryingRing.betaInv_mate R q gU j j gX sq.w sq
  have he : ((mateEquiv (ProEtale.VaryingRing.jAdj R q j)
      (ProEtale.VaryingRing.jAdj R q j)).symm
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleSquareG R q gU j j gX sq.w)).inv) =
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleBeta R q gU j j gX sq.w sq)).inv := by
    exact
      (((mateEquiv (ProEtale.VaryingRing.jAdj R q j)
        (ProEtale.VaryingRing.jAdj R q j)).symm_apply_eq).2 hm.symm)
  have hi : IsIso ((mateEquiv (ProEtale.VaryingRing.jAdj R q j)
      (ProEtale.VaryingRing.jAdj R q j)).symm
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleSquareG R q gU j j gX sq.w)).inv) := by
    rw [he]
    infer_instance
  exact inverseMateIsoOfAnyAdj a (ProEtale.VaryingRing.jAdj R q j)
    a (ProEtale.VaryingRing.jAdj R q j)
    (ProEtale.VaryingRing.G R q gU) (ProEtale.VaryingRing.G R q gX)
    (Functor.mapDerivedCategorySquareIso
      (ProEtale.VaryingRing.moduleSquareG R q gU j j gX sq.w)).symm hi

/-- The specified integral system pullback square is the localization of the ordinary
varying-ring square at the actual lifted quotient rings.
Source: Stacks 0D6D and 03S6; Zheng 4.10
(blueprint: lem-weil-integral-system-square-normalization).
Proof: exact localization preserves the compositor word and the equality transport
forming the varying-ring square. The proved compositor normalization identifies each
derived compositor with the integral one. The equality transports agree definitionally. -/
theorem integralComparisonSystemSquare_eq_varyingRing
    {U X : Scheme.{u}} (j : U ⟶ X) (gU : U ⟶ U) (gX : X ⟶ X)
    (h : gU ≫ j = j ≫ gX) :
    (integralComparisonSystemComposition l E j gX).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) h.symm) ≪≫
        integralComparisonSystemComposition l E gU j =
      Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleSquareG
          (fun n ↦ CommRingCat.of (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))
          (fun n ↦ CommRingCat.ofHom
            (Padic.coefficientExtensionTransition l E (n + 1)).ulift) gU j j gX h) := by
  rw [ProEtale.SemilinearProperOpen.Normalization.system_square_localization]
  rw [integralComparisonSystemComposition_eq_varyingRing,
    integralComparisonSystemComposition_eq_varyingRing]
  rfl

/-- The inverse Cartesian open mate is invertible in the actual integral coordinates,
for any adjunction on the specified restriction functor. -/
private theorem integralInverseOpenMate_isIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (gU : U ⟶ U) (gX : X ⟶ X) (sq : IsPullback gU j j gX)
    {F : coefficientSequenceDerived l E U ⥤ coefficientSequenceDerived l E X}
    (a : F ⊣ integralComparisonDerivedSequencePullback l E j) :
    IsIso ((mateEquiv a a).symm
      ((integralComparisonSystemComposition l E j gX).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) sq.w.symm) ≪≫
        integralComparisonSystemComposition l E gU j).inv) := by
  let d := (Functor.mapDerivedCategorySquareIso
    (ProEtale.VaryingRing.moduleSquareG
      (squareRings l E) (squareQuotient l E) gU j j gX sq.w)).inv
  refine inverseMateIsoOfFunctorEqualities
    (integralSystemPull_eq_varying l E j) (integralSystemPull_eq_varying l E gU)
    (integralSystemPull_eq_varying l E gX) a _ d ?_ ?_
  · exact heq_of_eq (congrArg Iso.inv
      (integralComparisonSystemSquare_eq_varyingRing l E j gU gX sq.w))
  · intro b
    exact varyingInverseOpenMate_isIso
      (squareRings l E) (squareQuotient l E) j gU gX sq b

end WeilConjectures.FrobeniusExchange
