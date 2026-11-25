/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorCoordinateMap
import all WeilConjectures.SixFunctors.IntegralHom.IntegralKoszulAugmentedModel
import all WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorUnitSections
import WeilConjectures.SixFunctors.IntegralHom.Signed.IntegralSignedHomTensorUnit
import WeilConjectures.SixFunctors.IntegralHom.KInjectivePrincipalTensor
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomKInjectiveDiagram
import Mathlib.CategoryTheory.WithTerminal.Basic

set_option linter.privateModule false

/-! # Unit-normalized tensor representatives of integral reduction towers

Source: the finite-free quotient resolution in the first paragraph of the current
blueprint `lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
namespace WeilConjectures.IntegralHom
attribute [local irreducible] koszulTensorPresentation tensorUnitIso homComplexFunctor
  HasDerivedCategory.standard derivedInternalHomOfUniverses
attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingSheaf CategoryTheory.sheafCompose

open CategoryTheory.MonoidalCategory
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local instance] countableColimits
  ordinaryTensorZero ordinaryTensorObjZero

private theorem postcompose_model_unit
    {C : Type*} [Category* C] {G V N M X : C}
    (gamma : G ⟶ V) (r : V ⟶ N) (b : N ⟶ M) (e : G ⟶ X)
    (u : X ⟶ N) (v : X ⟶ M) (hr : gamma ≫ r = e ≫ u) (hb : u ≫ b = v) :
    gamma ≫ (r ≫ b) = e ≫ v := by
  rw [← Category.assoc, hr, Category.assoc, hb]

private theorem map_unit_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (H : D ⥤ E) {B N X : C} {G Y : D} {V W : E}
    (gamma : G ⟶ Y) (r : Y ⟶ L.obj X) (e : L.obj N ≅ G) (u : B ≅ N)
    (i : B ⟶ X) (hb : H.obj (L.obj B) ⟶ V) (hx : H.obj (L.obj X) ⟶ W) (j : V ⟶ W)
    (hr : gamma ≫ r = e.inv ≫ L.map (u.inv ≫ i))
    (hn : H.map (L.map i) ≫ hx = hb ≫ j) :
    H.map gamma ≫ (H.map r ≫ hx) =
      (H.map e.inv ≫ H.map (L.map u.inv) ≫ hb) ≫ j := by
  rw [← H.map_comp_assoc, hr, L.map_comp, H.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [hn]

private theorem transported_unit
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {B N X : C} {G G' Y : D} (e : G' ≅ G) (c : L.obj N ≅ G) (u : B ≅ N)
    (i : B ⟶ X) (gamma : G' ⟶ Y) (r : Y ⟶ L.obj X)
    (h : gamma ≫ r = (c ≪≫ e.symm).inv ≫ L.map (u.inv ≫ i)) :
    gamma ≫ r = (e ≪≫ c.symm ≪≫ L.mapIso u.symm).hom ≫ L.map i := by
  simpa only [Functor.map_comp, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using h

private theorem signed_unit_normalization
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {X Y Z : C} {G G' : D} (g : Y ≅ X) (v : Z ≅ X)
    (s : G ≅ L.obj Y) (e : G' ≅ G) (f : Z ⟶ Y) (hf : f ≫ g.hom = v.hom) :
    e.inv ≫ (e ≪≫ (L.mapIso g.symm ≪≫ s.symm).symm ≪≫ L.mapIso v.symm).hom ≫
      L.map f = s.hom := by
  have hf' : v.inv ≫ f = g.inv := by
    apply (cancel_mono g.hom).1
    rw [Category.assoc, hf, Iso.inv_hom_id, Iso.inv_hom_id]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← L.map_comp, hf', ← L.map_comp, Iso.hom_inv_id, L.map_id, Category.comp_id]

private theorem native_signed_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (A I : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) :
    let R := completedIntegralCommRingSheafUnrestricted l E Y
    let B := coefficientUnit.{t, u} Y R
    ∀ (f : ((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I)).obj B ⟶
        homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A
          (((totalTensor.{t, u} Y R).obj I).obj B)),
      IsSignedHomTensor.{t, u} Y R A I B f →
        f ≫ ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op A)).map (tensorUnitIso.{t, u} Y R I).hom =
            (tensorUnitIso.{t, u} Y R
              (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I)).hom := by
  dsimp only
  intro f hf
  have hunit := integral_signedHomTensor_unit l E Y A I f hf
  rw [← tensorUnitIso_eq_native l E Y I,
    ← tensorUnitIso_eq_native l E Y
      (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheafUnrestricted l E Y) A I)] at hunit
  exact hunit

private theorem principalKoszulTower_shape
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)).sections)
    (n : ℕ) :
    (∀ k : ℤ, k ≠ -1 → k ≠ 0 →
      IsZero (((principalKoszulTower R a).obj (op n)).X k)) ∧
    Nonempty ((((principalKoszulTower R a).obj (op n)).X (-1)) ≅
      SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) ∧
    Nonempty ((((principalKoszulTower R a).obj (op n)).X 0) ≅
      SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) := by
  let U := SheafOfModules.unit
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  let f := principalKoszulScalarComplex R a n
  constructor
  · intro k hk₁ hk₀
    change IsZero ((CochainComplex.mappingCone f).X k)
    apply (CochainComplex.mappingCone.isZero_X_iff f k).2
    exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U _ (by omega),
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U k hk₀⟩
  · constructor
    · change Nonempty ((CochainComplex.mappingCone f).X (-1) ≅ U)
      exact ⟨HomologicalComplex.homotopyCofiber.XIsoBiprod f (-1) 0 (by decide) ≪≫
        (isoBiprodZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U (-1)
          (by decide))).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 U⟩
    · change Nonempty ((CochainComplex.mappingCone f).X 0 ≅ U)
      exact ⟨HomologicalComplex.homotopyCofiber.XIsoBiprod f 0 1 (by decide) ≪≫
        (isoZeroBiprod (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U 1
          (by decide))).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 U⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

-- The final unit normalization unifies the bundled and unrestricted coefficient sheaves.
/-- The two reduction towers have separate tensor models preserving their units.
This asserts no isomorphism between Hom tensor Q_n and Hom into tensor Q_n.
The only comparison normalization is at the coefficient unit B=R[0].

Source: current blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1,
finite-free construction; Stacks Tags 06YY, 08J7, 07A6 and 08TC
(blueprint: lem-sf-integral-hom-tower-unit-models).

Proof: use Q_n=[R --pi^(n+1)--> R] in degrees -1,0, with transitions (pi,id).
The degree-zero inclusions B=R[0] -> Q_n form a cone. Their composites with
Q_n -> A_n are the ordinary quotient units. These quasi-isomorphisms follow
from regularity of pi on the completed coefficient sheaf and identification
of its quotient. Choose any complex A representing K and a K-injective I
representing Q(G). Tensor with Q_n computes each reduction, since Q_n is
bounded free; I tensor Q_n is K-injective because it is a finite cone of
shifts of I. The Hom complexes therefore give the first tower model.
Hom(A,I) tensor Q_n gives the second, using e and the K-flat computation on
q'. Naturality of these calculations for (pi,id) gives s and t. Applying
them also to B gives s0,t0. Naturality for B -> Q_n gives the two separate
augmentation equations hs and ht, using the ordinary scalar unit 1 tensor x
and the canonical resolution-independent augmentation. At B, both tensor
functors identify with their untensored complexes by the right unitor.
A map satisfying IsSignedHomTensor has coefficient degree zero, hence sign
one, and acts as the identity under these unitors: evaluate on every local
section, then use the Hom product projections and sheafification universal
property. Thus its localization identifies t0 with s0 after e inverse,
which is precisely the last displayed equality. None of this proves that
the signed comparison is invertible at Q_n. Zero inputs, n=0 and the empty
scheme cause no exception to the same constructions. -/
theorem reductionTower_unit_models
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let H := (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
    let B : CochainComplex (Modules.{t, u} Y R) ℤ :=
      (CochainComplex.singleFunctor (Modules.{t, u} Y R) 0).obj
      (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    ∃ (A I : CochainComplex (Modules.{t, u} Y R) ℤ)
      (Q : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ),
      (∀ n : ℕ,
        (∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero ((Q.obj (op n)).X k)) ∧
        Nonempty ((Q.obj (op n)).X (-1) ≅ (show Modules.{t, u} Y R from
          SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))) ∧
        Nonempty ((Q.obj (op n)).X 0 ≅ (show Modules.{t, u} Y R from
          SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))) ∧
      let S := (totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I) ⋙
          DerivedCategory.Q
      let T := (totalTensor.{t, u} Y R).obj I ⋙
        (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op A) ⋙ DerivedCategory.Q
      ∃ (ι : (Functor.const ℕᵒᵖ).obj B ⟶ Q)
        (s : integralReductionTower l E Y D hl P ⋙ H ≅ Q ⋙ T)
        (t : integralReductionTower l E Y D hl P' ≅ Q ⋙ S)
        (s0 : H.obj (DerivedCategory.Q.obj G) ≅ T.obj B)
        (t0 : DerivedCategory.Q.obj G' ≅ S.obj B),
        (∀ n : ℕ,
          H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
              s.hom.app (op n) = s0.hom ≫ T.map (ι.app (op n))) ∧
        (∀ n : ℕ,
          (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) ≫
              t.hom.app (op n) = t0.hom ≫ S.map (ι.app (op n))) ∧
        ∀ f : ((totalTensor.{t, u} Y R).obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I)).obj B ⟶
            homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A
              (((totalTensor.{t, u} Y R).obj I).obj B),
          IsSignedHomTensor.{t, u} Y R A I B f →
            e.inv ≫ t0.hom ≫ DerivedCategory.Q.map f = s0.hom := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let M := Modules.{t, u} Y R
  let : HasDerivedCategory M := HasDerivedCategory.standard _
  let H := (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
  let a := PrincipalKoszulStrictReplacement.uniformizer l E Y
  let Q := principalKoszulTower R a
  let B := coefficientUnit.{t, u} Y R
  let ι := (coefficientCone.{t, u} Y R a).π
  let Qplus := WithInitial.lift Q ι.app (by
    intro i j f
    exact (ι.naturality f).symm.trans (by simp))
  have hQplus (I : CochainComplex M ℤ) [I.IsKInjective] (n : WithInitial ℕᵒᵖ) :
      (((totalTensor.{t, u} Y R).obj I).obj (Qplus.obj n)).IsKInjective := by
    cases n with
    | star =>
      dsimp only [Qplus, WithInitial.lift]
      exact CochainComplex.isKInjective_of_iso (tensorUnitIso.{t, u} Y R I).symm
    | of n =>
      dsimp only [Qplus, WithInitial.lift, Q, principalKoszulTower,
        Functor.ofOpSequence, Functor.ofSequence]
      exact isKInjective_tensor_principalKoszul Y R a I n.unop
  obtain ⟨A, I, eI, ⟨h⟩⟩ := integralHom_kInjective_tensor_diagram Y R K G Qplus hQplus
  let TI := (totalTensor.{t, u} Y R).obj I
  let HA := (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := R)).obj (op A)
  let C := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I
  let ui := tensorUnitIso.{t, u} Y R I
  let uc := tensorUnitIso.{t, u} Y R C
  let s0 : H.obj (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj (HA.obj (TI.obj B)) :=
    H.mapIso eI.symm ≪≫ H.mapIso (DerivedCategory.Q.mapIso ui.symm) ≪≫
      h.app WithInitial.star
  let c : DerivedCategory.Q.obj C ≅ H.obj (DerivedCategory.Q.obj G) :=
    DerivedCategory.Q.mapIso (HA.mapIso ui.symm) ≪≫ s0.symm
  obtain ⟨rI, hrI⟩ := integralReductionTower_koszul_augmented_model l E Y D hl P G I q hq eI
  obtain ⟨rC, hrC⟩ := integralReductionTower_koszul_augmented_model l E Y D hl P' G' C q' hq'
    (c ≪≫ e.symm)
  let r := rI
  let r' := rC ≪≫ koszulTensorPresentation l E Y C
  have hr (n : ℕ) :
      (integralReductionTowerCone l E Y D hl q hq).π.app (op n) ≫
        r.hom.app (op n) = eI.inv ≫
          DerivedCategory.Q.map (ui.inv ≫ TI.map (ι.app (op n))) := by
    have hunit := hrI n
    rw [levelUnit_eq_tensor] at hunit
    exact hunit
  have hr' (n : ℕ) :
      (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) ≫
        r'.hom.app (op n) = (c ≪≫ e.symm).inv ≫
          DerivedCategory.Q.map (uc.inv ≫
            ((totalTensor.{t, u} Y R).obj C).map (ι.app (op n))) := by
    exact postcompose_model_unit _ _ _ _ _ _ (hrC n)
      (koszulTensorPresentation_unit l E Y C n)
  let s : integralReductionTower l E Y D hl P ⋙ H ≅
      Q ⋙ (TI ⋙ (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R)).obj (op A) ⋙ DerivedCategory.Q) :=
    Functor.isoWhiskerRight r H ≪≫ Functor.isoWhiskerLeft WithInitial.incl h
  let t0 : DerivedCategory.Q.obj G' ≅
      DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj C).obj B) :=
    e ≪≫ c.symm ≪≫ DerivedCategory.Q.mapIso uc.symm
  refine Exists.intro A ?_
  refine Exists.intro I ?_
  refine Exists.intro Q ?_
  refine And.intro ?_ ?_
  · intro n
    have hh := principalKoszulTower_shape Y R a n
    refine ⟨hh.1, ?_, ?_⟩
    · exact hh.2.1
    · exact hh.2.2
  · dsimp only
    refine Exists.intro ι ?_
    refine Exists.intro s ?_
    refine Exists.intro r' ?_
    refine Exists.intro s0 ?_
    refine Exists.intro t0 ?_
    refine And.intro ?_ (And.intro ?_ ?_)
    · intro n
      have hn : H.map (DerivedCategory.Q.map (TI.map (ι.app (op n)))) ≫
          h.hom.app (WithInitial.of (op n)) =
        h.hom.app WithInitial.star ≫
          DerivedCategory.Q.map (HA.map (TI.map (ι.app (op n)))) :=
        h.hom.naturality (WithInitial.homTo (op n))
      exact map_unit_naturality DerivedCategory.Q H
        ((integralReductionTowerCone l E Y D hl q hq).π.app (op n))
        (r.hom.app (op n)) eI ui (TI.map (ι.app (op n)))
        (h.hom.app WithInitial.star) (h.hom.app (WithInitial.of (op n)))
        (DerivedCategory.Q.map (HA.map (TI.map (ι.app (op n))))) (hr n) hn
    · intro n
      exact transported_unit DerivedCategory.Q e c uc
        (((totalTensor.{t, u} Y R).obj C).map (ι.app (op n)))
        ((integralReductionTowerCone l E Y D hl q' hq').π.app (op n))
        (r'.hom.app (op n)) (hr' n)
    · intro f hf
      have hfunit : f ≫ HA.map ui.hom = uc.hom := native_signed_unit l E Y A I f hf
      exact signed_unit_normalization DerivedCategory.Q (HA.mapIso ui) uc s0 e f hfunit

end WeilConjectures.IntegralHom
