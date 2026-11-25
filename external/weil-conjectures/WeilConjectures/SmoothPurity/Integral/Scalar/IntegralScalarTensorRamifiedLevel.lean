/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels

import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralPrincipalUnitCriterion
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.FiniteFreeQuotientRoosComparison
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralOrdinaryTensorChain

/-! # The ramified finite tensor level comparison

Source: Stacks 03EL, 07A4, 0941 and 08TC; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-pur-integral-scalar-tensor-ramified-level).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective PrincipalKoszulStrictReplacement.siteSmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open CategoryTheory.PrincipalQuotientCompletion

attribute [local irreducible] quotientTower quotientMap

private theorem conjugate_normalization
    {C : Type a} [Category.{b} C] {D : Type a'} [Category.{b'} D]
    (F : C ⥤ D) {X A B : C} {Y Z : D} (i : A ≅ B)
    (r : F.obj A ≅ Y) (j : Y ≅ Z) (q : X ⟶ A) (t : X ⟶ B)
    (s : F.obj X ⟶ Y) (ht : q ≫ i.hom = t) (hr : F.map q ≫ r.hom = s) :
    F.map t ≫ (F.mapIso i.symm ≪≫ r ≪≫ j).hom = s ≫ j.hom := by
  rw [← ht]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, F.map_comp,
    Category.assoc, ← F.map_comp_assoc, i.hom_inv_id, F.map_id, Category.id_comp]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ j.hom) hr

private theorem principal_tower (W : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    ∃ a : ((quotientTower (completedIntegralCommRingSheafUnrestricted l E W)
        (PrincipalKoszulStrictReplacement.uniformizer l E W)).obj P).asFunctor ≅
      (IntegralOnSlice.tower l E W none).obj P,
      ∀ n, quotientMap (completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W) P n ≫ a.hom.app (op n) =
        ((IntegralOnSlice.augmentation l E W none).app P).app (op n) := by
  exact quotient_tower_comparison _ _ P _
    ((IntegralOnSlice.augmentation l E W none).app P)
    (quotient_level_comparison l E W P)

private theorem ordinary_model (W : AlgebraicGeometry.Scheme.{u}) :
    ∃ D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
        u + 2, u + 2} (integralCompletedScalarMap l E L ι W),
      D.E = integralOrdinaryScalar l E L ι W := by
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u + 1, u,
    u + 1, u + 2, u + 2} (integralCompletedScalarMap l E L ι W)
  refine ⟨D, ?_⟩
  refine CategoryTheory.Functor.ext
    (fun M ↦ (D.obj_eq M).trans (integralOrdinaryScalar_obj l E L ι W M).symm) ?_
  intro M N f
  rw [D.map_eq, integralOrdinaryScalar_map]
  simp

private theorem ramified_reduction (W : AlgebraicGeometry.Scheme.{u}) :
    ∃ (e : ℕ) (_ : 1 ≤ e),
      ∀ (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ),
      ∃ d : ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj
          (((IntegralOnSlice.tower l E W none).obj P).obj (op n)) ≅
        ((IntegralOnSlice.tower l L W none).obj
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)).obj
            (op (e * (n + 1) - 1)),
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
            (((IntegralOnSlice.augmentation l E W none).app P).app (op n)) ≫ d.hom =
          ((IntegralOnSlice.augmentation l L W none).app
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)).app
              (op (e * (n + 1) - 1)) := by
  classical
  obtain ⟨D, hD⟩ := ordinary_model l E L ι W
  rcases D with @⟨G, hG, hmG, haG, hpG, T, hT, ε, huniv, htri, hcomputes⟩
  change G = integralOrdinaryScalar l E L ι W at hD
  subst G
  let D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} (integralCompletedScalarMap l E L ι W) :=
    { E := integralOrdinaryScalar l E L ι W, obj_eq := hG, map_eq := hmG,
      additive := haG, preserves := hpG, T := T, pointwise := hT, ε := ε,
      universal := huniv, triangulated := htri, computes := hcomputes }
  have hc : completedCoefficientMap l E L ι W = integralCompletedScalarMap l E L ι W := by
    apply (integralCompletedScalarMap_existsUnique l E L ι W).unique
    · exact (completedCoefficientMap_existsUnique l E L ι W).exists.choose_spec
    · unfold integralCompletedScalarMap
      exact (integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec
  obtain ⟨uS, e, he, hu, hr⟩ := scalar_ramification l E L ι W
  rw [hc] at hr
  have : PreservesFiniteColimits D.E := integralOrdinaryScalar_finiteColimits l E L ι W
  obtain ⟨β, hβ⟩ := balancedTower D
    (PrincipalKoszulStrictReplacement.uniformizer l E W)
    (PrincipalKoszulStrictReplacement.uniformizer l L W) uS hu e he hr
  refine ⟨e, he, ?_⟩
  intro P n
  let F := (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
  obtain ⟨a, ha⟩ := principal_tower l E W P
  obtain ⟨b, hb⟩ := principal_tower l L W (F.obj P)
  let d := F.mapIso (a.app (op n)).symm ≪≫ (β P).app (op n) ≪≫
    b.app (op (e * (n + 1) - 1))
  refine ⟨d, ?_⟩
  exact (conjugate_normalization F (a.app (op n)) ((β P).app (op n))
    (b.app (op (e * (n + 1) - 1))) _ _ _ (ha n) (hβ P n)).trans
      (hb (e * (n + 1) - 1))

/-- Scalar extension of one finite tensor level is a later target tensor level.
Source: Stacks Tags 03EL and 07A4; the cofinal uniformizer calculation in
lem-pur-integral-scalar-tensor-chain-quasi-iso, proof steps 1 and 2.
(blueprint: lem-pur-integral-scalar-tensor-ramified-level).

Proof: let e be the positive ramification index of L/E. The image of the chosen
E-uniformizer generates the e-th power of the L-uniformizer ideal. Put
m = e * (n + 1) - 1, so m >= n. Completed constant-sheaf reduction identifies
O_L tensor over O_E with O_E/(pi_E^(n+1)) with O_L/(pi_L^(m+1)).
Use tensorTowerModel to identify each finite tensor with reduction of the
ordinary direct-sum total tensor. Associate the coefficient tensor factors,
apply the preceding quotient identification, and use the normalized ordinary
scalar tensor isomorphism. These are isomorphisms of complexes: tensor
association commutes with both signed differentials and scalar extension
preserves the coproduct totalization. Their composite sends the displayed
pure generator to the displayed pure generator. This is an ordinary balanced
tensor calculation and requires neither flatness nor boundedness of P,Q.
For an unramified extension take m=n. For either zero factor, or the empty
site, the same maps are the unique isomorphisms of zero complexes. -/
theorem integralScalarTensorRamifiedLevel (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    ∃ (m : ℕ) (_h : n ≤ m)
      (d : ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsTensorLevel l E W n).obj (P, Q)) ≅
        (integralOperationsTensorLevel l L W m).obj
          ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))),
      ∀ (p q : ℤ) (U : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (d.hom.f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W _ U 1
            (integralOperationsTotalTensorSection l E W n P Q p q U
              (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
              (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
        integralOperationsTotalTensorSection l L W m
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) p q U
          (unrestrictedIntegralTensorSection l L W m
            ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
            (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
          (unrestrictedIntegralTensorSection l L W m
            ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
            (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)) := by
  classical
  let F := (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
  let TE := coefficientTotalTensor.{u, u + 1, u}
    (AlgebraicGeometry.Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let TL := coefficientTotalTensor.{u, u + 1, u}
    (AlgebraicGeometry.Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l L W)
  obtain ⟨e, he, hred⟩ := ramified_reduction l E L ι W
  let m := e * (n + 1) - 1
  have hnm : n ≤ m := by
    have h := Nat.mul_le_mul_right (n + 1) he
    simp only [one_mul] at h
    dsimp only [m]
    omega
  obtain ⟨a, ha, _⟩ := IntegralAmbient.tensorTowerModel l E W
  obtain ⟨b, hb, _⟩ := IntegralAmbient.tensorTowerModel l L W
  dsimp only [IntegralAmbient.tensorTower, Functor.comp_obj] at a ha b hb
  obtain ⟨κ, hκ, _⟩ := normalizedIntegralOrdinaryTensorChain l E L ι W
  obtain ⟨r, hr⟩ := hred (TE.obj (P, Q)) n
  let an := (a.app (P, Q)).app (op n)
  let bm := (b.app (F.obj P, F.obj Q)).app (op m)
  let RL := IntegralOnSlice.tower l L W none ⋙
    (evaluation ℕᵒᵖ (CochainComplex (integralTowerModules l L W) ℤ)).obj (op m)
  let d := F.mapIso an.symm ≪≫ r ≪≫ RL.mapIso (κ.app (P, Q)) ≪≫ bm
  let tE := (((IntegralOnSlice.augmentation l E W none).app
    (TE.obj (P, Q))).app (op n)) ≫ an.hom
  let tL := (((IntegralOnSlice.augmentation l L W none).app
    (TL.obj (F.obj P, F.obj Q))).app (op m)) ≫ bm.hom
  have hcomp : F.map tE ≫ d.hom = (κ.hom.app (P, Q)) ≫ tL := by
    have hn := congrArg (fun k ↦ k.app (op m))
      ((IntegralOnSlice.augmentation l L W none).naturality (κ.hom.app (P, Q)))
    change (κ.hom.app (P, Q)) ≫
        (((IntegralOnSlice.augmentation l L W none).app
          (TL.obj (F.obj P, F.obj Q))).app (op m)) =
      (((IntegralOnSlice.augmentation l L W none).app
        (F.obj (TE.obj (P, Q)))).app (op m)) ≫ RL.map (κ.hom.app (P, Q)) at hn
    exact (conjugate_normalization F an r (RL.mapIso (κ.app (P, Q)) ≪≫ bm)
      _ tE _ rfl hr).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f ↦ f ≫ bm.hom) hn.symm).trans (Category.assoc _ _ _)))
  refine ⟨m, hnm, d, ?_⟩
  intro p q U x y
  have hE : (tE.f (p + q)).val.app U
      (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        P Q p q (p + q) rfl U x y) =
      integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y) := by
    change (an.hom.f (p + q)).val.app U
      (((((IntegralOnSlice.augmentation l E W none).app
        (TE.obj (P, Q))).app (op n)).f (p + q)).val.app U _) = _
    have hu := (IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec
      (TE.obj (P, Q)) n (p + q) U
      (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        P Q p q (p + q) rfl U x y)
    let f : ((((IntegralOnSlice.tower l E W none).obj
        (TE.obj (P, Q))).obj (op n)).X (p + q)) ⟶
        ((((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj
          (op n)).X (p + q)) := by
      change ((((IntegralAmbient.tensorTower l E W).obj (P, Q)).obj
        (op n)).X (p + q)) ⟶ _
      exact ((a.hom.app (P, Q)).app (op n)).f (p + q)
    have hv := congrArg (f.val.app U) hu
    dsimp only [f] at hv
    unfold IntegralOnSlice.augmentation
    exact hv.trans (ha P Q n p q U 1 x y)
  have hL : (tL.f (p + q)).val.app U
      (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l L W)
        (F.obj P) (F.obj Q) p q (p + q) rfl U
        (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
        (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)) =
      integralOperationsTotalTensorSection l L W m (F.obj P) (F.obj Q) p q U
        (unrestrictedIntegralTensorSection l L W m
          ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
        (unrestrictedIntegralTensorSection l L W m
          ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)) := by
    change (bm.hom.f (p + q)).val.app U
      (((((IntegralOnSlice.augmentation l L W none).app
        (TL.obj (F.obj P, F.obj Q))).app (op m)).f (p + q)).val.app U _) = _
    have hu := (IntegralOnSlice.augmentation_existsUnique l L W none).exists.choose_spec
      (TL.obj (F.obj P, F.obj Q)) m (p + q) U
      (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l L W)
        (F.obj P) (F.obj Q) p q (p + q) rfl U
        (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
        (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y))
    let f : ((((IntegralOnSlice.tower l L W none).obj
        (TL.obj (F.obj P, F.obj Q))).obj (op m)).X (p + q)) ⟶
        ((((integralOperationsTensorTowerFunctor l L W).obj (F.obj P, F.obj Q)).obj
          (op m)).X (p + q)) := by
      change ((((IntegralAmbient.tensorTower l L W).obj (F.obj P, F.obj Q)).obj
        (op m)).X (p + q)) ⟶ _
      exact ((b.hom.app (F.obj P, F.obj Q)).app (op m)).f (p + q)
    have hv := congrArg (f.val.app U) hu
    dsimp only [f] at hv
    unfold IntegralOnSlice.augmentation
    exact hv.trans (hb (F.obj P) (F.obj Q) m p q U 1 _ _)
  let z := coefficientTensorGenerator.{u, u + 1, u}
    (AlgebraicGeometry.Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y
  have hz := congrArg (fun k ↦ (k.f (p + q)).val.app U
    (integralOrdinaryTensorSection l E L ι W _ U 1 z)) hcomp
  change (d.hom.f (p + q)).val.app U
      (((integralOrdinaryScalar l E L ι W).map (tE.f (p + q))).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U 1 z)) =
    (tL.f (p + q)).val.app U
      (((κ.hom.app (P, Q)).f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U 1 z)) at hz
  have hs := scalar_map_tensor l E L ι W (tE.f (p + q)) U 1 z
  have ht := hκ P Q p q U x y
  have hz' := (congrArg ((d.hom.f (p + q)).val.app U) hs).symm.trans
    (hz.trans (congrArg ((tL.f (p + q)).val.app U) ht))
  exact (congrArg (fun v ↦ (d.hom.f (p + q)).val.app U
    (integralOrdinaryTensorSection l E L ι W _ U 1 v)) hE).symm.trans (hz'.trans hL)

end WeilConjectures
