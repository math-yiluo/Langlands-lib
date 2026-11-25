/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralKoszulQuotientUnits
import all WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorUnitSections
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.CategoryTheory.WithTerminal.Basic

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
attribute [local implicit_reducible] completedIntegralCoefficientSheaf

open CategoryTheory.MonoidalCategory
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local instance] countableColimits
  ordinaryTensorZero ordinaryTensorObjZero

private theorem normalized_augmented_unit
    {C : Type*} [Category* C] {P G N U V X Y Z : C}
    (q : P ≅ G) (e : N ≅ G) (up : U ≅ P) (un : V ≅ N) (r0 : X ≅ Z)
    (c0 : U ⟶ V) (cn : X ⟶ Y) (ap : U ⟶ X) (an : V ⟶ Y) (gamma : P ⟶ Z)
    (hc : c0 ≫ un.hom = up.hom ≫ q.hom ≫ e.inv)
    (hn : ap ≫ cn = c0 ≫ an) (hu : up.inv ≫ ap ≫ r0.hom = gamma) :
    (q.inv ≫ gamma) ≫ (r0.inv ≫ cn) = e.inv ≫ (un.inv ≫ an) := by
  have hc' : up.inv ≫ c0 = q.hom ≫ e.inv ≫ un.inv := by
    apply (cancel_mono un.hom).1
    rw [Category.assoc, hc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hn, ← Category.assoc up.inv c0, hc']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem localizedDiagram_iso
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F : C ⥤ (J ⥤ D)) (hF : W.IsInvertedBy F) (j : J)
    (u : F ⋙ (evaluation J D).obj j ≅ L)
    (X Y : C) (e : L.obj X ≅ L.obj Y) :
    ∃ a : F.obj X ≅ F.obj Y,
      a.hom.app j ≫ u.hom.app Y = u.hom.app X ≫ e.hom := by
  let G := Localization.lift F hF L
  let c := Localization.fac F hF L
  let v := Localization.liftNatIso L W (F ⋙ (evaluation J D).obj j) L
    (G ⋙ (evaluation J D).obj j) (𝟭 D) u
  let a := (c.app X).symm ≪≫ G.mapIso e ≪≫ c.app Y
  refine ⟨a, ?_⟩
  have hv (N : C) : v.hom.app (L.obj N) =
      (c.hom.app N).app j ≫ u.hom.app N := by
    simp only [v, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compRight, Localization.Lifting.id,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    change _ ≫ _ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  have hn := v.hom.naturality e.hom
  change (G.map e.hom).app j ≫ v.hom.app (L.obj Y) =
    v.hom.app (L.obj X) ≫ e.hom at hn
  rw [hv X, hv Y] at hn
  simp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [hn, ← Category.assoc, ← Category.assoc]
  rw [show (c.inv.app X).app j ≫ (c.hom.app X).app j = 𝟙 _ from
    (c.app X).inv_hom_id_app j, Category.id_comp]

private noncomputable def tensorDiagram
    {J : Type*} [Category* J]
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (S : J ⥤ CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex (Modules.{t, u} Y R) ℤ ⥤ (J ⥤ Derived.{t, u} Y R) where
  obj N := S ⋙ (totalTensor.{t, u} Y R).obj N ⋙ DerivedCategory.Q
  map f := Functor.whiskerRight
    (Functor.whiskerLeft S ((totalTensor.{t, u} Y R).map f)) DerivedCategory.Q
  map_id N := by ext n; simp
  map_comp f g := by ext n; simp

private theorem tensorDiagram_inverts
    {J : Type*} [Category* J]
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (S : J ⥤ CochainComplex (Modules.{t, u} Y R) ℤ)
    (hS : ∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R) (S.obj n)) :
    (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).IsInvertedBy
      (tensorDiagram.{t, u} Y R S) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective Y
  intro X X' f hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have h := kFlatTensorPreservesQuasiIsoIndependentCoefficients
    R (S.obj n) (hS n) f hf
  change IsIso (DerivedCategory.Q.map (((totalTensor.{t, u} Y R).map f).app (S.obj n)))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  exact h

attribute [local implicit_reducible] homComplex totalTensor coefficientTotalTensor
  evaluate projection
  homComplexπ moduleMonoidal coefficientUnit SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.Functor.map₂HomologicalComplex

attribute [local irreducible] tensorUnitIso homComplexFunctor
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard
  derivedInternalHomOfUniverses

attribute [local implicit_reducible] SheafOfModules.monoidalCategory

private theorem tensorUnitIso_eq_native
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (N : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) :
    tensorUnitIso.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y) N =
      (by exact PrincipalIntrinsicCompletion.tensorUnit l E Y N) := by
  unfold tensorUnitIso PrincipalIntrinsicCompletion.tensorUnit
  rfl

private theorem tensorUnit_kflat
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) (coefficientUnit.{t, u} Y R) := by
  intro Z hZ
  exact fun i ↦ (hZ i).of_iso (tensorUnitIso.{t, u} Y R Z).symm

private noncomputable def coefficientCone
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)).sections) :
    Cone (principalKoszulTower R a) where
  pt := coefficientUnit.{t, u} Y R
  π := NatTrans.ofOpSequence (fun n ↦ CochainComplex.mappingCone.inr
    (principalKoszulScalarComplex R a n)) (by
      intro n
      change CochainComplex.mappingCone.inr (principalKoszulScalarComplex R a n) =
        CochainComplex.mappingCone.inr (principalKoszulScalarComplex R a (n + 1)) ≫ _
      simp only [principalKoszulTower,
        Functor.ofOpSequence_map_homOfLE_succ, principalKoszulTransition]
      dsimp only [principalKoszulScalarComplex]
      rw [CochainComplex.mappingCone.map_eq_mapOfHomotopy,
        CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂]
      simp)

attribute [local implicit_reducible] coefficientCone NatTrans.ofOpSequence
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  principalAugmentation principalReduction principalQuotient principalKoszul
  principalKoszulScalarComplex principalKoszulTower

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingSheaf CategoryTheory.sheafCompose
  PrincipalKoszulStrictReplacement.tensorWith PrincipalKoszulStrictReplacement.sourceTower
  PrincipalKoszulStrictReplacement.residue
  IntegralOnSlice.Site IntegralOnSlice.siteCategory IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite IntegralOnSlice.projection
  SheafOfModules.restrictScalars completedIntegralCommRingProjectionUnrestricted
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  SheafOfModules.KFlatTotalTensorModel.tensor SheafOfModules.KFlatTotalTensorModel.monoidal

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence tensorScalarLevelIso

attribute [local implicit_reducible] tensorDiagram

private theorem levelUnit_eq_tensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (N : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) (n : ℕ) :
    PrincipalIntrinsicCompletion.levelUnit l E Y N n =
      (tensorUnitIso.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y) N).inv ≫
        ((totalTensor.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y)).obj N).map
          ((coefficientCone.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y)
            (PrincipalKoszulStrictReplacement.uniformizer l E Y)).π.app (op n)) := by
  rw [tensorUnitIso_eq_native l E Y N]
  rfl

private noncomputable def koszulTensorPresentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (N : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) :
    PrincipalKoszulStrictReplacement.sourceTower l E Y N ⋙ DerivedCategory.Q ≅
      principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E Y)
        (PrincipalKoszulStrictReplacement.uniformizer l E Y) ⋙
          (totalTensor.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y)).obj N ⋙
            DerivedCategory.Q := by
  refine NatIso.ofComponents (fun n ↦ Iso.refl _) ?_
  intro i j f
  exact (Category.comp_id _).trans (Category.id_comp _).symm

attribute [local irreducible] koszulTensorPresentation

private theorem koszulTensorPresentation_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (N : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) (n : ℕ) :
    DerivedCategory.Q.map (PrincipalIntrinsicCompletion.levelUnit l E Y N n) ≫
        (koszulTensorPresentation l E Y N).hom.app (op n) =
      DerivedCategory.Q.map
        ((tensorUnitIso.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y) N).inv ≫
          ((totalTensor.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y)).obj N).map
            ((coefficientCone.{t, u} Y (completedIntegralCommRingSheafUnrestricted l E Y)
              (PrincipalKoszulStrictReplacement.uniformizer l E Y)).π.app (op n))) := by
  unfold koszulTensorPresentation
  dsimp only [NatIso.ofComponents_hom_app, Iso.refl_hom]
  exact (Category.comp_id _).trans
    (congrArg DerivedCategory.Q.map (levelUnit_eq_tensor l E Y N n))

/-- The actual reduction tower on a K-flat resolution has a Koszul tensor model on
any representative, with the prescribed augmentation at every level.

Source: paragraph 1 of the current blueprint `lem-coef-integral-hom-reduction.proof.md`
(blueprint: lem-sf-integral-koszul-augmented-model).

Proof: append the coefficient unit to the Koszul diagram. Its terms are K-flat,
so tensoring with this entire diagram descends through localization. The right
unitor identifies evaluation at the added vertex with the localization functor.
Descending that natural isomorphism makes the transported apex equal to e.
Restrict to the original tower and compose with the comparison preserving the
actual quotient units on P. Naturality at each added-vertex arrow gives the
augmentation equation. This requires no flatness of N and works also for N=0. -/
theorem integralReductionTower_koszul_augmented_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P G N : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (e : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj G) :
    ∃ r : integralReductionTower l E Y D hl P ≅
        PrincipalKoszulStrictReplacement.sourceTower l E Y N ⋙ DerivedCategory.Q,
      ∀ n : ℕ,
        (integralReductionTowerCone l E Y D hl q hq).π.app (op n) ≫
            r.hom.app (op n) =
          e.inv ≫ DerivedCategory.Q.map (PrincipalIntrinsicCompletion.levelUnit l E Y N n) := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let : HasDerivedCategory (Modules.{t, u} Y R) := HasDerivedCategory.standard _
  let a := PrincipalKoszulStrictReplacement.uniformizer l E Y
  let Q := principalKoszulTower R a
  let B := coefficientUnit.{t, u} Y R
  let Qplus := WithInitial.lift Q (coefficientCone.{t, u} Y R a).π.app (by
    intro i j f
    exact ((coefficientCone.{t, u} Y R a).π.naturality f).symm.trans (by simp))
  have hQ (n : ℕᵒᵖ) :
      CochainComplex.IsKFlatIndependentCoefficients (R := R) (Q.obj n) := by
    have : (Q.obj n).IsStrictlyLE 0 :=
      PrincipalKoszulStrictReplacement.koszul_bounded l E Y n.unop
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      R (Q.obj n) 0 (PrincipalKoszulStrictReplacement.koszul_flat l E Y n.unop)
  have hplus (n : WithInitial ℕᵒᵖ) :
      CochainComplex.IsKFlatIndependentCoefficients (R := R) (Qplus.obj n) := by
    cases n with
    | star => exact tensorUnit_kflat.{t, u} Y R
    | of n => exact hQ n
  let F := tensorDiagram.{t, u} Y R Qplus
  let u : F ⋙ (evaluation (WithInitial ℕᵒᵖ) (Derived.{t, u} Y R)).obj .star ≅
      DerivedCategory.Q := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · change DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj N).obj B) ≅
        DerivedCategory.Q.obj N
      exact DerivedCategory.Q.mapIso (tensorUnitIso.{t, u} Y R N)
    · intro N N' f
      change DerivedCategory.Q.map (((totalTensor.{t, u} Y R).map f).app B) ≫
          DerivedCategory.Q.map (tensorUnitIso.{t, u} Y R N').hom =
        DerivedCategory.Q.map (tensorUnitIso.{t, u} Y R N).hom ≫ DerivedCategory.Q.map f
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map (tensorUnitIso_naturality Y R f)
  have : QuasiIso q := hq.1
  let ePN := asIso (DerivedCategory.Q.map q) ≪≫ e.symm
  obtain ⟨c, hc⟩ := localizedDiagram_iso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)) F
    (tensorDiagram_inverts.{t, u} Y R Qplus hplus) .star u P N ePN
  let cQ : PrincipalKoszulStrictReplacement.sourceTower l E Y P ⋙ DerivedCategory.Q ≅
      PrincipalKoszulStrictReplacement.sourceTower l E Y N ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun n ↦ c.app (WithInitial.of n)) (by
      intro i j f
      exact c.hom.naturality (WithInitial.incl.map f))
  obtain ⟨r0, hunit⟩ := integralReductionTower_koszul_quotient_units l E Y D hl P hq.2
  let r := r0.symm ≪≫ cQ
  refine ⟨r, ?_⟩
  intro n
  have hn := c.hom.naturality (WithInitial.homTo (op n))
  have hu : DerivedCategory.Q.map (tensorUnitIso.{t, u} Y R P).inv ≫
      DerivedCategory.Q.map (((totalTensor.{t, u} Y R).obj P).map
        ((coefficientCone.{t, u} Y R a).π.app (op n))) ≫ r0.hom.app (op n) =
      DerivedCategory.Q.map (integralTowerUnit l E Y D hl P n) := by
    rw [← Functor.map_comp_assoc, ← levelUnit_eq_tensor l E Y P n]
    exact hunit n
  have hbase : c.hom.app WithInitial.star ≫
      DerivedCategory.Q.map (tensorUnitIso.{t, u} Y R N).hom =
    DerivedCategory.Q.map (tensorUnitIso.{t, u} Y R P).hom ≫
      DerivedCategory.Q.map q ≫ e.inv := hc
  have hn' : DerivedCategory.Q.map (((totalTensor.{t, u} Y R).obj P).map
      ((coefficientCone.{t, u} Y R a).π.app (op n))) ≫
      c.hom.app (WithInitial.of (op n)) =
    c.hom.app WithInitial.star ≫ DerivedCategory.Q.map
      (((totalTensor.{t, u} Y R).obj N).map
        ((coefficientCone.{t, u} Y R a).π.app (op n))) := hn
  rw [levelUnit_eq_tensor l E Y N n, Functor.map_comp]
  exact normalized_augmented_unit (integralTowerAugmentationIso l E Y D hl q hq) e
    (DerivedCategory.Q.mapIso (tensorUnitIso.{t, u} Y R P))
    (DerivedCategory.Q.mapIso (tensorUnitIso.{t, u} Y R N)) (r0.app (op n))
    (c.hom.app WithInitial.star) (c.hom.app (WithInitial.of (op n)))
    (DerivedCategory.Q.map (((totalTensor.{t, u} Y R).obj P).map
      ((coefficientCone.{t, u} Y R a).π.app (op n))))
    (DerivedCategory.Q.map (((totalTensor.{t, u} Y R).obj N).map
      ((coefficientCone.{t, u} Y R a).π.app (op n))))
    (DerivedCategory.Q.map (integralTowerUnit l E Y D hl P n)) hbase hn' hu

end WeilConjectures.IntegralHom
