/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Comparison of the two normalized integral pullback augmentations

Source: Stacks Project, Tags 03EL, 06YY and 0941, and the coefficient-line
pullback convention of the orientation datum.
(blueprint: lem-sf-integral-pullback-augmentation-ambient)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
namespace WeilConjectures
attribute [local irreducible] IntegralAmbient.pull IntegralAmbient.coefficientMap
  IntegralOnSlice.roosUnit IntegralAmbient.pullOperationUnit proEtaleRingModulePullback

private theorem cocone_hom_ext {A : Type*} [Category* A] [Abelian A]
    {K L P : CochainComplex A ℤ} (phi : K ⟶ L)
    {f g : P ⟶ CochainComplex.mappingCocone phi}
    (hfst : f ≫ CochainComplex.mappingCocone.fst phi =
      g ≫ CochainComplex.mappingCocone.fst phi)
    (hsnd : ∀ i : ℤ, f.f i ≫ (CochainComplex.mappingCocone.snd phi).v
      i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd phi).v i (i - 1) (by omega)) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  let inc := (CochainComplex.mappingCocone.inl phi).v i i (by omega)
  let inc' := (CochainComplex.mappingCocone.inr phi).1.v (i - 1) i (by omega)
  let fst := (CochainComplex.mappingCocone.fst phi).f i
  let snd := (CochainComplex.mappingCocone.snd phi).v i (i - 1) (by omega)
  have hi : fst ≫ inc + snd ≫ inc' = 𝟙 _ :=
    CochainComplex.mappingCocone.id_X phi i (i - 1) (by omega)
  have hf : f.f i ≫ fst = g.f i ≫ fst := congrArg (fun h ↦ h.f i) hfst
  have hs : f.f i ≫ snd = g.f i ≫ snd := hsnd i
  have he : f.f i ≫ (fst ≫ inc + snd ≫ inc') =
      g.f i ≫ (fst ≫ inc + snd ≫ inc') := by
    simpa only [Preadditive.comp_add, ← Category.assoc] using
      congrArg₂ (fun a b ↦ a + b)
        (congrArg (fun a ↦ a ≫ inc) hf) (congrArg (fun a ↦ a ≫ inc') hs)
  calc
    f.f i = f.f i ≫ (fst ≫ inc + snd ≫ inc') :=
      (Category.comp_id _).symm.trans (congrArg (fun a ↦ f.f i ≫ a) hi.symm)
    _ = g.f i ≫ (fst ≫ inc + snd ≫ inc') := he
    _ = g.f i := (congrArg (fun a ↦ g.f i ≫ a) hi).trans (Category.comp_id _)

/-- The explicit scalar/root pullback augmentation is the ambient completion unit
under the canonical comparison of ordinary module inverse images. No completeness
or flatness assumption on the complex is involved.

Source: Stacks Project, Tags 03EL, 06YY and 0941; the normalization conventions of
`theorem-smooth-purity-all-admissible-coefficients`, arbitrary scheme pullback.
(blueprint: lem-sf-integral-pullback-augmentation-ambient)

Proof: The projection characterizations of `sfCompletedCoefficientMap` and
`IntegralAmbient.coefficientMap` identify the structural ring maps of the two
module direct images. They therefore have the same right adjoint. Uniqueness of
left adjoints gives an isomorphism of their ordinary module pullbacks whose
adjunction-unit square commutes. Extend that isomorphism termwise to complexes.
The unit square says that each source section inserted by `moduleSection` maps
to the corresponding `IntegralAmbient.pullSection`. The quotient augmentation
sends this section to its scalar tensor with one. By `pullTowerModel`, the tower
comparison sends that tensor to the published finite pullback generator. Thus
the composite on the right has exactly the first-component equations of
`existsUnique_pullbackAugmentation`. Its second component is zero by
`pullOperationUnit_coordinates`, also after precomposition by the comparison.
The two coordinate equalities and the mapping-cocone identity give equality of
the actual chain maps. The argument uses adjunctions and projections, so also applies
to the empty scheme and to zero complexes. -/
theorem integralPullbackAugmentation_ambient
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    letI : (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
        FrobeniusCoefficientTwists.modulePull l E g).PreservesZeroMorphisms :=
      @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
          FrobeniusCoefficientTwists.modulePull l E g)
        (proEtaleRingModulePullback_additive g
          ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull g))
    letI : (IntegralAmbient.pull l E g).PreservesZeroMorphisms :=
      @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (IntegralAmbient.pull l E g) (IntegralAmbient.pull_additive l E g)
    ∃ b : (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
        FrobeniusCoefficientTwists.modulePull l E g) ≅ IntegralAmbient.pull l E g,
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        (FrobeniusCoefficientTwists.pullbackAugmentation l E g).app P =
          ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) ≫
            IntegralAmbient.pullOperationUnit l E g P := by
  classical
  let F : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
    FrobeniusCoefficientTwists.modulePull l E g
  let G : integralTowerModules l E X ⥤ integralTowerModules l E Y :=
    proEtaleRingModuleDirectImage g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull g)
  let : F.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ F
      (proEtaleRingModulePullback_additive g
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull g))
  let : (IntegralAmbient.pull l E g).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (IntegralAmbient.pull l E g) (IntegralAmbient.pull_additive l E g)
  let := proEtaleBaseChange_isContinuous g
  have hc : sfCompletedCoefficientMap l E g = IntegralAmbient.coefficientMap l E g := by
    apply (IntegralAmbient.coefficientMap_existsUnique l E g).unique
    · intro n
      exact (sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n
    · simpa only [IntegralAmbient.coefficientMap] using
        (IntegralAmbient.coefficientMap_existsUnique l E g).exists.choose_spec
  let adj : F ⊣ G :=
    proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)
  have hadj : proEtaleRingDirectImageMap g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull g) = sfCompletedCoefficientMap l E g :=
    (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E g)
  let he := congrArg (fun c : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X) ↦
    (⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
      completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (proEtaleSheafDirectImage g RingCat.{u + 1}).obj
          (completedIntegralCoefficientSheafUnrestricted l E X))) (hadj.trans hc)
  let e : G ≅ IntegralAmbient.push l E g :=
    by
      dsimp only [G, proEtaleRingModuleDirectImage, IntegralAmbient.push]
      exact SheafOfModules.pushforwardCongr (F := proEtaleBaseChange g) he
  let a := (IntegralAmbient.adjunction l E g).ofNatIsoRight e.symm
  let b := adj.leftAdjointUniq a
  have hb (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
      (b.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (FrobeniusCoefficientTwists.moduleSection l E g M V x) =
      IntegralAmbient.pullSection l E g M V x := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app adj a M
    exact congrArg (fun f ↦ f.val.app (op V) x) h
  refine ⟨b, ?_⟩
  intro P
  let T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ :=
    (integralOperationsPullbackTowerFunctor l E g).obj P
  let phi := towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
    (integralOperationsTowerStep T)
  let M : CochainComplex (integralTowerModules l E X) ℤ :=
    (IntegralAmbient.pullComplex l E g).obj P
  let S : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ :=
    (IntegralOnSlice.tower l E X none).obj M
  let q (n : ℕ) : M ⟶ S.obj (op n) :=
    ((IntegralOnSlice.augmentation l E X none).app M).app (op n)
  let t (n : ℕ) : S.obj (op n) ⟶ T.obj (op n) :=
    ((IntegralAmbient.pullTowerIso l E g).hom.app P).app (op n)
  let c := (NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P
  let eta : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      CochainComplex.mappingCocone phi :=
    (FrobeniusCoefficientTwists.pullbackAugmentation l E g).app P
  let unit : M ⟶
      CochainComplex.mappingCocone phi := IntegralAmbient.pullOperationUnit l E g P
  let eta' := c ≫ unit
  have hfst : eta ≫ CochainComplex.mappingCocone.fst phi =
      eta' ≫ CochainComplex.mappingCocone.fst phi := by
    dsimp only [eta']
    have hh : unit ≫ CochainComplex.mappingCocone.fst phi =
        Limits.Pi.lift q ≫ Limits.Pi.map t :=
      (IntegralAmbient.pullOperationUnit_coordinates l E g P).1
    rw [Category.assoc, hh]
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc]
    apply HomologicalComplex.hom_ext
    intro i
    let f : F.obj (P.X i) ⟶ (T.obj (op n)).X i :=
      (eta ≫ CochainComplex.mappingCocone.fst phi ≫
        Pi.π (fun n ↦ T.obj (op n)) n).f i
    let h : F.obj (P.X i) ⟶ (T.obj (op n)).X i := (c ≫ q n ≫ t n).f i
    change f = h
    apply (adj.homEquiv (P.X i) _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext V x
    let W := op ((proEtaleBaseChange g).obj V.unop)
    let sec := FrobeniusCoefficientTwists.moduleSection l E g (P.X i) V.unop x
    let pulled := IntegralAmbient.pullSection l E g (P.X i) V.unop x
    let z := IntegralOnSlice.generator l E X none n
      ((IntegralAmbient.pull l E g).obj (P.X i)) W 1 pulled
    change (((eta ≫ CochainComplex.mappingCocone.fst phi ≫
        Pi.π (fun n ↦ T.obj (op n)) n).f i).val.app W) sec =
      ((t n).f i).val.app W (((q n).f i).val.app W
        ((b.hom.app (P.X i)).val.app W sec))
    have hleft : (((eta ≫ CochainComplex.mappingCocone.fst phi ≫
        Pi.π (fun n ↦ T.obj (op n)) n).f i).val.app W) sec =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V.unop
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V.unop) 1 x) := by
      dsimp only [eta, W, sec, F, T, phi,
        FrobeniusCoefficientTwists.pullbackAugmentation, HomologicalComplex.comp_f]
      exact (FrobeniusCoefficientTwists.existsUnique_pullbackAugmentation
        l E g).exists.choose_spec.1 P i n V.unop x
    have hq : ((q n).f i).val.app W pulled = z := by
      dsimp only [q, IntegralOnSlice.augmentation]
      exact (IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
        M n i W pulled
    have ht : ((t n).f i).val.app W z =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V.unop
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V.unop) 1 x) := by
      have h := (IntegralAmbient.pullTowerModel l E g).exists.choose_spec
        P n i V.unop 1 x
      have hu : IntegralAmbient.finitePullSection l E g n P i V.unop 1 x =
          integralOperationsPullbackGenerator l E g n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V.unop
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V.unop) 1 x) := by
        let N : integralOperationsFiniteModules l E X n :=
          (integralOperationsLevelPullback l E g n).obj
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)
        let y : N.val.obj W := integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V.unop
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V.unop) 1 x)
        change (1 : (integralCoefficientSheaf l E X n).obj.obj W) • y = y
        exact one_smul _ _
      dsimp only [t, IntegralAmbient.pullTowerIso]
      exact h.trans hu
    exact hleft.trans ((congrArg
      (fun y ↦ ((t n).f i).val.app W (((q n).f i).val.app W y))
      (hb (P.X i) V.unop x)).trans
        ((congrArg (fun y ↦ ((t n).f i).val.app W y) hq).trans ht)).symm
  have hsnd (i : ℤ) : eta.f i ≫ (CochainComplex.mappingCocone.snd phi).v
      i (i - 1) (by omega) =
      eta'.f i ≫ (CochainComplex.mappingCocone.snd phi).v i (i - 1) (by omega) := by
    rw [show eta.f i ≫ (CochainComplex.mappingCocone.snd phi).v
      i (i - 1) (by omega) = 0 from
      by
        dsimp only [eta, F, T, phi]
        unfold FrobeniusCoefficientTwists.pullbackAugmentation
        exact (FrobeniusCoefficientTwists.existsUnique_pullbackAugmentation
          l E g).exists.choose_spec.2 P i]
    have hu : unit.f i ≫ (CochainComplex.mappingCocone.snd phi).v
        i (i - 1) (by omega) = 0 :=
      (IntegralAmbient.pullOperationUnit_coordinates l E g P).2 i (i - 1) (by omega)
    dsimp only [eta']
    rw [HomologicalComplex.comp_f, Category.assoc, hu, comp_zero]
  change eta = eta'
  exact cocone_hom_ext phi hfst hsnd

end WeilConjectures
