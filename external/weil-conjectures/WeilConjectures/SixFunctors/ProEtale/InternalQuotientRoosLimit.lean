/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import all WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion

/-! # The augmented actual Roos complex after exact coefficient transport

Source: Stacks Tags 0941 and 099M; integral-models proof (1).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
attribute [local irreducible] IntegralConstantModel.pointComparison upperStarFromPoint
attribute [local irreducible] IntegralModelsStacks.smallModules
attribute [local irreducible] Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
local instance roosLimitDerived :
    HasDerivedCategory (ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _
local instance roosLimitTowerDerived :
    HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _

private theorem augmentedCoconeIso
    {C : Type*} [Category* C] [Abelian C]
    (V P : CochainComplex C ℤ) (t t' : V ⟶ V) (ht : t = t')
    (a : P ⟶ V) (ha : a ≫ t' = 0)
    (α : P ⟶ AdicCompletion.genericRoos V t)
    (hα : ∀ i, α.f i = biprod.lift (a.f i) 0) :
    α ≫ ((AdicCompletion.genericCoconeIso V t).symm ≪≫
      eqToIso (congrArg (fun f : V ⟶ V ↦ CochainComplex.mappingCocone f) ht)).hom =
      CochainComplex.mappingCocone.lift t' a 0 (by simp [ha]) := by
  subst t'
  apply (cancel_mono (AdicCompletion.genericCoconeIso V t).hom).mp
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Iso.symm_hom, Category.comp_id,
    Category.assoc, Iso.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro i
  rw [hα]
  change biprod.lift (a.f i) 0 =
    (CochainComplex.mappingCocone.lift t a 0 _).f i ≫
      (AdicCompletion.genericCoconeCoordinateIso V t i).hom
  apply biprod.hom_ext
  · dsimp only [AdicCompletion.genericCoconeCoordinateIso]
    erw [biprod.lift_fst, Category.assoc, biprod.lift_fst,
      CochainComplex.mappingCocone.lift_f_fst_f]
  · dsimp only [AdicCompletion.genericCoconeCoordinateIso]
    erw [biprod.lift_snd, Category.assoc, biprod.lift_snd, Preadditive.comp_neg,
      CochainComplex.mappingCocone.lift_f_snd_v]
    simp

private theorem compatibleFamily
    {C : Type*} [Category* C] (T : ℕᵒᵖ ⥤ C) (P : C)
    (v : (Functor.const ℕᵒᵖ).obj P ⟶ T) (n : ℕ) :
    v.app (op (n + 1)) ≫ T.map (homOfLE (Nat.le_succ n)).op = v.app (op n) := by
  have h := v.naturality (homOfLE (Nat.le_succ n)).op
  change 𝟙 P ≫ v.app (op n) = v.app (op (n + 1)) ≫
    T.map (homOfLE (Nat.le_succ n)).op at h
  simpa only [Category.id_comp] using h.symm

private theorem mappedUnits_compatible
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D]
    (F : C ⥤ D) [F.Additive] (T : CochainComplex (ℕᵒᵖ ⥤ C) ℤ)
    (P : CochainComplex C ℤ) (γ : ∀ n, P ⟶ T.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (γ (n + 1)) ≫
        ((roosTowerAction F).obj T).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      (F.mapHomologicalComplex (.up ℤ)).map (γ n) := by
  change (F.mapHomologicalComplex (.up ℤ)).map (γ (n + 1)) ≫
    (F.mapHomologicalComplex (.up ℤ)).map
      (T.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
  rw [← Functor.map_comp, hγ]

private theorem additiveComparison_augmentation
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D]
    (F : C ⥤ D) [F.Additive] (T : CochainComplex (ℕᵒᵖ ⥤ C) ℤ)
    (P : CochainComplex C ℤ) (γ : ∀ n, P ⟶ T.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosAugment (X := T) γ hγ) ≫
        roosAdditiveComparison F T =
      roosAugment (X := (roosTowerAction F).obj T)
        (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (γ n))
        (mappedUnits_compatible F T P γ hγ) := by
  apply HomologicalComplex.hom_ext
  intro i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (roosχ ((roosTowerAction F).obj T) p).hom).mp
  erw [roosAugment_χ]
  exact roosAdditiveComparison_augmentation F T P γ hγ p

private theorem derivedFactor_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.mapDerivedCategory)
    {P P' : CochainComplex C ℤ} (a : P ⟶ P') :
    G.map (DerivedCategory.Q.map a) ≫
        (e.app (DerivedCategory.Q.obj P') ≪≫ F.mapDerivedCategoryFactors.app P').hom =
      (e.app (DerivedCategory.Q.obj P) ≪≫ F.mapDerivedCategoryFactors.app P).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, e.hom.naturality, Category.assoc,
    F.mapDerivedCategoryFactors_hom_naturality, ← Category.assoc]

private theorem strictLimitUnit_eq
    {C : Type*} [Category* C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]
    (T : ℕᵒᵖ ⥤ CochainComplex C ℤ) (P : CochainComplex C ℤ)
    (v : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (hv : ∀ n, v.app (op (n + 1)) ≫ T.map (homOfLE (Nat.le_succ n)).op =
      v.app (op n)) :
    roosAugmentLimit
        (X := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T)
        (fun n ↦ v.app (op n)) hv ≫
      (strictTowerLimitIso (A := C)).hom.app
        ((HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T) =
      strictTowerLimitUnit T P v := by
  let Z := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T
  apply HomologicalComplex.hom_ext
  intro i
  apply limit.hom_ext
  intro n
  erw [HomologicalComplex.comp_f, Category.assoc]
  have h := congrArg (fun f ↦ HomologicalComplex.Hom.f f i)
    (limit.isoLimitCone_hom_π
      ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
        HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
  change ((strictTowerLimitIso (A := C)).hom.app Z).f i ≫
      limit.π (Z.X i) n = (limit.π Z.asFunctor n).f i at h
  erw [h, ← HomologicalComplex.comp_f]
  erw [roosAugmentLimit_π (X := Z) (fun k ↦ v.app (op k)) hv n.unop]
  symm
  exact limit.lift_π (strictTowerUnitCone T P v i) n

private theorem augmentedDerivedLimitIso
    {B : Type*} [Category* B] [Abelian B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasExactLimitsOfShape (Discrete ℕ) B] [EnoughInjectives B]
    [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [IsGrothendieckAbelian (ℕᵒᵖ ⥤ B)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (c : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (_hc : RF.IsRightDerivedFunctor c
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ)))
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (c.app I))
    (T : ℕᵒᵖ ⥤ CochainComplex B ℤ) (P : CochainComplex B ℤ)
    (v : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (hv : ∀ n, v.app (op (n + 1)) ≫ T.map (homOfLE (Nat.le_succ n)).op =
      v.app (op n)) :
    let Z := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T
    ∃ e : DerivedCategory.Q.obj (roosF.obj Z) ≅ RF.obj (DerivedCategory.Q.obj Z),
      DerivedCategory.Q.map (roosAugment (X := Z) (P := P) (fun n ↦ v.app (op n)) hv) ≫
        e.hom = DerivedCategory.Q.map (strictTowerLimitUnit T P v) ≫ c.app Z := by
  let Z := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T
  let β := (Functor.isoWhiskerRight (strictTowerLimitIso (A := B))
    DerivedCategory.Q).hom ≫ c
  obtain ⟨ρ, hρ⟩ := normalizedRoosIso (B := B) RF β (fun I hi ↦ by
    have := hI I hi
    change IsIso (DerivedCategory.Q.map ((strictTowerLimitIso (A := B)).hom.app I) ≫
      c.app I)
    infer_instance)
  have hρZ := congr_app hρ Z
  change DerivedCategory.Q.map (roosι Z) ≫ ρ.hom.app Z =
    DerivedCategory.Q.map ((strictTowerLimitIso (A := B)).hom.app Z) ≫ c.app Z at hρZ
  refine ⟨ρ.app Z, ?_⟩
  simp only [Iso.app_hom]
  erw [roosAugment_eq, DerivedCategory.Q.map_comp, Category.assoc, hρZ,
    ← DerivedCategory.Q.map_comp_assoc, strictLimitUnit_eq]

private theorem assembleLocalizedComparison
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) {U U' T : D} {P R S : C}
    (u : U ⟶ U') (e : U ≅ Q.obj P) (e' : U' ≅ Q.obj R)
    (j : R ≅ S) (ρ : Q.obj S ≅ T)
    (a : P ⟶ R) (b : P ⟶ S) (d : Q.obj P ⟶ T)
    (hsource : u ≫ e'.hom = e.hom ≫ Q.map a)
    (haug : a ≫ j.hom = b) (hnorm : Q.map b ≫ ρ.hom = d) :
    u ≫ (e' ≪≫ Q.mapIso j ≪≫ ρ).hom = e.hom ≫ d := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hsource, Category.assoc, ← Q.map_comp_assoc, haug, hnorm]

private def towerRoosTransport
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D]
    (F : C ⥤ D) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (T : ℕᵒᵖ ⥤ CochainComplex C ℤ) (K : CochainComplex C ℤ)
    (s : K ≅ roosF.obj
      ((HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T)) :
    (F.mapHomologicalComplex (.up ℤ)).obj K ≅
      roosF.obj ((HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj
        (T ⋙ F.mapHomologicalComplex (.up ℤ))) := by
  let S := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T
  let e := @asIso _ _ _ _ (roosAdditiveComparison F S)
    (roosAdditiveComparison_isIso F S)
  exact (F.mapHomologicalComplex (.up ℤ)).mapIso s ≪≫ e

private theorem towerRoosTransport_augmentation
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D]
    (F : C ⥤ D) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (T : ℕᵒᵖ ⥤ CochainComplex C ℤ) (K : CochainComplex C ℤ)
    (s : K ≅ roosF.obj
      ((HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T))
    (P : CochainComplex C ℤ) (a : P ⟶ K)
    (γ : ∀ n, P ⟶ T.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op = γ n)
    (hs : a ≫ s.hom = roosAugment
      (X := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T) γ hγ) :
    (F.mapHomologicalComplex (.up ℤ)).map a ≫ (towerRoosTransport F T K s).hom =
      roosAugment
        (X := (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj
          (T ⋙ F.mapHomologicalComplex (.up ℤ)))
        (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (γ n))
        (mappedUnits_compatible F
          ((HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T)
          P γ hγ) := by
  dsimp only [towerRoosTransport, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  erw [← Functor.map_comp_assoc, hs]
  exact additiveComparison_augmentation F
    ((HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj T) P γ hγ

private abbrev sourceSequence (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :=
  Functor.ofOpSequence (X := fun n ↦ (AdicCompletion.level l E X n).obj P)
    (AdicCompletion.levelStep l E X P)

private abbrev sourceTower (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :=
  (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj
    (sourceSequence l E X P)

attribute [local semireducible] modules

private theorem complexIso_naturality
    {P P' : CochainComplex (AdicCompletion.Modules l E X) ℤ} (a : P ⟶ P') :
    (functor l E X).map (DerivedCategory.Q.map a) ≫ (complexIso l E X P').hom =
      (complexIso l E X P).hom ≫
        DerivedCategory.Q.map (((modules l E X).mapHomologicalComplex (.up ℤ)).map a) := by
  let A := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let B := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (IntegralModelsStacks.scalarMap l E X)
  let C := IntegralModelsStacks.smallModules X (constantRing l E X)
  let e := Functor.isoWhiskerLeft A.mapDerivedCategory (Functor.mapDerivedCategoryCompIso B C) ≪≫
    Functor.mapDerivedCategoryCompIso A (B ⋙ C)
  exact derivedFactor_naturality (modules l E X) (functor l E X) e a

attribute [local irreducible] modules

private theorem sourceTower_u (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    roosU (sourceTower l E X P) = AdicCompletion.oneSubShift l E X P := by
  unfold roosU AdicCompletion.oneSubShift
  congr 1
  funext n
  exact Functor.ofOpSequence_map_homOfLE_succ
    (X := fun n ↦ (AdicCompletion.level l E X n).obj P) (AdicCompletion.levelStep l E X P) n

private def sourceRoosIso (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    AdicCompletion.roos l E X P ≅ roosF.obj (sourceTower l E X P) :=
  (AdicCompletion.genericCoconeIso (AdicCompletion.product l E X P)
    (AdicCompletion.oneSubShift l E X P)).symm ≪≫
    eqToIso (congrArg
      (fun t : AdicCompletion.product l E X P ⟶ AdicCompletion.product l E X P ↦
        CochainComplex.mappingCocone t) (sourceTower_u l E X P).symm)

private theorem sourceUnits_compatible
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
    AdicCompletion.levelUnit l E X P (n + 1) ≫
        (sourceTower l E X P).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      AdicCompletion.levelUnit l E X P n := by
  change AdicCompletion.levelUnit l E X P (n + 1) ≫
    (Functor.ofOpSequence (X := fun n ↦ (AdicCompletion.level l E X n).obj P)
      (AdicCompletion.levelStep l E X P)).map
      (homOfLE (Nat.le_succ n)).op = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact AdicCompletion.levelUnit_step l E X P n

private theorem small_exact :
    HasExactLimitsOfShape (Discrete ℕ) (ConstantCompletion.Mod (ring l E X)) := by
  let R := constantRing l E X
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  let : CountableAB4Star A :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ)
    (IntegralModelsStacks.smallModules X R).asEquivalence

private theorem small_tower_grothendieck :
    IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) := by
  let A := ConstantCompletion.Mod (ring l E X)
  let : IsGrothendieckAbelian.{u + 1} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u + 1, u + 1, 0}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (siteModuleRings (ring l E X))
  have := roos_tower_grothendieck A (AsSmall.{u + 1} ℕᵒᵖ)
  exact IsGrothendieckAbelian.of_equivalence
    (Equivalence.congrLeft (AsSmall.equiv (C := ℕᵒᵖ)).symm)

private theorem comap_products
    {C : Type*} [Category* C] [CategoryTheory.MonoidalCategory C]
    [HasLimitsOfShape (Discrete ℕ) C]
    {R S : C} [MonObj R] [MonObj S] (f : R ⟶ S) [IsMonHom f] :
    PreservesLimitsOfShape (Discrete ℕ) (Mod.comap f : Mod C S ⥤ Mod C R) := by
  have : PreservesLimitsOfShape (Discrete ℕ) ((Mod.comap f : Mod C S ⥤ Mod C R) ⋙ Mod.forget R) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (Mod.forget S : Mod C S ⥤ C))
  have : ReflectsLimitsOfShape (Discrete ℕ) (Mod.forget R : Mod C R ⥤ C) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (Mod.comap f) (Mod.forget R)

private theorem composite_products
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₃]
    (A : C₀ ⥤ C₁) (B : C₁ ⥤ C₂) (D : C₂ ⥤ C₃)
    (hA : PreservesLimitsOfShape (Discrete ℕ) A)
    (hB : PreservesLimitsOfShape (Discrete ℕ) B)
    (hD : PreservesLimitsOfShape (Discrete ℕ) D) :
    PreservesLimitsOfShape (Discrete ℕ) (A ⋙ B ⋙ D) := by
  infer_instance

private instance modules_products :
    PreservesLimitsOfShape (Discrete ℕ) (modules l E X) := by
  let A := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let B := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (IntegralModelsStacks.scalarMap l E X)
  unfold modules
  exact composite_products A B (IntegralModelsStacks.smallModules X (constantRing l E X))
    (comap_products (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X))
    (comap_products (IntegralModelsStacks.scalarMap l E X)) inferInstance

private theorem sourceRoosIso_augmentation
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    AdicCompletion.augmentation l E X P ≫ (sourceRoosIso l E X P).hom =
      roosAugment (X := sourceTower l E X P) (P := P) (AdicCompletion.levelUnit l E X P)
        (sourceUnits_compatible l E X P) := by
  exact augmentedCoconeIso (AdicCompletion.product l E X P) P
    (AdicCompletion.oneSubShift l E X P) (roosU (sourceTower l E X P))
    (sourceTower_u l E X P).symm (AdicCompletion.unitProduct l E X P)
    (by rw [sourceTower_u]; exact AdicCompletion.unitProduct_oneSubShift l E X P)
    (AdicCompletion.augmentation l E X P) (by intro i; rfl)

private theorem transportedUnits_compatible
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
    (quotientUnits l E X P).app (op (n + 1)) ≫
        (quotientComplex l E X P).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      (quotientUnits l E X P).app (op n) := by
  exact compatibleFamily (quotients l E X P) (complex l E X P) (quotientUnits l E X P) n

private def transportedRoosIso
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    complex l E X (AdicCompletion.roos l E X P) ≅
      roosF.obj (quotientComplex l E X P) := by
  exact towerRoosTransport (modules l E X) (sourceSequence l E X P)
    (AdicCompletion.roos l E X P) (sourceRoosIso l E X P)

private theorem transportedRoosIso_augmentation
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    ((modules l E X).mapHomologicalComplex (.up ℤ)).map
        (AdicCompletion.augmentation l E X P) ≫ (transportedRoosIso l E X P).hom =
      roosAugment (X := quotientComplex l E X P) (P := complex l E X P)
        (fun n ↦ (quotientUnits l E X P).app (op n))
        (transportedUnits_compatible l E X P) := by
  exact towerRoosTransport_augmentation (modules l E X) (sourceSequence l E X P)
    (AdicCompletion.roos l E X P) (sourceRoosIso l E X P) P
    (AdicCompletion.augmentation l E X P) (AdicCompletion.levelUnit l E X P)
    (sourceUnits_compatible l E X P) (sourceRoosIso_augmentation l E X P)

/-- Exact coefficient transport carries the actual Roos augmentation to the
normalized total right derived limit of the strict transported quotient tower.
This does not mention a generator, a Koszul complex or a completion presentation.

Source: integral-models proof (1); Stacks Tags 0941, 099L and 099M.
(auxiliary; not a blueprint node).

Proof: the three ordinary functors making up modules preserve countable products:
limits of scalar-restricted modules are computed on underlying sheaves, and the
section functor is an equivalence. They are additive and exact. Their product comparison
intertwines the
quotient transitions, hence 1-shift, and carries the actual signed Roos complex to
the signed Roos complex of quotientComplex. It also carries (unit,0) to the same
augmentation in the latter complex. On the pro-etale site countable products of
abelian sheaves are exact, hence so are module products; the section equivalence
transports this assertion to the small ringed site. Thus the strict Roos functor
preserves quasi-isomorphisms. Resolve the tower by a K-injective tower with injective
terms. Its transitions split and the ordinary limit includes as the kernel of
1-shift. That kernel inclusion into the Roos complex is a quasi-isomorphism. Use
it and the right-derived comparison on the K-injective resolution to get e.
Naturality of the comparison identifies the composite of the augmentation with e
with the ordinary compatible-family map followed by c. The localization factors
of the three exact functors are exactly complexIso, which gives the left source
identification in the equation. K-injective normalization gives the calculation
for the specified RF and c. No K-flatness or completeness assumption is needed,
and the zero and empty-site cases give the same identity.
-/
theorem quotient_roos_limit
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (RF : DerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) ⥤
      ConstantCompletion.D (ring l E X))
    (c : (lim : (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) ⥤ _).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hc : RF.IsRightDerivedFunctor c
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) (.up ℤ)))
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (c.app I)) :
    ∃ e : (functor l E X).obj (DerivedCategory.Q.obj (AdicCompletion.roos l E X P)) ≅
        RF.obj (DerivedCategory.Q.obj (quotientComplex l E X P)),
      (functor l E X).map (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) ≫
        e.hom = (complexIso l E X P).hom ≫
          DerivedCategory.Q.map (quotientLimitUnit l E X P) ≫
            c.app (quotientComplex l E X P) := by
  let A := ConstantCompletion.Mod (ring l E X)
  let : HasExactLimitsOfShape (Discrete ℕ) A := small_exact l E X
  let : IsGrothendieckAbelian.{u + 1} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u + 1, u + 1, 0}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (siteModuleRings (ring l E X))
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := small_tower_grothendieck l E X
  obtain ⟨ρ, hρ⟩ := augmentedDerivedLimitIso RF c hc hI
    (quotients l E X P) (complex l E X P) (quotientUnits l E X P)
    (transportedUnits_compatible l E X P)
  let e := complexIso l E X (AdicCompletion.roos l E X P) ≪≫
    DerivedCategory.Q.mapIso (transportedRoosIso l E X P) ≪≫ ρ
  refine ⟨e, ?_⟩
  exact assembleLocalizedComparison DerivedCategory.Q
    ((functor l E X).map (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)))
    (complexIso l E X P) (complexIso l E X (AdicCompletion.roos l E X P))
    (transportedRoosIso l E X P) ρ
    (((modules l E X).mapHomologicalComplex (.up ℤ)).map
      (AdicCompletion.augmentation l E X P)) _ _
    (complexIso_naturality l E X (AdicCompletion.augmentation l E X P))
    (transportedRoosIso_augmentation l E X P) hρ

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
