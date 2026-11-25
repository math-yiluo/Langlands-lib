/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageReductionCone
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.SixFunctors.ProEtale.IntegralReductionTransitionComparison
import WeilConjectures.SixFunctors.ProEtale.IntegralRestrictionPullbackTowerSquare
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # Quotient transitions and units under integral direct image

Source: Stacks 099N, 0944; blueprint integral open direct image, Completeness paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
namespace AlgebraicGeometry.ProEtale

attribute [local instance 30000] AdicCompletion.ringMonoidalObject
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingCommutative AdicCompletion.modulesDerived
  AdicCompletion.finiteModulesDerived
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  upperStarFromPoint CondensedRing.upperStar CondensedRing.derivedComapUpperStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

private def restrictionPushIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {U : C' ⥤ C} {T : D ⥤ D'} {V : D' ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (χ : L ⋙ T ≅ S ⋙ L') : V ⋙ R ≅ R' ⋙ U :=
  conjugateIsoEquiv (a.comp t) (s.comp b) χ.symm

@[irreducible] private def restrictionPushOfPointwiseIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {U : C' ⥤ C} {T : D ⥤ D'} {V : D' ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (f : L ⋙ T ⟶ S ⋙ L') (hf : ∀ K, IsIso (f.app K)) : V ⋙ R ≅ R' ⋙ U := by
  have : ∀ K, IsIso (f.app K) := hf
  have : IsIso f := NatIso.isIso_of_isIso_app _
  exact restrictionPushIso a b s t (asIso f)

private theorem asIso_inv_app
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (f : F ⟶ G) [IsIso f] (M : C) :
    (asIso f).inv.app M = inv (f.app M) := by
  exact NatIso.isIso_inv_app f M

private theorem cancelUnitComparison
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ≅ G) (M : C)
    {Z : D} (v : Z ⟶ F.obj M) (w : Z ⟶ G.obj M)
    (h : v ≫ a.hom.app M = w) : w ≫ a.inv.app M = v := by
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem projection_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {U : C' ⥤ C} {T : D ⥤ D'} {V : D' ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (χ : L ⋙ T ≅ S ⋙ L') (K : D) :
    R.map (t.unit.app K) ≫ (restrictionPushIso a b s t χ).hom.app (T.obj K) =
      s.unit.app (R.obj K) ≫ U.map
        ((b.homEquiv _ _) (χ.inv.app (R.obj K) ≫ T.map (a.counit.app K))) := by
  let α := TwoSquare.mk _ _ _ _ χ.inv
  have hi := iterated_mateEquiv_conjugateEquiv a b s t α
  have hu := unit_mateEquiv t s (mateEquiv a b α) K
  change R.map (t.unit.app K) ≫
    ((mateEquiv t s (mateEquiv a b α))).app (T.obj K) = _ at hu
  rw [hi] at hu
  have hp : (mateEquiv a b α).app K =
      (b.homEquiv _ _) (χ.inv.app (R.obj K) ≫ T.map (a.counit.app K)) := by
    simp [mateEquiv, α, Adjunction.homEquiv_unit]
  simpa only [restrictionPushIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom, Functor.id_obj, hp, α,
    TwoSquare.mk]
    using hu

private theorem projection_unit_map
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {U : C' ⥤ C} {T : D ⥤ D'} {V : D' ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (f : L ⋙ T ⟶ S ⋙ L') [IsIso f] (K : D) :
    R.map (t.unit.app K) ≫ (restrictionPushIso a b s t (asIso f)).hom.app (T.obj K) =
      s.unit.app (R.obj K) ≫ U.map
        ((b.homEquiv _ _) (inv (f.app (R.obj K)) ≫ T.map (a.counit.app K))) := by
  have h := projection_unit a b s t (asIso f) K
  rw [asIso_inv_app f (R.obj K)] at h
  exact h

private theorem restrictionPushIso_inv
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {U : C' ⥤ C} {T : D ⥤ D'} {V : D' ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (χ : L ⋙ T ≅ S ⋙ L')
    (r : U ⋙ L ⟶ L' ⋙ V)
    (hr : (mateEquiv s t (TwoSquare.mk _ _ _ _ χ.hom)) = r) :
    (restrictionPushIso a b s t χ).inv =
      (mateEquiv b a (TwoSquare.mk _ _ _ _ r)) := by
  have h := iterated_mateEquiv_conjugateEquiv s t a b
    (TwoSquare.mk _ _ _ _ χ.hom)
  have hm : mateEquiv s t (TwoSquare.mk _ _ _ _ χ.hom) =
      TwoSquare.mk _ _ _ _ r := by
    refine NatTrans.ext (funext fun Z ↦ ?_)
    exact congrArg (fun z ↦ z.app Z) hr
  rw [hm] at h
  simpa only [restrictionPushIso, conjugateIsoEquiv_apply_inv, Iso.symm_inv] using h.symm

private theorem invertRestrictionSquare
    {C A B C' A' B' : Type*}
    [Category C] [Category A] [Category B]
    [Category C'] [Category A'] [Category B']
    (U : A ⥤ C) (V : B ⥤ A) (W : B ⥤ C)
    (U' : A' ⥤ C') (V' : B' ⥤ A') (W' : B' ⥤ C')
    (F : C ⥤ C') (G : A ⥤ A') (H : B ⥤ B')
    (a : U ⋙ F ≅ G ⋙ U') (b : W ⋙ F ≅ H ⋙ W')
    (e : V ⋙ G ≅ H ⋙ V') (c : V ⋙ U ≅ W) (d : V' ⋙ U' ≅ W')
    (h : ∀ Z, U'.map (e.inv.app Z) ≫ a.inv.app (V.obj Z) =
      d.hom.app (H.obj Z) ≫ b.inv.app Z ≫ F.map (c.inv.app Z)) :
    ∀ Z, F.map (c.hom.app Z) ≫ b.hom.app Z =
      a.hom.app (V.obj Z) ≫ U'.map (e.hom.app Z) ≫ d.hom.app (H.obj Z) := by
  intro Z
  have hh := congrArg
    (fun z ↦ F.map (c.hom.app Z) ≫ b.hom.app Z ≫ d.inv.app (H.obj Z) ≫ z ≫
      a.hom.app (V.obj Z) ≫ U'.map (e.hom.app Z)) (h Z)
  simpa [Category.assoc, ← U'.map_comp_assoc, ← F.map_comp_assoc] using
    congrArg (fun z ↦ z ≫ d.hom.app (H.obj Z)) hh

private theorem pushRestriction_square
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {U : C₁ ⥤ C₀} {V : C₂ ⥤ C₁} {W : C₂ ⥤ C₀}
    {U' : D₁ ⥤ D₀} {V' : D₂ ⥤ D₁} {W' : D₂ ⥤ D₀}
    (r₁ : U ⋙ L₀ ⟶ L₁ ⋙ U') (r₂ : V ⋙ L₁ ⟶ L₂ ⋙ V')
    (r : W ⋙ L₀ ⟶ L₂ ⋙ W') (c : V ⋙ U ≅ W) (d : V' ⋙ U' ≅ W')
    (h : ∀ Z, L₀.map (c.inv.app Z) ≫ r₁.app (V.obj Z) ≫ U'.map (r₂.app Z) =
      r.app Z ≫ d.inv.app (L₂.obj Z)) (K : D₂) :
    U.map ((mateEquiv a₂ a₁ (TwoSquare.mk _ _ _ _ r₂)).app K) ≫
        (mateEquiv a₁ a₀ (TwoSquare.mk _ _ _ _ r₁)).app (V'.obj K) =
      c.hom.app (R₂.obj K) ≫
        (mateEquiv a₂ a₀ (TwoSquare.mk _ _ _ _ r)).app K ≫ R₀.map (d.inv.app K) := by
  let α := TwoSquare.mk _ _ _ _ r₂
  let β := TwoSquare.mk _ _ _ _ r₁
  let γ := TwoSquare.mk _ _ _ _ r
  have hs : TwoSquare.hComp α β = (γ.whiskerTop c.hom).whiskerBottom d.inv := by
    refine NatTrans.ext (funext fun Z ↦ ?_)
    simp only [α, β, γ, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    apply (cancel_epi (L₀.map (c.inv.app Z))).1
    simpa only [Category.assoc, ← L₀.map_comp_assoc, Iso.inv_hom_id_app,
      L₀.map_id, Category.id_comp] using h Z
  have hm := congrArg (mateEquiv a₂ a₀) hs
  rw [mateEquiv_vcomp a₂ a₁ a₀, mateEquiv_whiskerTop_whiskerBottom] at hm
  have hk := congrArg (fun q ↦ q.app K) hm
  simpa only [α, β, γ, TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] using hk

attribute [local instance] CondensedRing.scalarSixMap_isMonHom
  CondensedRing.scalarSixRing_comm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

private instance (priority := 30000) pointReductionMon (n : ℕ) :
    IsMonHom (DerivedNakayama.reductionRing l E n) :=
  Sheaf.isMonHom_sheafCompose_map _ (DerivedNakayama.reductionRingSheaf l E n)

private instance (priority := 30000) pointTransitionMon (n : ℕ) :
    IsMonHom (AdicCompletion.transitionRing l E n) :=
  Sheaf.isMonHom_sheafCompose_map _ (AdicCompletion.transitionRingSheaf l E n)

private instance (priority := 30000) integralComm (Z : Scheme.{u}) :
    IsCommMonObj (AdicCompletion.ring l E Z) :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint Z)

private instance (priority := 30000) finiteComm (Z : Scheme.{u}) (n : ℕ) :
    IsCommMonObj (AdicCompletion.finiteRing l E Z n) :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint Z)

private instance (priority := 40000) integralCommSym (Z : Scheme.{u}) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ _
      (ProEtale.sheafSymmetricCategory Z).toBraidedCategory
      (AdicCompletion.ring l E Z) (AdicCompletion.ringMonoidalObject l E Z) := by
  exact AdicCompletion.ringCommutative l E Z

private instance (priority := 40000) finiteCommSym (Z : Scheme.{u}) (n : ℕ) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ _
      (ProEtale.sheafSymmetricCategory Z).toBraidedCategory
      (AdicCompletion.finiteRing l E Z n) (AdicCompletion.finiteRingMonoidalObject l E Z n) := by
  exact AdicCompletion.finiteRingCommutative l E Z n

private theorem pullbackRestrictionSquare (n : ℕ)
    (M : AdicCompletion.FiniteDerived l E X n) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory.map
        ((AdicCompletion.restrictComp l E X n).inv.app M) ≫
      (CondensedRing.derivedComapUpperStarIso
        (DerivedNakayama.reductionRing l E (n + 2)) j).inv.app
          ((AdicCompletion.finiteRestrict l E X n).obj M) ≫
      (AdicCompletion.restrict l E U (n + 1)).map
        ((CondensedRing.derivedComapUpperStarIso
          (AdicCompletion.transitionRing l E n) j).inv.app M) =
      (CondensedRing.derivedComapUpperStarIso
        (DerivedNakayama.reductionRing l E (n + 1)) j).inv.app M ≫
      (AdicCompletion.restrictComp l E U n).inv.app
        ((CondensedRing.upperStar
          (DerivedNakayama.quotientRing l E (n + 1)) j).mapDerivedCategory.obj M) := by
  exact integral_restriction_pullback_tower_square l E j n M

@[irreducible] private def scalarPushRestriction (n : ℕ)
    [hχ : IsIso (integralReductionPullbackMap l E j n)] :
    AdicCompletion.restrict l E U n ⋙
        CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j ≅
      CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.quotientRing l E (n + 1)) j ⋙ AdicCompletion.restrict l E X n:= by
  dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at *
  exact restrictionPushIso
    ((CondensedRing.derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.integerRing l E) j))
    ((CondensedRing.derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.quotientRing l E (n + 1)) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.quotientRing l E (n + 1)) j))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
    (@asIso _ _ _ _ (integralReductionPullbackMap l E j n) hχ)

private def finiteScalarMap (n : ℕ) :
    (CommMon.mk (DerivedNakayama.quotientRing l E (n + 2)) :
      CondensedRing.ScalarSixRing.{u}) ⟶
      CommMon.mk (DerivedNakayama.quotientRing l E (n + 1)) :=
  CommMon.homMk (Mon.Hom.mk (AdicCompletion.transitionRing l E n)
    (isMonHom_hom := pointTransitionMon l E n))

@[irreducible] private def finitePushRestriction (n : ℕ) :
    AdicCompletion.finiteRestrict l E U n ⋙
        CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.quotientRing l E (n + 2)) j ≅
      CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.quotientRing l E (n + 1)) j ⋙
        AdicCompletion.finiteRestrict l E X n:= by
  dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at *
  with_unfolding_all
    exact restrictionPushOfPointwiseIso
      ((CondensedRing.derivedUpperStarLowerStarAdjunction
        (DerivedNakayama.quotientRing l E (n + 2)) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.quotientRing l E (n + 2)) j))
      ((CondensedRing.derivedUpperStarLowerStarAdjunction
        (DerivedNakayama.quotientRing l E (n + 1)) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.quotientRing l E (n + 1)) j))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.transition l E X n))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.transition l E U n))
      (CondensedRing.scalarSixPullHom (finiteScalarMap l E n) j)
      (CondensedRing.scalarSixPullHom_isIso_app (finiteScalarMap l E n) j)

private theorem scalarPushRestriction_inv (n : ℕ)
    [IsIso (integralReductionPullbackMap l E j n)] :
    (scalarPushRestriction l E j n).inv =
      (mateEquiv
        ((CondensedRing.derivedUpperStarLowerStarAdjunction
          (DerivedNakayama.quotientRing l E (n + 1)) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing l E (n + 1)) j))
        ((CondensedRing.derivedUpperStarLowerStarAdjunction
          (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.integerRing l E) j))
        (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso
          (DerivedNakayama.reductionRing l E (n + 1)) j).inv)):= by
  try dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at *
  unfold scalarPushRestriction
  apply restrictionPushIso_inv
  exact
    ((mateEquiv _ _).apply_symm_apply (TwoSquare.mk _ _ _ _ _))

private theorem finitePushRestriction_inv (n : ℕ) :
    (finitePushRestriction l E j n).inv =
      (mateEquiv
        ((CondensedRing.derivedUpperStarLowerStarAdjunction
          (DerivedNakayama.quotientRing l E (n + 1)) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing l E (n + 1)) j))
        ((CondensedRing.derivedUpperStarLowerStarAdjunction
          (DerivedNakayama.quotientRing l E (n + 2)) j).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing l E (n + 2)) j))
        (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso
          (AdicCompletion.transitionRing l E n) j).inv)):= by
  dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at *
  unfold finitePushRestriction restrictionPushOfPointwiseIso
  apply restrictionPushIso_inv
  try simp only [finiteScalarMap, CondensedRing.scalarSixPullHom,
    Adjunction.pushHomOfComapIso]
  exact
    ((mateEquiv _ _).apply_symm_apply (TwoSquare.mk _ _ _ _ _))

private theorem pushRestrictionSquare (n : ℕ)
    [IsIso (integralReductionPullbackMap l E j n)]
    [IsIso (integralReductionPullbackMap l E j (n + 1))]
    (M : AdicCompletion.FiniteDerived l E U n) :
    (CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.integerRing l E) j).map
        ((AdicCompletion.restrictComp l E U n).hom.app M) ≫
      (scalarPushRestriction l E j n).hom.app M =
    (scalarPushRestriction l E j (n + 1)).hom.app
        ((AdicCompletion.finiteRestrict l E U n).obj M) ≫
      (AdicCompletion.restrict l E X (n + 1)).map
        ((finitePushRestriction l E j n).hom.app M) ≫
      (AdicCompletion.restrictComp l E X n).hom.app
        ((CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.quotientRing l E (n + 1)) j).obj M):= by
  dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at *
  apply invertRestrictionSquare
    (AdicCompletion.restrict l E U (n + 1)) (AdicCompletion.finiteRestrict l E U n)
    (AdicCompletion.restrict l E U n)
    (AdicCompletion.restrict l E X (n + 1)) (AdicCompletion.finiteRestrict l E X n)
    (AdicCompletion.restrict l E X n)
    (CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j)
    (CondensedRing.moduleObjectDerivedPushforward
      (DerivedNakayama.quotientRing l E (n + 2)) j)
    (CondensedRing.moduleObjectDerivedPushforward
      (DerivedNakayama.quotientRing l E (n + 1)) j)
    (scalarPushRestriction l E j (n + 1)) (scalarPushRestriction l E j n)
    (finitePushRestriction l E j n) (AdicCompletion.restrictComp l E U n)
    (AdicCompletion.restrictComp l E X n)
  intro N
  rw [scalarPushRestriction_inv, scalarPushRestriction_inv, finitePushRestriction_inv]
  exact pushRestriction_square _ _ _ _ _ _ _ _ (pullbackRestrictionSquare l E j n) N

private theorem adjointTransition_unique
    {C A B : Type*} [Category C] [Category A] [Category B]
    {L : C ⥤ A} {U : A ⥤ C} {N : C ⥤ B} {W : B ⥤ C}
    (a : L ⊣ U) (b : N ⊣ W) (V : B ⥤ A) (c : V ⋙ U ≅ W)
    (K : C) (v : L.obj K ⟶ V.obj (N.obj K))
    (h : a.unit.app K ≫ U.map v ≫ c.hom.app (N.obj K) = b.unit.app K) :
    v = (a.homEquiv _ _).symm (b.unit.app K ≫ c.inv.app (N.obj K)) := by
  apply (a.homEquiv _ _).injective
  simp only [Functor.id_obj]
  rw [Equiv.apply_symm_apply, a.homEquiv_unit]
  apply (cancel_mono (c.hom.app (N.obj K))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj] using h

private theorem scalarPushRestriction_unit (n : ℕ)
    [hχ : IsIso (integralReductionPullbackMap l E j n)]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :
    let F := CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j
    F.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E U n)).unit.app K) ≫
      (scalarPushRestriction l E j n).hom.app ((AdicCompletion.derivedReduction l E U n).obj K) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E X n)).unit.app (F.obj K) ≫
      (AdicCompletion.restrict l E X n).map (integralFiniteProjection l E j n K):= by
  have h := @projection_unit_map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((CondensedRing.derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.integerRing l E) j))
    ((CondensedRing.derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.quotientRing l E (n + 1)) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.quotientRing l E (n + 1)) j))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
    (integralReductionPullbackMap l E j n) hχ K
  dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at h ⊢
  unfold scalarPushRestriction
  dsimp (config := { instances := true }) only
    [AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
     AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at *
  dsimp (config := { instances := true }) only [id_eq, integralFiniteProjection,
    AdicCompletion.derivedReduction, AdicCompletion.restrict, Functor.id_obj,
    CondensedRing.moduleObjectDerivedPushforward] at *
  with_unfolding_all exact h

private theorem assembleTransition
    {C A B C' A' B' : Type*}
    [Category C] [Category A] [Category B]
    [Category C'] [Category A'] [Category B']
    {L : C ⥤ A} {U : A ⥤ C} {N : C ⥤ B} {W : B ⥤ C}
    {L' : C' ⥤ A'} {R : A' ⥤ C'} {N' : C' ⥤ B'} {S : B' ⥤ C'}
    (al : L ⊣ U) (an : N ⊣ W) (ar : L' ⊣ R) (az : N' ⊣ S)
    (V : B ⥤ A) (T : B' ⥤ A') (F : C ⥤ C') (G : A ⥤ A') (H : B ⥤ B')
    (a : U ⋙ F ≅ G ⋙ R) (b : W ⋙ F ≅ H ⋙ S)
    (e : V ⋙ G ≅ H ⋙ T) (c : V ⋙ U ≅ W) (d : T ⋙ R ≅ S)
    (hsq : ∀ Z, F.map (c.hom.app Z) ≫ b.hom.app Z =
      a.hom.app (V.obj Z) ≫ R.map (e.hom.app Z) ≫ d.hom.app (H.obj Z))
    (K : C) (bm : L'.obj (F.obj K) ≅ G.obj (L.obj K))
    (bn : N'.obj (F.obj K) ≅ H.obj (N.obj K))
    (hm : F.map (al.unit.app K) ≫ a.hom.app (L.obj K) =
      ar.unit.app (F.obj K) ≫ R.map bm.hom)
    (hn : F.map (an.unit.app K) ≫ b.hom.app (N.obj K) =
      az.unit.app (F.obj K) ≫ S.map bn.hom)
    (v : L.obj K ⟶ V.obj (N.obj K))
    (w : L'.obj (F.obj K) ⟶ T.obj (N'.obj (F.obj K)))
    (hv : al.unit.app K ≫ U.map v ≫ c.hom.app (N.obj K) = an.unit.app K)
    (hw : ar.unit.app (F.obj K) ≫ R.map w ≫ d.hom.app (N'.obj (F.obj K)) =
      az.unit.app (F.obj K)) :
    F.map (U.map v ≫ c.hom.app (N.obj K)) ≫
        (b.app (N.obj K) ≪≫ S.mapIso bn.symm).hom =
      (a.app (L.obj K) ≪≫ R.mapIso bm.symm).hom ≫
        (R.map w ≫ d.hom.app (N'.obj (F.obj K))) := by
  have hw' := adjointTransition_unique ar az T d (F.obj K) w hw
  have hm' := cancelUnitComparison a (L.obj K) _ _ hm
  have hn' := cancelUnitComparison b (N.obj K) _ _ hn
  simp only [Category.assoc] at hm' hn'
  have h := IntegralPresentation.adjointTransitionComparison al an ar az V T F G H
    a b e c d hsq K bm bn hm' hn' v hv
  simp only [Functor.id_obj] at hw'
  rw [← hw'] at h
  let am := a.app (L.obj K) ≪≫ R.mapIso bm.symm
  let an' := b.app (N.obj K) ≪≫ S.mapIso bn.symm
  have h' : (R.map w ≫ d.hom.app (N'.obj (F.obj K))) ≫ an'.inv =
      am.inv ≫ F.map (U.map v ≫ c.hom.app (N.obj K)) := by
    simpa only [am, an', Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
      Iso.app_inv, Category.assoc] using h
  change F.map (U.map v ≫ c.hom.app (N.obj K)) ≫ an'.hom =
    am.hom ≫ (R.map w ≫ d.hom.app (N'.obj (F.obj K)))
  apply (cancel_epi am.inv).1
  apply (cancel_mono an'.inv).1
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using h'.symm

private theorem assembleUnit
    {C A C' A' : Type*} [Category C] [Category A] [Category C'] [Category A']
    {L : C ⥤ A} {U : A ⥤ C} {L' : C' ⥤ A'} {R : A' ⥤ C'}
    (al : L ⊣ U) (ar : L' ⊣ R) (F : C ⥤ C') (G : A ⥤ A')
    (a : U ⋙ F ≅ G ⋙ R) (K : C) (b : L'.obj (F.obj K) ≅ G.obj (L.obj K))
    (h : F.map (al.unit.app K) ≫ a.hom.app (L.obj K) =
      ar.unit.app (F.obj K) ≫ R.map b.hom) :
    F.map (al.unit.app K) ≫ (a.app (L.obj K) ≪≫ R.mapIso b.symm).hom =
      ar.unit.app (F.obj K) := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    ← Category.assoc]
  rw [h, Category.assoc, ← R.map_comp, Iso.hom_inv_id, R.map_id]
  dsimp only [Functor.id_obj]
  exact Category.comp_id _

attribute [local irreducible] integralFiniteProjection

attribute [-instance] AdicCompletion.ringMonoidalObject
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingCommutative AdicCompletion.modulesDerived
  AdicCompletion.finiteModulesDerived
attribute [-instance] pointReductionMon pointTransitionMon integralComm finiteComm
  integralCommSym finiteCommSym CondensedRing.scalarSixRing_comm
  CondensedRing.scalarSixMap_isMonHom

/-- The existing integral coefficient commutativity for the symmetric sheaf braiding.
Source: coefficient scalar adjunctions
(auxiliary; not a blueprint node). -/
local instance integralSymmetricComm (Z : Scheme.{u}) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ _
      (ProEtale.sheafSymmetricCategory Z).toBraidedCategory
      (AdicCompletion.ring l E Z) inferInstance := by
  exact AdicCompletion.ringCommutative l E Z

/-- The existing finite coefficient commutativity for the symmetric sheaf braiding.
Source: coefficient scalar adjunctions
(auxiliary; not a blueprint node). -/
local instance finiteSymmetricComm (Z : Scheme.{u}) (n : ℕ) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ _
      (ProEtale.sheafSymmetricCategory Z).toBraidedCategory
      (AdicCompletion.finiteRing l E Z n) inferInstance := by
  exact AdicCompletion.finiteRingCommutative l E Z n

/-- Finite quotient projection isomorphisms identify the whole reduction sequence,
including its transitions and augmentation, before taking any derived limit.
Assume the specified scalar mates and their finite geometric projections are invertible;
this statement supplies the remaining transition and unit compatibility.
Source: Stacks 099N, 0944; blueprint integral open direct image, Completeness paragraph
(auxiliary; not a blueprint node).

Proof: use the lifted ring of integers with its principal uniformizer ideal. The
sfb_integral_coefficient_limit identifies its completed coefficient sheaf. Apply the
normalized internal-to-section-action equivalences at U and X. Scalar restriction
squares are the identity on underlying sections and their left adjoint comparisons
send pure tensors to the same pure tensors. The specified finiteProjection maps of
CompletedDirectImageLimits are therefore the internal finite projection maps.
Their invertibility is supplied by hproj, proved separately by the scalar cone
comparison. Restrict finite scalars and identify
restriction with geometric direct image to obtain a_n in the displayed direction.
A consecutive quotient sends s tensor m to rho(s) tensor m on both paths; this proves
the transition equation. Both augmentation paths send m to 1 tensor m; the scalar
and geometric adjunction triangles prove the displayed unit equation after deriving.
These equations also follow from towerProjection_properties after transporting its
normalized evaluation maps. No completeness of K is assumed in this assertion.
The same formulas hold for n=0, zero complexes, empty schemes and unbounded K. -/
theorem integral_direct_image_reduction_tower
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (hχ : ∀ n : ℕ, IsIso (integralReductionPullbackMap l E j n))
    (hproj : ∀ n : ℕ, letI := hχ n; IsIso (integralFiniteProjection l E j n K)) :
    let F := CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j
    ∃ a : ∀ n : ℕ,
      F.obj (AdicCompletion.integralLevel l E U K n) ≅
        AdicCompletion.integralLevel l E X (F.obj K) n,
      (∀ n : ℕ, F.map (AdicCompletion.integralStep l E U K n) ≫ (a n).hom =
        (a (n + 1)).hom ≫ AdicCompletion.integralStep l E X (F.obj K) n) ∧
      ∀ n : ℕ, F.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E U n)).unit.app K) ≫ (a n).hom =
          (Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app (F.obj K):= by
  let (n : ℕ) : IsIso (integralReductionPullbackMap l E j n) := hχ n
  let F := CondensedRing.moduleObjectDerivedPushforward
    (DerivedNakayama.integerRing l E) j
  let p (n : ℕ) := @asIso _ _ _ _ (integralFiniteProjection l E j n K) (hproj n)
  let a (n : ℕ) :=
    (scalarPushRestriction l E j n).app ((AdicCompletion.derivedReduction l E U n).obj K) ≪≫
      (AdicCompletion.restrict l E X n).mapIso (p n).symm
  refine ⟨a, ?_, ?_⟩
  · intro n
    have h := assembleTransition
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U (n + 1)))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X (n + 1)))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
      (AdicCompletion.finiteRestrict l E U n) (AdicCompletion.finiteRestrict l E X n)
      F
      (CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E (n + 2)) j)
      (CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E (n + 1)) j)
      (scalarPushRestriction l E j (n + 1)) (scalarPushRestriction l E j n)
      (finitePushRestriction l E j n)
      (AdicCompletion.restrictComp l E U n) (AdicCompletion.restrictComp l E X n)
      (pushRestrictionSquare l E j n) K (p (n + 1)) (p n)
      (scalarPushRestriction_unit l E j (n + 1) K)
      (scalarPushRestriction_unit l E j n K)
      (AdicCompletion.derivedStep l E U K n) (AdicCompletion.derivedStep l E X (F.obj K) n)
      (AdicCompletion.reductionUnit_compatible l E U K n)
      (AdicCompletion.reductionUnit_compatible l E X (F.obj K) n)
    dsimp (config := { instances := true }) only
      [a, F, AdicCompletion.integralStep, AdicCompletion.integralLevel,
       AdicCompletion.restrict, AdicCompletion.derivedReduction,
       AdicCompletion.ringMonoidalObject, AdicCompletion.finiteRingMonoidalObject,
       AdicCompletion.modulesDerived, AdicCompletion.finiteModulesDerived] at h ⊢
    with_unfolding_all exact h
  · intro n
    have h := assembleUnit
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
      F (CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E (n + 1)) j)
      (scalarPushRestriction l E j n) K (p n) (scalarPushRestriction_unit l E j n K)
    dsimp (config := { instances := true }) only
      [a, F, AdicCompletion.integralLevel, AdicCompletion.restrict,
       AdicCompletion.derivedReduction, AdicCompletion.ringMonoidalObject,
       AdicCompletion.finiteRingMonoidalObject, AdicCompletion.modulesDerived,
       AdicCompletion.finiteModulesDerived] at h ⊢
    with_unfolding_all exact h

end AlgebraicGeometry.ProEtale
