/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.IntegralReductionPullbackNormalization
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # Coherence of pullback with consecutive integral scalar restrictions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local instance 20000] ProEtale.sheafBraidedCategory
attribute [local instance] CondensedRing.scalarSixRing_comm
  CondensedRing.scalarSixMap_isMonHom
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

private theorem coherentRestrictionSquare_app
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (U : C₁ ⥤ C₀) (V : C₂ ⥤ C₁) (W : C₂ ⥤ C₀)
    (U' : D₁ ⥤ D₀) (V' : D₂ ⥤ D₁) (W' : D₂ ⥤ D₀)
    (α : U ⋙ F₀ ≅ F₁ ⋙ U') (β : V ⋙ F₁ ≅ F₂ ⋙ V')
    (γ : W ⋙ F₀ ≅ F₂ ⋙ W') (c : W ≅ V ⋙ U) (d : W' ≅ V' ⋙ U')
    (c' : W ≅ V ⋙ U) (d' : W' ≅ V' ⋙ U') (hc : c = c') (hd : d = d')
    (h : Functor.isoWhiskerRight c F₀ ≪≫
        (Functor.associator V U F₀ ≪≫ Functor.isoWhiskerLeft V α ≪≫
          (Functor.associator V F₁ U').symm ≪≫ Functor.isoWhiskerRight β U' ≪≫
          Functor.associator F₂ V' U') = γ ≪≫ Functor.isoWhiskerLeft F₂ d)
    (M : C₂) :
    F₀.map (c'.hom.app M) ≫ α.hom.app (V.obj M) ≫ U'.map (β.hom.app M) =
      γ.hom.app M ≫ d'.hom.app (F₂.obj M) := by
  subst c'
  subst d'
  have h' := NatTrans.congr_app (congrArg Iso.hom h) M
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id] using h'

private theorem mappedInverseComposite
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [dC : HasDerivedCategory C] [dD : HasDerivedCategory D] [dE : HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    [CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G)]
    [CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G)]
    (e : F ⋙ G ≅ H) :
    Functor.mapDerivedCategoryNatIso e.symm ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm =
      (Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso e).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_symm]

private theorem comapCongrSymm
    {V : Type*} [Category V] [MonoidalCategory V]
    {R S : V} [MonObj R] [MonObj S] {f g : R ⟶ S}
    [IsMonHom f] [IsMonHom g] (e : f = g) :
    (Mod.comapCongr (C := V) e).symm = Mod.comapCongr (C := V) e.symm := by
  cases e
  rfl

private def scalarMap {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) :
    A.X ⟶ B.X := a.hom.hom

private instance scalarMapMon {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) :
    IsMonHom (scalarMap a) := by
  with_unfolding_all exact a.hom.isMonHom_hom

private theorem scalarMap_comp
    {A B C : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    scalarMap (a ≫ b) = scalarMap a ≫ scalarMap b := by
  rfl

private theorem factorAt
    {A B C : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) (Z : Scheme.{u}) :
    coefficientMap (Λ := A.X) (Λ' := C.X) (scalarMap c) Z =
      coefficientMap (Λ := A.X) (Λ' := B.X) (scalarMap a) Z ≫
        coefficientMap (Λ := B.X) (Λ' := C.X) (scalarMap b) Z := by
  rw [← coefficientMap_comp, ← scalarMap_comp]
  exact congrArg (fun (g : A ⟶ C) ↦ coefficientMap (scalarMap g) Z) h.symm

private def towerAlong
    {A B C : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) (Z : Scheme.{u}) :
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (coefficientMap (Λ := A.X) (Λ' := C.X) (scalarMap c) Z) ≅
      Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (coefficientMap (Λ := B.X) (Λ' := C.X) (scalarMap b) Z) ⋙
        Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (coefficientMap (Λ := A.X) (Λ' := B.X) (scalarMap a) Z) :=
  ((Mod.comapComp (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap (Λ := A.X) (Λ' := B.X) (scalarMap a) Z)
      (coefficientMap (Λ := B.X) (Λ' := C.X) (scalarMap b) Z)).symm ≪≫
    Mod.comapCongr (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (factorAt a b c h Z).symm).symm

private theorem derivedSquareAlong
    {A B C : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) {U X : Scheme.{u}} (j : U ⟶ X) :
    Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (towerAlong a b c h X) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) (CondensedRing.scalarSixPull A j) ≪≫
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (coefficientMap (Λ := B.X) (Λ' := C.X) (scalarMap b) X)).mapDerivedCategory
          (CondensedRing.derivedComapUpperStarIso (Λ := A.X) (Λ' := B.X) (scalarMap a) j).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (CondensedRing.derivedComapUpperStarIso (Λ := B.X) (Λ' := C.X) (scalarMap b) j).symm
          (Mod.comap (D := Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
            (coefficientMap (Λ := A.X) (Λ' := B.X) (scalarMap a) U)).mapDerivedCategory ≪≫
        Functor.associator _ _ _) =
      (CondensedRing.derivedComapUpperStarIso (Λ := A.X) (Λ' := C.X) (scalarMap c) j).symm ≪≫
        Functor.isoWhiskerLeft (CondensedRing.scalarSixPull C j)
          (Functor.mapDerivedCategoryNatIso (towerAlong a b c h U) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm) := by
  subst c
  dsimp only [towerAlong, CondensedRing.scalarSixOrdinaryRestrictionTower]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, comapCongrSymm]
  with_unfolding_all exact CondensedRing.scalarSixDerivedRestrictionTowerSquare a b j

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

private def integralBundle : CondensedRing.ScalarSixRing.{u} :=
  CommMon.mk (DerivedNakayama.integerRing l E)

private def quotientBundle (n : ℕ) : CondensedRing.ScalarSixRing.{u} :=
  CommMon.mk (DerivedNakayama.quotientRing l E (n + 1))

@[instance_reducible] private def integralBundleDerived (Z : Scheme.{u}) :
    HasDerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralBundle l E).X Z)) := by
  with_unfolding_all exact AdicCompletion.modulesDerived l E Z

@[instance_reducible] private def quotientBundleDerived (Z : Scheme.{u}) (n : ℕ) :
    HasDerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (quotientBundle l E n).X Z)) := by
  with_unfolding_all exact AdicCompletion.finiteModulesDerived l E Z n

private def reductionBundle (n : ℕ) : integralBundle l E ⟶ quotientBundle l E n :=
  CommMon.homMk (Mon.Hom.mk (DerivedNakayama.reductionRing l E (n + 1))
    (isMonHom_hom := Sheaf.isMonHom_sheafCompose_map _
      (DerivedNakayama.reductionRingSheaf l E (n + 1))))

private def transitionBundle (n : ℕ) : quotientBundle l E (n + 1) ⟶ quotientBundle l E n :=
  CommMon.homMk (Mon.Hom.mk (AdicCompletion.transitionRing l E n)
    (isMonHom_hom := Sheaf.isMonHom_sheafCompose_map _
      (AdicCompletion.transitionRingSheaf l E n)))

private theorem bundleFactor (n : ℕ) :
    reductionBundle l E (n + 1) ≫ transitionBundle l E n = reductionBundle l E n := by
  apply CommMon.hom_ext
  rfl

private def ordinaryComp (Z : Scheme.{u}) (n : ℕ) :
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (AdicCompletion.transition l E Z n) ⋙
      Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (AdicCompletion.quotient l E Z (n + 1)) ≅
      Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (AdicCompletion.quotient l E Z n) :=
  (Mod.comapComp (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (AdicCompletion.quotient l E Z (n + 1)) (AdicCompletion.transition l E Z n)).symm ≪≫
      Mod.comapCongr (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (AdicCompletion.quotient_transition l E Z n)

attribute [-instance] scalarMapMon CondensedRing.scalarSixRing_comm
  CondensedRing.scalarSixMap_isMonHom

/-- Pullback respects the compositor for two consecutive quotient restrictions.
Source: blueprint integral open direct image, Completeness paragraph; Stacks 06YY.
(auxiliary; not a blueprint node).

Proof: pull the two quotient ring maps from the point to U and X. Their composite is
exactly the smaller quotient map. On ordinary internal modules, the restriction
compositor is the identity on the underlying object. The pullback/restriction
comparison is the mate of the identity-on-underlying-sheaves direct-image comparison.
Pasting the two ordinary squares therefore equals the square for the composite ring
map. Apply the termwise derived localization, preserving the composition isomorphisms,
and replace the ordinary restriction compositor by the published restrictComp. This
is the derived restriction tower square, evaluated at M. No flatness is used because
restriction and geometric inverse image are exact. The argument includes n=0, zero
complexes, empty schemes, and unbounded complexes. -/
theorem integral_restriction_pullback_tower_square (n : ℕ)
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
  let bundleComm (A : CondensedRing.ScalarSixRing.{u}) : IsCommMonObj A.X := A.comm
  let scalarMapMonoid {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) :
      IsMonHom (scalarMap a) := scalarMapMon a
  let a := reductionBundle l E (n + 1)
  let b := transitionBundle l E n
  let c := reductionBundle l E n
  have hf : a ≫ b = c := bundleFactor l E n
  have h := derivedSquareAlong a b c hf j
  have ho (Z : Scheme.{u}) :
      towerAlong a b c hf Z = (ordinaryComp l E Z n).symm := by
    dsimp only [towerAlong, ordinaryComp]
    rfl
  have hc (Z : Scheme.{u}) :
      Functor.mapDerivedCategoryNatIso (towerAlong a b c hf Z) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              (AdicCompletion.transition l E Z n))
            (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              (AdicCompletion.quotient l E Z (n + 1)))).symm =
        (AdicCompletion.restrictComp l E Z n).symm := by
    rw [ho Z]
    dsimp only [AdicCompletion.restrictComp, ordinaryComp]
    with_unfolding_all
      exact mappedInverseComposite
        (dC := quotientBundleDerived l E Z n)
        (dD := quotientBundleDerived l E Z (n + 1))
        (dE := integralBundleDerived l E Z) _ _ _ _
  dsimp only [CondensedRing.scalarSixPull] at h
  have hp := coherentRestrictionSquare_app
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory
    (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 2)) j).mapDerivedCategory
    (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) j).mapDerivedCategory
    (AdicCompletion.restrict l E X (n + 1)) (AdicCompletion.finiteRestrict l E X n)
    (AdicCompletion.restrict l E X n)
    (AdicCompletion.restrict l E U (n + 1)) (AdicCompletion.finiteRestrict l E U n)
    (AdicCompletion.restrict l E U n)
    (CondensedRing.derivedComapUpperStarIso
      (DerivedNakayama.reductionRing l E (n + 2)) j).symm
    (CondensedRing.derivedComapUpperStarIso (AdicCompletion.transitionRing l E n) j).symm
    (CondensedRing.derivedComapUpperStarIso
      (DerivedNakayama.reductionRing l E (n + 1)) j).symm
    _ _ (AdicCompletion.restrictComp l E X n).symm
    (AdicCompletion.restrictComp l E U n).symm (hc X) (hc U) h M
  with_unfolding_all exact hp

end AlgebraicGeometry.ProEtale
