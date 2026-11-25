/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit

/-!
# The derived coefficient comparisons as mates

Let `a : Λ ⟶ Λ'` be a flat morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. Write `T = L(Ext_a)` for the derived extension of scalars and `Res = D(Res_a)` for the
levelwise restriction of scalars, so that `T ⊣ Res`. The derived comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` are built from the
commutation `ρ_f : Rf_* ⋙ Res ≅ Res ⋙ Rf_*` (`ProEtale.CondensedRing.derivedComapLowerStarIso`)
by mates and conjugates. This file identifies them with mates of the commutation
`τ_f : Res ⋙ Lf^* ≅ Lf^* ⋙ Res` (`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`),
induced levelwise by the underived commutation `ProEtale.CondensedRing.comapUpperStarIso`:

* `ρ_f` is the mate of `τ_f` for the derived adjunctions `Lf^* ⊣ Rf_*`
  (`ProEtale.CondensedRing.derivedComapLowerStarIso_hom_eq_mateEquiv`);
* hence **(Pull)** `Lf^* ⋙ T ≅ T ⋙ Lf^*` (`ProEtale.CondensedRing.derivedPullIso`), the conjugate
  of `ρ_f`, is the mate of `τ_f` for `T ⊣ Res`
  (`ProEtale.CondensedRing.mateEquiv_derivedPullIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (G : D ⥤ E) [G.Additive] [L.PreservesKInjectiveComplexes]

/-- For an exact functor `L` preserving K-injective complexes, the identification
`R(L ⋙ G) ≅ D(L) ⋙ RG` is the composition isomorphism `R(L ⋙ G) ≅ RL ⋙ RG` followed by
`RL ≅ D(L)`. -/
lemma mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso_eq
    (hG : ∀ (K : CochainComplex C ℤ) [K.IsKInjective], IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) :
    mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso L G hG =
      rightDerivedFunctorCompIso L G ≪≫
        isoWhiskerRight L.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor := by
  have := isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_of_isIso L G hG
  ext1
  apply (L ⋙ G).rightDerivedFunctor.rightDerived_ext (L ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K
  simp only [mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso, rightDerivedFunctorCompIso,
    Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, comp_obj,
    whiskerLeft_comp, rightDerived_fac_app_assoc, rightDerived_fac_app, rightDerivedNatIso_hom,
    Iso.refl_hom, Category.id_comp, whiskerRight_app, rightDerivedNatTrans,
    rightDerivedFunctorCompUnit, mapDerivedCategoryCompRightDerivedFunctorUnit,
    associator_hom_app, associator_inv_app, Category.comp_id, Category.assoc]
  have h := NatTrans.congr_app L.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← Functor.map_comp, h]

end CategoryTheory.Functor

namespace CategoryTheory

section TransportedSquare

variable {DZ DY DX EZ EY EX : Type*} [Category* DZ] [Category* DY] [Category* DX]
  [Category* EZ] [Category* EY] [Category* EX]
  {RZ : DZ ⥤ EZ} {RY : DY ⥤ EY} {RX : DX ⥤ EX}
  {LG DG : DZ ⥤ DY} {LF DF : DY ⥤ DX} {LH DH : DZ ⥤ DX}
  {lg dg : EZ ⥤ EY} {lf df : EY ⥤ EX} {lh dh : EZ ⥤ EX}

/-- Commutation squares `R ⋙ l ≅ L ⋙ R` transported along isomorphisms `ε : l ≅ d` and
`ε' : L ≅ D` from commutation squares `S : R ⋙ d ≅ D ⋙ R` are compatible with composition
isomorphisms `c : lh ≅ lg ⋙ lf` and `c' : LH ≅ LG ⋙ LF` transported from composition
isomorphisms `dh ≅ dg ⋙ df` and `DH ≅ DG ⋙ DF` with which the squares `S` are compatible. -/
lemma transportedSquare_comp_hom_app (εG : LG ≅ DG) (εF : LF ≅ DF) (εH : LH ≅ DH)
    (εg : lg ≅ dg) (εf : lf ≅ df) (εh : lh ≅ dh)
    (Sg : RZ ⋙ dg ≅ DG ⋙ RY) (Sf : RY ⋙ df ≅ DF ⋙ RX) (Sh : RZ ⋙ dh ≅ DH ⋙ RX)
    (tri : dh ≅ dg ⋙ df) (tri' : DH ≅ DG ⋙ DF)
    (H : ∀ K, Sh.hom.app K ≫ RX.map (tri'.hom.app K) =
      tri.hom.app (RZ.obj K) ≫ df.map (Sg.hom.app K) ≫ Sf.hom.app (DG.obj K))
    (c : lh ≅ lg ⋙ lf) (c' : LH ≅ LG ⋙ LF)
    (hc : ∀ K, c.hom.app K = εh.hom.app K ≫ tri.hom.app K ≫ df.map (εg.inv.app K) ≫
      εf.inv.app (lg.obj K))
    (hc' : ∀ K, c'.hom.app K = εH.hom.app K ≫ tri'.hom.app K ≫ DF.map (εG.inv.app K) ≫
      εF.inv.app (LG.obj K)) (K : DZ) :
    c.hom.app (RZ.obj K) ≫
        lf.map (εg.hom.app (RZ.obj K) ≫ Sg.hom.app K ≫ RY.map (εG.inv.app K)) ≫
        εf.hom.app (RY.obj (LG.obj K)) ≫ Sf.hom.app (LG.obj K) ≫ RX.map (εF.inv.app (LG.obj K)) =
      (εh.hom.app (RZ.obj K) ≫ Sh.hom.app K ≫ RX.map (εH.inv.app K)) ≫
        RX.map (c'.hom.app K) := by
  have hnat := Sf.hom.naturality (εG.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [hc, hc']
  simp only [Category.assoc, NatIso.naturality_1_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% (H K)]

end TransportedSquare

/-- Transporting the right adjoints in a conjugate square gives a mate square whenever the
other pair of adjunctions sends its proposed right square to the transported conjugate. -/
private lemma isMateSquare_of_conjugateIsoEquiv_ofNatIsoRight
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ R₁' : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₄} {R₂ : C₄ ⥤ C₂}
    {L₃ : C₁ ⥤ C₃} {R₃ : C₃ ⥤ C₁} {L₄ : C₃ ⥤ C₄} {R₄ R₄' : C₄ ⥤ C₃}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₃ ⊣ R₃) (b₂ : L₄ ⊣ R₄)
    (e₁ : R₁ ≅ R₁') (e₄ : R₄ ≅ R₄') (ρ : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁)
    (τ : R₁' ⋙ L₃ ≅ L₂ ⋙ R₄')
    (hτ : mateEquiv a₂ b₁ τ.hom =
      Functor.whiskerLeft R₂ e₁.inv ≫ ρ.inv ≫ Functor.whiskerRight e₄.hom R₃) :
    (a₁.ofNatIsoRight e₁).IsMateSquare (b₂.ofNatIsoRight e₄)
      ((conjugateIsoEquiv (b₁.comp b₂) (a₁.comp a₂)).symm ρ) τ := by
  rw [Adjunction.isMateSquare_iff, mateEquiv_ofNatIsoRight]
  apply (mateEquiv a₂ b₁).injective
  rw [hτ, mateEquiv_whiskerRight_comp, mateEquiv_comp_whiskerLeft,
    ← conjugateEquiv_comp_eq_mateEquiv_mateEquiv]
  have hρ : conjugateEquiv (a₁.comp a₂) (b₁.comp b₂)
      ((conjugateIsoEquiv (b₁.comp b₂) (a₁.comp a₂)).symm ρ).inv = ρ.inv :=
    congrArg Iso.inv ((conjugateIsoEquiv (b₁.comp b₂) (a₁.comp a₂)).apply_symm_apply ρ)
  rw [hρ]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The commutation `τ_f : Res ⋙ Lf^*_Λ ≅ Lf^*_{Λ'} ⋙ Res` of the levelwise restriction of
scalars with the derived pullbacks, induced levelwise by the underived commutation
`ProEtale.CondensedRing.comapUpperStarIso` (the derived pullbacks being computed levelwise). -/
noncomputable def derivedComapLeftDerivedUpperStarIso :
    D(Mod.comap (coefficientMap a Y)) ⋙ L((f)^*⟦Λ⟧) ≅
      L((f)^*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a X)) :=
  Functor.isoWhiskerLeft _ (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso (comapUpperStarIso a f).symm ≪≫
    Functor.isoWhiskerRight (f)^*⟦Λ'⟧.leftDerivedFunctorIsoMapDerivedCategory.symm _

/-- The components of `τ_f`. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))) :
    (derivedComapLeftDerivedUpperStarIso a f).hom.app K =
      (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app
          (D(Mod.comap (coefficientMap a Y)).obj K) ≫
        (Functor.mapDerivedCategorySquareIso (comapUpperStarIso a f).symm).hom.app K ≫
        D(Mod.comap (coefficientMap a X)).map
          ((f)^*⟦Λ'⟧.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) :=
  rfl

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

/-- The commutation `ρ_f : Rf_* ⋙ Res ≅ Res ⋙ Rf_*` is the mate of
`τ_f : Res ⋙ Lf^* ≅ Lf^* ⋙ Res` for the derived adjunctions `Lf^* ⊣ Rf_*`. -/
lemma derivedComapLowerStarIso_hom_eq_mateEquiv :
    (derivedComapLowerStarIso a f).hom =
      mateEquiv (derivedUpperStarLowerStarAdjunction Λ' f)
        (derivedUpperStarLowerStarAdjunction Λ f)
        (derivedComapLeftDerivedUpperStarIso a f).hom := by
  have hunit (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
      (Mod.comap (coefficientMap a Y)).map ((upperStarLowerStarAdjunction Λ' f).unit.app N) ≫
        (comapLowerStarIso a f).hom.app ((f)^*⟦Λ'⟧.obj N) =
      (upperStarLowerStarAdjunction Λ f).unit.app ((Mod.comap (coefficientMap a Y)).obj N) ≫
        (f)_*⟦Λ⟧.map ((comapUpperStarIso a f).symm.hom.app N) := by
    have h := squareCompatible_upperStarLowerStarAdjunction_unit a f N
    simp only [Functor.id_obj, Functor.comp_obj, Functor.pasteSquareIso_hom_app,
      Functor.idSquareIso_hom_app, Category.id_comp] at h
    rw [Iso.symm_hom, ← h, Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    simp
  have h := Adjunction.mateEquiv_derivedAdjunction_restrict (upperStarLowerStarAdjunction Λ f)
    (upperStarLowerStarAdjunction Λ' f) (comapUpperStarIso a f).symm (comapLowerStarIso a f)
    hunit (fun _ _ ↦ inferInstance)
  refine Eq.trans ?_ h.symm
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso_eq]
  simp only [derivedComapLowerStarIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc]
  rfl

/-- **(Pull)** is the mate of `τ_f` for the derived adjunctions `T ⊣ Res`: the conjugate of
`ρ_f` along the composite adjunctions is obtained by taking mates twice
(`CategoryTheory.conjugateEquiv_comp_eq_mateEquiv_mateEquiv`), and `ρ_f` is the mate of `τ_f`. -/
lemma mateEquiv_derivedPullIso_hom :
    mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
        (TwoSquare.mk _ _ _ _ (derivedPullIso a f).hom) =
      (derivedComapLeftDerivedUpperStarIso a f).hom := by
  apply (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' f)
    (derivedUpperStarLowerStarAdjunction Λ f)).injective
  rw [← derivedComapLowerStarIso_hom_eq_mateEquiv, ← conjugateEquiv_comp_eq_mateEquiv_mateEquiv]
  exact congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (derivedComapLowerStarIso a f))

/-- **(Push)** is the mate of the inverse of **(Pull)** for the derived adjunctions
`Lf^* ⊣ Rf_*`. -/
lemma derivedPushHom_eq_mateEquiv :
    derivedPushHom a f = mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ' f)
      (TwoSquare.mk _ _ _ _ (derivedPullIso a f).inv) := by
  have h := conjugateEquiv_comp_eq_mateEquiv_mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedUpperStarLowerStarAdjunction Λ' f) (derivedPullIso a f).inv
  have h₂ : conjugateEquiv ((derivedUpperStarLowerStarAdjunction Λ f).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
        (derivedUpperStarLowerStarAdjunction Λ' f)) (derivedPullIso a f).inv =
      (derivedComapLowerStarIso a f).inv := congrArg Iso.inv ((conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
      (derivedUpperStarLowerStarAdjunction Λ' f))
    ((derivedUpperStarLowerStarAdjunction Λ f).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))).apply_symm_apply
    (derivedComapLowerStarIso a f))
  rw [h₂] at h
  exact ((mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))).symm_apply_eq).mpr h

section OpenImmersion

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **(Shriek)** for an open immersion `j` and **(Pull)** for `j` are mates: the mate of the
inverse of `j_! ⋙ T ≅ T ⋙ j_!` for the adjunctions `j_! ⊣ Lj^*` is `Lj^* ⋙ T ≅ T ⋙ Lj^*`.
Both are mates along `T ⊣ Res` of the levelwise commutation of `Res` with `j^*`. -/
lemma isMateSquare_derivedOpenImmersionShriekIso_derivedPullIso :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm).IsMateSquare
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ' j).symm)
      (derivedOpenImmersionShriekIso a j) (derivedPullIso a j) := by
  apply isMateSquare_of_conjugateIsoEquiv_ofNatIsoRight
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j)
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ' j).symm
    (derivedComapUpperStarIso a j) (derivedPullIso a j)
  rw [mateEquiv_derivedPullIso_hom]
  ext K
  simp [derivedComapLeftDerivedUpperStarIso, derivedComapUpperStarIso,
    leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion,
    Functor.mapDerivedCategoryNatIso_symm]

end OpenImmersion

section Comp

variable {Z : Scheme.{u}} (g : Y ⟶ Z)

omit [IsCommMonObj Λ'] [∀ X : Scheme.{u},
  PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] in
/-- The components of the composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of derived pullbacks
of module objects, in terms of the functors induced levelwise by the exact pullbacks. -/
lemma leftDerivedUpperStarComp_hom_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ f g).hom.app K =
      (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app K ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f g)).hom.app K ≫
        D((f)^*⟦Λ⟧).map ((g)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.inv.app (L((g)^*⟦Λ⟧).obj K) := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso]

omit [∀ X : Scheme.{u},
  PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] in
/-- The commutations `τ` of the levelwise restriction of scalars with the derived pullbacks are
compatible with the composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
lemma derivedComapLeftDerivedUpperStarIso_comp_hom_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ' Z))) :
    (leftDerivedUpperStarComp Λ f g).hom.app (D(Mod.comap (coefficientMap a Z)).obj K) ≫
        L((f)^*⟦Λ⟧).map ((derivedComapLeftDerivedUpperStarIso a g).hom.app K) ≫
        (derivedComapLeftDerivedUpperStarIso a f).hom.app (L((g)^*⟦Λ'⟧).obj K) =
      (derivedComapLeftDerivedUpperStarIso a (f ≫ g)).hom.app K ≫
        D(Mod.comap (coefficientMap a X)).map ((leftDerivedUpperStarComp Λ' f g).hom.app K) := by
  have H := fun K' ↦ Functor.mapDerivedCategorySquareIso_hom_app_comp
    (comapUpperStarIso a g).symm (comapUpperStarIso a f).symm (comapUpperStarIso a (f ≫ g)).symm
    (upperStarComp Λ f g) (upperStarComp Λ' f g) (fun N ↦ by
      have h := squareCompatible_upperStarComp a f g N
      simp only [Functor.comp_obj, Functor.pasteSquareIso_hom_app] at h
      simp only [Iso.symm_hom]
      rw [← cancel_epi ((comapUpperStarIso a (f ≫ g)).hom.app N), Iso.hom_inv_id_app_assoc,
        ← reassoc_of% h]
      simp [← Functor.map_comp_assoc]) K'
  exact transportedSquare_comp_hom_app _ _ _ _ _ _ _ _ _ _ _ H _ _
    (leftDerivedUpperStarComp_hom_app f g) (leftDerivedUpperStarComp_hom_app f g) K

/-- **(Pull)** is compatible with the composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
lemma squareCompatible_leftDerivedUpperStarComp :
    NatTrans.SquareCompatible (derivedPullIso a (f ≫ g))
      (Functor.pasteSquareIso (derivedPullIso a g) (derivedPullIso a f))
      (leftDerivedUpperStarComp Λ f g).hom (leftDerivedUpperStarComp Λ' f g).hom := by
  exact NatTrans.SquareCompatible.of_mateEquiv_paste
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)) _ _ _
    (mateEquiv_derivedPullIso_hom a (f ≫ g)) (mateEquiv_derivedPullIso_hom a g)
    (mateEquiv_derivedPullIso_hom a f) (derivedComapLeftDerivedUpperStarIso_comp_hom_app a f g)

end Comp

end AlgebraicGeometry.ProEtale.CondensedRing
