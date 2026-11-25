/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIdentify
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedPlus

/-!
# Derived pushforward commutes with `E ⊗_{𝒪_E} -` on bounded below objects

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes. The derived comparison
**(Push)** `E_Y ⊗ᴸ Rf_* K ⟶ Rf_*(E_X ⊗ᴸ K)` for the inclusion `𝒪̲_E ⟶ E̲` is an isomorphism for
every bounded below `K ∈ D(𝒪_{E,X})`
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`).

For a general flat coefficient change `a`, the derived (Push) on the image of a complex `I` is
identified with the underived (Push), through the units of the right derived pushforwards and
the counits of the derived extensions of scalars
(`ProEtale.CondensedRing.derivedPushHom_app_Qh_fac`). This is proved through the adjunction
`L(Ext) ⊣ D(Res)`, using the formulas for its unit and counit on complexes
(`CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh`) and for
`derivedComapLowerStarIso` (`ProEtale.CondensedRing.derivedComapLowerStarIso_inv_app_Qh`).

For `𝒪_E ⟶ E`, represent `K` by a bounded below complex `I` of injectives. The unit of `Rf_*` is
an isomorphism at `I`, `I` being K-injective. The counits of the exact extensions of scalars are
isomorphisms. The underived (Push) is an isomorphism. Finally, the unit of `Rf_*` is an
isomorphism at `E_X ⊗ I`, a bounded below complex of `f_*`-acyclic objects.
-/

@[expose] public section

universe v u' u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

/-- A compatibility of units determines a factorization of the mate. -/
private lemma pushHom_fac_of_unit_compatibility
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {F : A ⥤ C} {U : C ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    (adjX : F ⊣ U) (adjY : G ⊣ V) (P : A ⥤ B) (P' : C ⥤ D)
    (β : U ⋙ P ⟶ P' ⋙ V) {Z : A} {ZY : B} {W : C} {DY DE : D}
    (u : ZY ⟶ P.obj Z) (cX : F.obj Z ⟶ W) (cY : G.obj ZY ⟶ DY)
    (b : DY ⟶ DE) (r : DE ⟶ P'.obj W)
    (h : u ≫ P.map (adjX.unit.app Z ≫ U.map cX) ≫ β.app W =
      adjY.unit.app ZY ≫ V.map cY ≫ V.map b ≫ V.map r) :
    G.map u ≫ ((mateEquiv adjX adjY).symm β).app Z ≫ P'.map cX = cY ≫ b ≫ r := by
  apply (adjY.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  dsimp only [Functor.comp_obj]
  rw [adjY.unit_naturality_assoc]
  have hm := (unit_mateEquiv_symm adjX adjY (TwoSquare.mk _ _ _ _ β) Z).symm
  rw [reassoc_of% hm]
  have hn := β.naturality cX
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Functor.map_comp_assoc]
  exact h

/-- Transport the underived unit square through the comparison maps before taking its mate. -/
private lemma pushHom_fac_of_comparison_units
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {F : A ⥤ C} {U : C ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    (adjX : F ⊣ U) (adjY : G ⊣ V) (P : A ⥤ B) (P' : C ⥤ D)
    (β : U ⋙ P ⟶ P' ⋙ V) {Z Z' : A} {ZY H B₁ B₂ : B} {W : C} {DY DE : D}
    (u : ZY ⟶ P.obj Z) (cX : F.obj Z ⟶ W) (cY : G.obj ZY ⟶ DY)
    (b : DY ⟶ DE) (r : DE ⟶ P'.obj W)
    (x : Z ⟶ Z') (z : Z' ⟶ U.obj W) (y : ZY ⟶ H) (v₀ : H ⟶ V.obj DY)
    (p : ZY ⟶ B₁) (t : B₁ ⟶ P.obj Z') (q : B₁ ⟶ B₂)
    (v₁ : B₂ ⟶ V.obj DE) (k : H ⟶ B₂)
    (hX : adjX.unit.app Z ≫ U.map cX = x ≫ z)
    (hY : adjY.unit.app ZY ≫ V.map cY = y ≫ v₀)
    (hP : p ≫ t = u ≫ P.map x)
    (hβ : t ≫ P.map z ≫ β.app W = q ≫ v₁ ≫ V.map r)
    (hV : k ≫ v₁ = v₀ ≫ V.map b) (hxy : y ≫ k = p ≫ q) :
    G.map u ≫ ((mateEquiv adjX adjY).symm β).app Z ≫ P'.map cX = cY ≫ b ≫ r := by
  apply pushHom_fac_of_unit_compatibility adjX adjY P P' β
  rw [hX, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hP, hβ, reassoc_of% hY, ← reassoc_of% hV, reassoc_of% hxy]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ'] in
/-- The underived (Push) on homotopy categories is compatible with the units of extension of
scalars, on the image of a complex. -/
lemma unit_app_comp_map_mapHomotopyCategory_pushHom_app
    (I : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :
    ((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
        (ComplexShape.up ℤ)).unit.app
        ((((f)_*⟦Λ⟧).mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj I)) ≫
      ((Mod.comap (coefficientMap a Y)).mapHomotopyCategory _).map
        ((NatTrans.mapHomotopyCategory (pushHom a f) _).app
          ((HomotopyCategory.quotient _ _).obj I)) =
    (((f)_*⟦Λ⟧).mapHomotopyCategory _).map
        (((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).inv _).app
        (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory _).obj
          ((HomotopyCategory.quotient _ _).obj I)) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp]
  erw [← Functor.map_comp]
  refine congrArg _ ?_
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact (unit_mateEquiv_symm _ _ (TwoSquare.mk _ _ _ _ (comapLowerStarIso a f).inv) (I.X n)).symm

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

omit [IsCommMonObj Λ'] in
/-- `derivedComapLowerStarIso` on the image of a complex, inverse form. -/
lemma derivedComapLowerStarIso_inv_app_Qh
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
      (ComplexShape.up ℤ)) :
    ((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app
        (((Mod.comap (coefficientMap a X)).mapHomotopyCategory _).obj K) ≫
      ((f)_*⟦Λ⟧).rightDerivedFunctor.map
        ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.inv.app K) ≫
      (derivedComapLowerStarIso a f).inv.app (Qh.obj K) =
    Qh.map ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).inv _).app K) ≫
      (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.inv.app
        ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K) ≫
      (Mod.comap (coefficientMap a Y)).mapDerivedCategory.map
        (((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app K) := by
  have h := derivedComapLowerStarIso_hom_app_Qh a f K
  have hc : (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K ≫
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).inv _).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  have hc' : (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).inv _).app K ≫
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  have : IsIso ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K) :=
    ⟨_, hc, hc'⟩
  have : IsIso (Qh.map ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K)) :=
    Functor.map_isIso _ _
  have : Epi ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app
      ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K) ≫
    Qh.map ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K)) := epi_comp _ _
  rw [← cancel_epi ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app
      ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K) ≫
    Qh.map ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K))]
  simp only [Category.assoc]
  have hQ : Qh.map ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K) ≫
      Qh.map ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).inv _).app K) = 𝟙 _ := by
    rw [← Functor.map_comp, hc, CategoryTheory.Functor.map_id]
  rw [← reassoc_of% h, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  erw [reassoc_of% hQ]
  erw [Iso.hom_inv_id_app_assoc]

/-- The derived (Push) on the image of a complex `I`, through the units of the right derived
pushforwards and the counits of the derived extensions of scalars, is the underived (Push). -/
lemma derivedPushHom_app_Qh_fac
    (I : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :
    (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.map
        (((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
      (derivedPushHom a f).app (Qh.obj ((HomotopyCategory.quotient _ _).obj I)) ≫
      ((f)_*⟦Λ'⟧).rightDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj I)) =
    (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app
        ((((f)_*⟦Λ⟧).mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj I)) ≫
      Qh.map ((NatTrans.mapHomotopyCategory (pushHom a f) _).app
        ((HomotopyCategory.quotient _ _).obj I)) ≫
      ((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app
        (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory _).obj
          ((HomotopyCategory.quotient _ _).obj I)) := by
  have hX := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh (coefficientMap a X)
    ((HomotopyCategory.quotient _ _).obj I)
  have hY := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh (coefficientMap a Y)
    ((((f)_*⟦Λ⟧).mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj I))
  have hP := ((f)_*⟦Λ⟧).rightDerivedFunctorUnit.naturality
    (((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ _).obj I))
  have hβ := derivedComapLowerStarIso_inv_app_Qh a f
    (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory _).obj
      ((HomotopyCategory.quotient _ _).obj I))
  have hV := (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.inv.naturality
    ((NatTrans.mapHomotopyCategory (pushHom a f) _).app ((HomotopyCategory.quotient _ _).obj I))
  have hxy := congrArg Qh.map (unit_app_comp_map_mapHomotopyCategory_pushHom_app a f I)
  simp only [Functor.map_comp] at hxy
  exact pushHom_fac_of_comparison_units
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    ((f)_*⟦Λ⟧).rightDerivedFunctor ((f)_*⟦Λ'⟧).rightDerivedFunctor
    (derivedComapLowerStarIso a f).inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ hX hY hP hβ hV hxy

section Integral

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **(Push) for `𝒪_E ⟶ E` on bounded below objects**: for a quasi-compact quasi-separated `f`
and a bounded below `K ∈ D(𝒪_{E,X})`, the comparison `E_Y ⊗ᴸ Rf_* K ⟶ Rf_*(E_X ⊗ᴸ K)` is an
isomorphism. -/
theorem isIso_derivedPushHom_app_padicIntegers_of_isGE
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app K) := by
  -- Bind the existence proofs before eliminating them, to avoid abstracting over the large goal.
  have hK := K.exists_iso_Q_obj_of_isGE n
  obtain ⟨T, _, ⟨e⟩⟩ := hK
  have hT := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T n
  obtain ⟨I, i, _, hI, _⟩ := hT
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I n
  rw [NatTrans.isIso_app_iff_of_iso _
    (e ≪≫ asIso (Q.map i) ≪≫ ((quotientCompQhIso _).app I).symm)]
  dsimp only [Functor.comp_obj]
  have h := derivedPushHom_app_Qh_fac (padicIntegersRingObjToContinuousMapRingObj ℓ E) f I
  have : ∀ k, IsIso (((NatTrans.mapHomologicalComplex
      (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f) (ComplexShape.up ℤ)).app I).f
        k) := fun k ↦
    (inferInstance : IsIso ((pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app
      (I.X k)))
  have : IsIso ((NatTrans.mapHomologicalComplex
      (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f) (ComplexShape.up ℤ)).app I) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((NatTrans.mapHomotopyCategory
      (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f) (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj I)) :=
    Functor.map_isIso (HomotopyCategory.quotient _ _) ((NatTrans.mapHomologicalComplex
      (pushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f) (ComplexShape.up ℤ)).app I)
  have : CochainComplex.IsStrictlyGE ((Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I) n :=
    (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi ↦
      show IsZero ((Mod.extendScalars _).obj (I.X i)) from
        Functor.map_isZero _ (I.isZero_of_isStrictlyGE n i hi)
  have : IsIso (((f)_*⟦Profinite.continuousMapRingObj E.1⟧).rightDerivedFunctorUnit.app
      (((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        X)).mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj I))) :=
    Functor.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE _ ((Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I) n fun k ↦
      rightAcyclic_lowerStar_of_rightAcyclic_forget _ f
        (rightAcyclic_lowerStar_extendScalars_of_injective ℓ E f (I.X k))
  have := IsIso.of_isIso_fac_left h
  have := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this
  -- Compare the instance arguments without unfolding the derived functors.
  with_reducible exact this

end Integral

end AlgebraicGeometry.ProEtale.CondensedRing
