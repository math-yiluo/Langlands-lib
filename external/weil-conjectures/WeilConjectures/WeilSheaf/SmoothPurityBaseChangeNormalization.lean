/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescentNormalization
public import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedForgetMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionMapDerived

/-!
# The ordinary base-change square underlying descent

These equations identify the specified descent comparison with the ordinary
base-change mate, first on sheaves and then on derived categories.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L l : C ⥤ D} {R : D ⥤ C} {L' l' : C' ⥤ D'} {R' : D' ⥤ C'}
  {G g : C ⥤ C'} {H h : D ⥤ D'}

/-- Transport the specified exchange map through isomorphisms of the left functors. -/
lemma traceExchange_eq_of_iso (adj : L ⊣ R) (adj' : L' ⊣ R')
    (eL : L ≅ l) (eL' : L' ≅ l') (eG : G ≅ g) (eH : H ≅ h)
    (θ : G ⋙ L' ≅ L ⋙ H) (θ' : g ⋙ l' ≅ l ⋙ h)
    (hθ : ∀ K, l'.map (eG.inv.app K) ≫ eL'.inv.app (G.obj K) ≫ θ.hom.app K =
      θ'.hom.app K ≫ h.map (eL.inv.app K) ≫ eH.inv.app (L.obj K)) (K : D) :
    eG.inv.app (R.obj K) ≫ (exchangeRight adj adj' θ).app K ≫ R'.map (eH.hom.app K) =
      (exchangeRight (adj.ofNatIsoLeft eL) (adj'.ofNatIsoLeft eL') θ').app K := by
  have he := map_exchangeRight_app_of_comm adj adj' θ
    (adj.ofNatIsoLeft eL) (adj'.ofNatIsoLeft eL') θ'
    (HB := 𝟭 _) (HA := 𝟭 _) (HB' := 𝟭 _) (HA' := 𝟭 _)
    (Functor.leftUnitor _ ≪≫ eL.symm ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ eL'.symm ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ eG.symm ≪≫ (Functor.rightUnitor _).symm)
    (Functor.leftUnitor _ ≪≫ eH.symm ≪≫ (Functor.rightUnitor _).symm)
    (fun K ↦ by simp) (fun K ↦ by simp) (fun K ↦ by simpa using hθ K) K
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_id] at he
  rw [← Category.assoc, he, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.map_id, Category.comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}} {s : X ⟶ Spec (.of k)}
  {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y} {h : f ≫ t = s}

/-- The square obtained by forgetting descent is the specified weakly étale square. -/
lemma ordinaryTraceDescentIso_eq_lowerStarBaseChangeIso
    (hc : UpperStarWeilCompatible Λ f h) :
    Endofunctor.IsoAlgebra.ordinaryTraceDescentIso
      (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)
      (geometricFiberWeilLowerStar Λ s)
      (T₀ := (s.geometricFiberProj)^*⟦Λ⟧) (Iso.refl _)
      (geometricFiberWeilLowerStar Λ t)
      (S₀ := (t.geometricFiberProj)^*⟦Λ⟧) (Iso.refl _)
      (asIso (lowerStarGeometricFiberWeilBaseChange hc)) =
        lowerStarBaseChangeIso Λ (Scheme.Hom.isPullback_geometricFiberMap f h).flip := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa [Endofunctor.IsoAlgebra.ordinaryTraceDescentIso,
    Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso, lowerStarBaseChangeIso] using
    lowerStarGeometricFiberWeilBaseChange_app_forget Λ hc M

section Ordinary

variable {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The specified ordinary derived base-change comparison is the derived mate. -/
lemma rightDerivedLowerStarBaseChangeIso_hom_app_eq_derivedBaseChange
    (sq : IsPullback g' f' f g) [WeaklyEtale g] [WeaklyEtale g']
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerStarBaseChangeIso Λ sq).hom.app K =
      ((upperStarLowerStarAdjunction Λ f).derivedBaseChange
        (upperStarLowerStarAdjunction Λ f')
        (upperStarSquareComparison Λ sq.toCommSq)).app K := by
  have he := Adjunction.traceExchange_eq_of_iso
    (upperStarLowerStarAdjunction Λ f).derivedAdjunction
    (upperStarLowerStarAdjunction Λ f').derivedAdjunction
    (upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory
    (upperStar Λ f').leftDerivedFunctorIsoMapDerivedCategory
    (upperStar Λ g).leftDerivedFunctorIsoMapDerivedCategory
    (upperStar Λ g').leftDerivedFunctorIsoMapDerivedCategory
    (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison Λ sq.toCommSq))
    (Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq.toCommSq))
    (Adjunction.leftDerivedFunctorSquareIso_hom_app
      (upperStarSquareComparison Λ sq.toCommSq)) K
  simpa only [rightDerivedLowerStarBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, asIso_hom,
    leftDerivedUpperStarIsoMapDerivedCategory, baseChangeMap,
    pullbackSquareComparison_eq_leftDerivedFunctorSquareIso,
    derivedUpperStarLowerStarAdjunction, Adjunction.derivedAdjunction_ofNatIsoLeft,
    Adjunction.exchangeRight_eq_mateEquiv, Adjunction.derivedBaseChange] using he

/-- Deriving the ordinary weakly étale square agrees with taking the derived mate. -/
lemma derivedBaseChange_eq_rightDerivedFunctorCommIso
    (sq : IsPullback g' f' f g) [WeaklyEtale g] [WeaklyEtale g'] :
    ((upperStarLowerStarAdjunction Λ f).derivedBaseChange
      (upperStarLowerStarAdjunction Λ f') (upperStarSquareComparison Λ sq.toCommSq)) =
        (Functor.rightDerivedFunctorCommIso (lowerStarBaseChangeIso Λ sq)).hom := by
  have hb : (mateEquiv (upperStarLowerStarAdjunction Λ f)
      (upperStarLowerStarAdjunction Λ f')
      (TwoSquare.mk _ _ _ _ (upperStarSquareComparison Λ sq.toCommSq).hom)) =
        (lowerStarBaseChangeIso Λ sq).hom := by
    simpa only [lowerStarBaseChangeIso, asIso_hom,
      ← Adjunction.exchangeRight_eq_mateEquiv] using
      (lowerStarBaseChange_eq Λ sq.toCommSq).symm
  simpa only [Adjunction.derivedBaseChange, Functor.mapDerivedCategorySquareIso_symm,
    Iso.symm_inv, Functor.rightDerivedFunctorCommIso] using
    Adjunction.derived_exact_forget_mate
      (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
      ((g)^*⟦Λ⟧) ((g')^*⟦Λ⟧) (upperStarSquareComparison Λ sq.toCommSq).symm
      (lowerStarBaseChangeIso Λ sq) hb

end Ordinary

/-- Forgetting the specified descended direct-image comparison gives ordinary base change. -/
lemma geometricFiberWeilRightDerivedLowerStarIso_forget
    (hc : UpperStarWeilCompatible Λ f h)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerStarBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap f h).flip).hom.app K =
      (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
        (Endofunctor.IsoAlgebra.forget _)).inv.app ((lowerStar Λ f).rightDerivedFunctor.obj K) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        ((geometricFiberWeilRightDerivedLowerStarIso hc).inv.app K) ≫
      (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
        (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)).hom.app
          ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj K) ≫
      (lowerStar Λ (Scheme.Hom.geometricFiberMap f h)).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
          (Endofunctor.IsoAlgebra.forget _)).hom.app K) := by
  rw [rightDerivedLowerStarBaseChangeIso_hom_app_eq_derivedBaseChange,
    derivedBaseChange_eq_rightDerivedFunctorCommIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap f h).flip]
  have he := Endofunctor.IsoAlgebra.traceDescentComparison_forget
    (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)
    (geometricFiberWeilLowerStar Λ s)
    (T₀ := (s.geometricFiberProj)^*⟦Λ⟧) (Iso.refl _)
    (geometricFiberWeilLowerStar Λ t)
    (S₀ := (t.geometricFiberProj)^*⟦Λ⟧) (Iso.refl _)
    (asIso (lowerStarGeometricFiberWeilBaseChange hc)) K
  rw [ordinaryTraceDescentIso_eq_lowerStarBaseChangeIso] at he
  have hs : Functor.mapDerivedCategoryNatIso
      (Iso.refl (geometricFiberWeilLowerStar Λ s ⋙ Endofunctor.IsoAlgebra.forget _)) =
      Iso.refl _ := Iso.ext Functor.mapDerivedCategoryNatIso_refl
  have ht : Functor.mapDerivedCategoryNatIso
      (Iso.refl (geometricFiberWeilLowerStar Λ t ⋙ Endofunctor.IsoAlgebra.forget _)) =
      Iso.refl _ := Iso.ext Functor.mapDerivedCategoryNatIso_refl
  simp only [hs, ht, Iso.trans_refl] at he
  dsimp only [Endofunctor.IsoAlgebra.traceDescentComparison,
    geometricFiberWeilRightDerivedLowerStarIso] at *
  exact_mod_proofs he

end AlgebraicGeometry.ProEtale.CondensedRing
