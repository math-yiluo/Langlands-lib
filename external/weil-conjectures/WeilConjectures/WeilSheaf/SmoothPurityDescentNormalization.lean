/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityDerivedSquareComp
public import WeilConjectures.Tactic.ExactModProofs

/-!
# Normalization of the descended proper-image comparison

The derived comparison used to descend a trace is fixed by its equation with the
right-derived units. This records that equation before forgetting the Weil structure.
-/

@[expose] public section

universe w₀ w w' v v' u u'

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type*} [Category A] [Abelian A]
  {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w} (IsoAlgebra F)]
  [HasDerivedCategory.{w'} (IsoAlgebra G)] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  (T : A ⥤ IsoAlgebra F) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  {T₀ : A ⥤ C} [T₀.Additive] [T₀.PreservesKInjectiveComplexes]
  (α : T ⋙ forget F ≅ T₀)

/-- The comparison with exact precomposition respects the right-derived unit. -/
@[reassoc]
lemma rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso_hom_fac
    (K : HomotopyCategory A (.up ℤ)) :
    (T ⋙ mapOfNatIso e).rightDerivedFunctorUnit.app K ≫
      (rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso e T α).hom.app
        (DerivedCategory.Qh.obj K) =
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e)).app K := by
  simp [rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso]

variable {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions B]
  {L₀ : A ⥤ B} [L₀.Additive]
  (S : B ⥤ IsoAlgebra G) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The derived descent square assembled from a sheaf comparison. -/
noncomputable def traceDescentComparison (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e) :
    T.mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor ≅
      L₀.rightDerivedFunctor ⋙ S.mapDerivedCategory :=
  (rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso e T α).symm ≪≫
    (Functor.rightDerivedFunctorNatIso β).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso L₀ S

omit [Abelian.HasKInjectiveResolutions B] in
/-- Normalization of the derived descent square by the two derived units. -/
lemma traceDescentComparison_inv_fac (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e)
    (K : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit L₀ S).app K ≫
      (traceDescentComparison e T α S β).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e)).app K := by
  have h₁ : (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit L₀ S).app K ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso L₀ S).inv.app
        (DerivedCategory.Qh.obj K) = (L₀ ⋙ S).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso]
  have h₂ : (L₀ ⋙ S).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso β).hom.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app K) ≫
          (T ⋙ mapOfNatIso e).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  simp only [traceDescentComparison, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂,
    rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso_hom_fac]

omit [Abelian.HasKInjectiveResolutions B] in
/-- The derived-unit normalization with the source unit expanded. -/
lemma traceDescentComparison_inv_fac' (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e)
    (K : HomotopyCategory A (.up ℤ)) :
    S.mapDerivedCategoryFactorsh.inv.app ((L₀.mapHomotopyCategory (.up ℤ)).obj K) ≫
        S.mapDerivedCategory.map (L₀.rightDerivedFunctorUnit.app K) ≫
        (traceDescentComparison e T α S β).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ mapOfNatIso e)) (.up ℤ)).inv.app K) ≫
        (mapOfNatIso e).rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (mapOfNatIso e).rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.inv.app K) := by
  have h := traceDescentComparison_inv_fac e T α S β K
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.assoc,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app] at h
  exact h

variable {S₀ : B ⥤ D} [S₀.Additive] [PreservesFiniteLimits S₀] [PreservesFiniteColimits S₀]
  [PreservesFiniteLimits T₀] [PreservesFiniteColimits T₀]
  (αS : S ⋙ forget G ≅ S₀)

/-- The ordinary square obtained by forgetting a descent square. -/
noncomputable def ordinaryTraceDescentIso (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e) :
    L₀ ⋙ S₀ ≅ T₀ ⋙ L :=
  (Functor.isoWhiskerLeft L₀ αS).symm ≪≫
    (Functor.associator L₀ S (forget G)).symm ≪≫
    Functor.isoWhiskerRight β (forget G) ≪≫
    Functor.associator T (mapOfNatIso e) (forget G) ≪≫
    Functor.isoWhiskerLeft T (mapOfNatIsoCompForgetIso e) ≪≫
    (Functor.associator T (forget F) L).symm ≪≫ Functor.isoWhiskerRight α L

omit [Abelian.HasKInjectiveResolutions B] in
/-- Forgetting the derived descent comparison gives the derived ordinary square. -/
theorem traceDescentComparison_forget (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e)
    (K : DerivedCategory A) :
    (Functor.rightDerivedFunctorCommIso (ordinaryTraceDescentIso e T α S αS β)).hom.app K =
      ((Functor.mapDerivedCategoryCompIso S (forget G)) ≪≫
        Functor.mapDerivedCategoryNatIso αS).inv.app (L₀.rightDerivedFunctor.obj K) ≫
      (forget G).mapDerivedCategory.map ((traceDescentComparison e T α S β).inv.app K) ≫
      (rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app (T.mapDerivedCategory.obj K) ≫
      L.rightDerivedFunctor.map
        (((Functor.mapDerivedCategoryCompIso T (forget F)) ≪≫
          Functor.mapDerivedCategoryNatIso α).hom.app K) := by
  apply Functor.traceDerivedSquare_comp (mapOfNatIsoCompForgetIso e) β
    (ordinaryTraceDescentIso e T α S αS β)
    (rightDerivedFunctorMapOfNatIsoCompForgetIso F e)
    (traceDescentComparison e T α S β).symm
    (Functor.rightDerivedFunctorCommIso (ordinaryTraceDescentIso e T α S αS β))
  · exact Functor.rightDerivedFunctorCommIso_fac_app' (mapOfNatIsoCompForgetIso e)
  · exact traceDescentComparison_inv_fac' e T α S β
  · exact Functor.rightDerivedFunctorCommIso_fac_app _
  · intro M
    simp [ordinaryTraceDescentIso]

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {B B' C D : Type*} [Category B] [Category B'] [Category C] [Category D]
  {F : C ⥤ C} {G : D ⥤ D} {l : B ⥤ B'} {r : B' ⥤ B}
  {L : C ⥤ D} {R : D ⥤ C} (adjB : l ⊣ r) (adj : L ⊣ R)
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (hmate : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) = eR.hom)
  {PB : B ⥤ IsoAlgebra F} {PB' : B' ⥤ IsoAlgebra G}

/-- Compute a lifted mate using explicitly identified underlying functors. -/
lemma traceMate_forget {P₀ : B ⥤ C} {P₀' : B' ⥤ D}
    (hP : PB ⋙ forget F = P₀) (hP' : PB' ⋙ forget G = P₀')
    (θ : l ⋙ PB' ≅ PB ⋙ mapOfNatIso eL) (θ₀ : l ⋙ P₀' ≅ P₀ ⋙ L)
    (hθ : ∀ b, (θ.inv.app b).hom.f = eqToHom (by rw [← hP]; rfl) ≫ θ₀.inv.app b ≫
      eqToHom (by rw [← hP']; rfl)) (b' : B') :
    ((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR hmate)
      (TwoSquare.mk _ _ _ _ θ.inv)).app b').hom.f =
      eqToHom (by rw [← hP]; rfl) ≫
        (mateEquiv adjB adj (TwoSquare.mk _ _ _ _ θ₀.inv)).app b' ≫
        eqToHom (by rw [← hP']; rfl) := by
  subst hP hP'
  have hθ' : Functor.whiskerRight θ.inv (forget G) = θ₀.inv := by
    ext b
    simpa using hθ b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [mateEquiv_mapOfNatIsoAdjunction_app_hom_f, hθ']

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}} {s : X ⟶ Spec (.of k)}
  {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y} {h : f ≫ t = s}

/-- Forgetting the descended sheaf base-change map gives the ordinary base-change map. -/
lemma lowerStarGeometricFiberWeilBaseChange_app_forget
    (hc : UpperStarWeilCompatible Λ f h)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarGeometricFiberWeilBaseChange hc).app M).hom.f =
      (lowerStarBaseChange Λ
        (Scheme.Hom.isPullback_geometricFiberMap f h).flip.toCommSq).app M := by
  have he := Endofunctor.IsoAlgebra.traceMate_forget
    (upperStarLowerStarAdjunction Λ f)
    (upperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap f h))
    (upperStarGeometricFiberMapCompFrobeniusIso Λ f h)
    (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)
    (Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv _ _)
    (P₀ := (t.geometricFiberProj)^*⟦Λ⟧) (P₀' := (s.geometricFiberProj)^*⟦Λ⟧) rfl rfl
    (upperStarCompGeometricFiberWeilLowerStarIso hc) (geometricFiberUpperStarComparison Λ f h)
    (fun N ↦ by simp [upperStarCompGeometricFiberWeilLowerStarIso]) M
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  rw [geometricFiberUpperStarComparison, Iso.symm_inv,
    ← Adjunction.exchangeRight_eq_mateEquiv, ← lowerStarBaseChange_eq] at he
  dsimp only [lowerStarGeometricFiberWeilBaseChange]
  exact_mod_proofs he

end AlgebraicGeometry.ProEtale.CondensedRing
