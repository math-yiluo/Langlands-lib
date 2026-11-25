/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityExactDescentNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
public import WeilConjectures.WeilSheaf.SmoothPurityShriekFreeComparison
public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilConjectures.WeilSheaf.SmoothPurityInverseMateExchange

/-! # The geometric comparison underlying descended extension by zero -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {B B' C D : Type*} [Category B] [Category B'] [Category C] [Category D]
  {F : C ⥤ C} {G : D ⥤ D} {l : B ⥤ B'} {r : B' ⥤ B}
  {L : C ⥤ D} {R : D ⥤ C} (adjB : l ⊣ r) (adj : L ⊣ R)
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (hmate : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) = eR.hom)
  {PB : B ⥤ IsoAlgebra F} {PB' : B' ⥤ IsoAlgebra G}

/-- The inverse mate of a descent square is computed on the underlying objects. -/
lemma traceInverseMate_forget {P₀ : B ⥤ C} {P₀' : B' ⥤ D}
    (hP : PB ⋙ forget F = P₀) (hP' : PB' ⋙ forget G = P₀')
    (θ : r ⋙ PB ≅ PB' ⋙ mapOfNatIso eR) (θ₀ : r ⋙ P₀ ≅ P₀' ⋙ R)
    (hθ : ∀ b', (θ.hom.app b').hom.f = eqToHom (by rw [← hP]; rfl) ≫
      θ₀.hom.app b' ≫ eqToHom (by rw [← hP']; rfl)) (b : B) :
    (((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR hmate)).symm
      (TwoSquare.mk _ _ _ _ θ.hom)).app b).hom.f =
      eqToHom (by rw [← hP]; rfl) ≫
        ((mateEquiv adjB adj).symm (TwoSquare.mk _ _ _ _ θ₀.hom)).app b ≫
        eqToHom (by rw [← hP']; rfl) := by
  subst hP hP'
  have hθ' : Functor.whiskerRight θ.hom (forget F) = θ₀.hom := by
    ext b
    simpa using hθ b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [mateEquiv_symm_mapOfNatIsoAdjunction_app_hom_f, hθ']

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)}
  {j : X ⟶ Y} [IsOpenImmersion j] {h : j ≫ t = s}
  (hc : UpperStarWeilCompatible Λ j h)

omit [Finite k] in
/-- The ordinary inverse mate used by descent is the specified extension-by-zero
base-change comparison. -/
lemma openTraceInverseMate_eq :
    ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap j h))).symm
      (TwoSquare.mk _ _ _ _ (geometricFiberUpperStarComparison Λ j h).hom)) =
      (openImmersionLowerShriekUpperStarBaseChangeIso Λ
        (Scheme.Hom.isPullback_geometricFiberMap j h)).inv := by
  rw [purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv,
    geometricFiberUpperStarComparison, Iso.symm_hom, upperStarSquareComparison_flip_inv]
  exact Adjunction.inverseMate_natTrans_eq_exchangeLeft _ _ _

/-- Forgetting the sheaf-level descended open comparison gives the ordinary one. -/
lemma geometricFiberWeilExtensionByZeroBaseChange_app_forget
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((geometricFiberWeilExtensionByZeroBaseChange hc).app M).hom.f =
      (openImmersionLowerShriekUpperStarBaseChangeIso Λ
        (Scheme.Hom.isPullback_geometricFiberMap j h)).inv.app M := by
  have he := Endofunctor.IsoAlgebra.traceInverseMate_forget
    (openImmersionLowerShriekUpperStarAdjunction Λ j)
    (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap j h))
    (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ j h)
    (upperStarGeometricFiberMapCompFrobeniusIso Λ j h)
    (Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv _ _)
    (P₀ := (upperStar Λ s.geometricFiberProj))
    (P₀' := (upperStar Λ t.geometricFiberProj)) rfl rfl
    (upperStarCompGeometricFiberWeilLowerStarIso hc) (geometricFiberUpperStarComparison Λ j h)
    (fun N ↦ by simp [upperStarCompGeometricFiberWeilLowerStarIso]) M
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  rw [openTraceInverseMate_eq] at he
  dsimp only [geometricFiberWeilExtensionByZeroBaseChange]
  exact_mod_proofs he

/-- Forgetting the exactly derived descended open comparison gives ordinary
extension-by-zero base change, with the derived composition coordinates. -/
lemma geometricFiberWeilExtensionByZeroMapDerivedCategoryIso_forget
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap j h)).hom.app K =
      (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
        (Endofunctor.IsoAlgebra.forget _)).inv.app
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        ((geometricFiberWeilExtensionByZeroMapDerivedCategoryIso hc).inv.app K) ≫
      (Functor.mapDerivedCategoryCompForgetIso (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
        (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ j h))).hom.app
          ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj K) ≫
      (openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap j h)).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
          (Endofunctor.IsoAlgebra.forget _)).hom.app K) := by
  apply Functor.exactDescentComparison_forget
    (openImmersionLowerShriek Λ j) (geometricFiberWeilLowerStar Λ s)
    (geometricFiberWeilLowerStar Λ t) (Endofunctor.IsoAlgebra.forget _)
    (Endofunctor.IsoAlgebra.forget _)
    (openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap j h))
    (weilExtensionByZero Λ j h) (asIso (geometricFiberWeilExtensionByZeroBaseChange hc))
    (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
      (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ j h))
    (openImmersionLowerShriekUpperStarBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap j h))
  intro M
  have he := Functor.map_iso_inv_eq_of_map_hom_eq (Endofunctor.IsoAlgebra.forget _)
    ((asIso (geometricFiberWeilExtensionByZeroBaseChange hc)).app M)
    ((openImmersionLowerShriekUpperStarBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap j h)).symm.app M)
    (geometricFiberWeilExtensionByZeroBaseChange_app_forget Λ hc M)
  simp only [Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  dsimp +instances only [Iso.app_inv, Iso.symm_inv, Functor.comp_obj, Functor.comp_map] at he ⊢
  exact he.symm

end AlgebraicGeometry.ProEtale.CondensedRing
