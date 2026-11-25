/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldUpperStarCompCoherence

/-!
# Coherence of the derived residue field transport with composition

The isomorphisms `ProEtale.residueFieldDerivedUpperStarIso : Lh^* ⋙ D(G) ≅ D(G) ⋙ Lh^*` are
compatible with the composition isomorphisms of derived pullbacks
(`ProEtale.residueFieldDerivedUpperStarIsoCompCoherenceAt`). This follows from the underived
compatibility `ProEtale.residueFieldModuleSheafUpperStarIso_compCoherence`, by applying
`D(-)` (`CategoryTheory.Functor.mapDerivedCategory_compCoherence`) and transporting along the
isomorphisms `L(h^*) ≅ D(h^*)` (`CategoryTheory.compCoherence_of_isoConj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **The derived residue field transport is compatible with composition**: the isomorphisms
`residueFieldDerivedUpperStarIso` are compatible with the composition isomorphisms
`L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` of derived pullbacks. -/
theorem residueFieldDerivedUpperStarIsoCompCoherenceAt {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) : ResidueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E p q := by
  -- The unifications below only need to unfold reducible constants. At default transparency
  -- the elaborator unfolds the composition of the derived categories (a localization) when
  -- comparing the (pretty-printing identical) sides, which takes minutes.
  intro M
  with_reducible
    refine compCoherence_of_isoConj
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) q)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) p)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) (p ≫ q))
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) q)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) (p ≫ q))
      ((Functor.mapDerivedCategoryCompIso
          ((q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧)
          (residueFieldModuleSheaf Y ℓ E)).hom ≫
        (Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E q)).hom ≫
        (Functor.mapDerivedCategoryCompIso (residueFieldModuleSheaf Z ℓ E)
          ((q)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).inv)
      ((Functor.mapDerivedCategoryCompIso
          ((p)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧)
          (residueFieldModuleSheaf X ℓ E)).hom ≫
        (Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E p)).hom ≫
        (Functor.mapDerivedCategoryCompIso (residueFieldModuleSheaf Y ℓ E)
          ((p)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).inv)
      ((Functor.mapDerivedCategoryCompIso
          ((p ≫ q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧)
          (residueFieldModuleSheaf X ℓ E)).hom ≫
        (Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E (p ≫ q))).hom ≫
        (Functor.mapDerivedCategoryCompIso (residueFieldModuleSheaf Z ℓ E)
          ((p ≫ q)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).inv)
      ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          ((q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧)
          ((p)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧)).inv)
      ((Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          ((q)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])
          ((p)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).inv)
      ?_ (residueFieldDerivedUpperStarIso ℓ E q) (residueFieldDerivedUpperStarIso ℓ E p)
      (residueFieldDerivedUpperStarIso ℓ E (p ≫ q)) ?_ ?_ ?_
      (CondensedRing.leftDerivedUpperStarComp
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) p q)
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p q)
      ?_ ?_ M
  · with_reducible
      exact Functor.mapDerivedCategory_compCoherence' _ _ _ _ _
        (residueFieldModuleSheafUpperStarIso_compCoherence ℓ E p q)
  · intro M
    delta residueFieldDerivedUpperStarIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  · intro M
    delta residueFieldDerivedUpperStarIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  · intro M
    delta residueFieldDerivedUpperStarIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  · intro M
    delta CondensedRing.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]
  · intro M
    delta ProEtale.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale
