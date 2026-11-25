/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EquivalenceCompCoherence

/-!
# The base change morphism for `Rν_*` and the composition of pullbacks

For a morphism of schemes `g`, the base change morphism `Lg^*_{ét} Rν_* ⟶ Rν_* Lg^*_{proét}`
(`ProEtale.rightDerivedComparisonBaseChange`) is the mate of the commutation
`D(ν^*) ⋙ Lg^*_{proét} ≅ Lg^*_{ét} ⋙ D(ν^*)` (`ProEtale.derivedComparisonUpperStarUpperStarIso`)
under the adjunctions `D(ν^*) ⊣ Rν_*`. This file shows:

* `ProEtale.comparisonUpperStarUpperStarIso_compCoherence`: the underived commutations
  `g^*_{ét} ⋙ ν^* ≅ ν^* ⋙ g^*_{proét}` are compatible with the composition isomorphisms of the
  pullbacks, being conjugate to the identities `g_* ⋙ ν_* = ν_* ⋙ g_*`, which are compatible with
  the composition isomorphisms of the pushforwards;
* `ProEtale.derivedComparisonUpperStarUpperStarIso_compCoherence`: hence so are the derived
  commutations;
* `ProEtale.rightDerivedComparisonBaseChange_comp`: hence the base change morphisms are
  compatible with the composition isomorphisms of the derived pullbacks
  (`CategoryTheory.mateEquiv_app_comp_of_compCoherence`).
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace CategoryTheory

variable {C₃ C₂ C₁ D₃ D₂ D₁ : Type*} [Category* C₃] [Category* C₂] [Category* C₁]
  [Category* D₃] [Category* D₂] [Category* D₁] {G₃ : C₃ ⥤ D₃} {G₂ : C₂ ⥤ D₂} {G₁ : C₁ ⥤ D₁}
  {mg : C₃ ⥤ C₂} {mf : C₂ ⥤ C₁} {mfg : C₃ ⥤ C₁} {sg : D₃ ⥤ D₂} {sf : D₂ ⥤ D₁} {sfg : D₃ ⥤ D₁}

/-- The compatibility of comparison isomorphisms with composition isomorphisms, stated with the
inverses of the comparison isomorphisms. -/
lemma CompCoherence.inv_app {Cm : mfg ≅ mg ⋙ mf} {Cs : sfg ≅ sg ⋙ sf}
    {ig : mg ⋙ G₂ ≅ G₃ ⋙ sg} {iF : mf ⋙ G₁ ≅ G₂ ⋙ sf} {ifg : mfg ⋙ G₁ ≅ G₃ ⋙ sfg}
    (H : CompCoherence Cm Cs ig iF ifg) (M : C₃) :
    ifg.inv.app M ≫ G₁.map (Cm.hom.app M) =
      Cs.hom.app (G₃.obj M) ≫ sf.map (ig.inv.app M) ≫ iF.inv.app (mg.obj M) := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (H M)]
  simp [← Functor.map_comp_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-! ### The underived commutations -/

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The two descriptions of the commutation of `ν_*` with the pushforwards agree: both are
identities. -/
lemma lowerStarCompComparisonLowerStarIso_eq {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    lowerStarCompComparisonLowerStarIso g A = lowerStarComparisonLowerStarIso A g := by
  ext G V
  simp only [lowerStarCompComparisonLowerStarIso, lowerStarComparisonLowerStarIso,
    toProEtCompOverPullbackIso]
  simp only [Functor.comp_obj, Iso.trans_hom, Functor.sheafPushforwardContinuousIso_hom,
    Iso.symm_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app, NatIso.ofComponents_inv_app, Iso.refl_inv,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom]
  erw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction `ν_*` carries the composition isomorphism of the pro-étale pushforwards to
that of the étale pushforwards. -/
lemma comparisonLowerStar_map_lowerStarComp_hom_app {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) (N : Sheaf (Scheme.ProEt.topology X) A) :
    (comparisonLowerStar A Z).map ((ProEtale.lowerStarComp A p q).hom.app N) =
      (Etale.lowerStarComp A p q).hom.app ((comparisonLowerStar A X).obj N) := by
  ext V
  erw [Etale.lowerStarComp_hom_app_hom_app]
  exact (lowerStarComp_hom_app_hom_app A p q N _).trans (by congr 2)

/-- The inverse of the commutation `ν^* ⋙ g^*_{proét} ≅ g^*_{ét} ⋙ ν^*` is the conjugate of the
identity `g_* ⋙ ν_* = ν_* ⋙ g_*` in the square of adjunctions `ν^* ⊣ ν_*`, `g^* ⊣ g_*`. -/
lemma comparisonUpperStarUpperStarIso_symm {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (comparisonUpperStarUpperStarIso A g).symm =
      Adjunction.pullIsoOfComapIso (comparisonAdjunction A Z) (comparisonAdjunction A Y)
        (Etale.upperStarLowerStarAdjunction A g) (ProEtale.upperStarLowerStarAdjunction A g)
        (lowerStarComparisonLowerStarIso A g) := by
  rw [comparisonUpperStarUpperStarIso, Adjunction.symm_conjugateIsoEquiv_symm_apply,
    Iso.symm_symm_eq]
  rfl

/-- **The commutations of `ν^*` with the pullbacks are compatible with composition**: the
isomorphisms `g^*_{ét} ⋙ ν^* ≅ ν^* ⋙ g^*_{proét}` are compatible with the composition
isomorphisms of the étale and the pro-étale pullbacks. -/
theorem comparisonUpperStarUpperStarIso_compCoherence {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) :
    CompCoherence (Etale.upperStarComp A p q) (ProEtale.upperStarComp A p q)
      (comparisonUpperStarUpperStarIso A q).symm (comparisonUpperStarUpperStarIso A p).symm
      (comparisonUpperStarUpperStarIso A (p ≫ q)).symm := by
  intro M
  rw [comparisonUpperStarUpperStarIso_symm, comparisonUpperStarUpperStarIso_symm,
    comparisonUpperStarUpperStarIso_symm]
  refine Adjunction.pullIsoOfComapIso_hom_app_comp (comparisonAdjunction A X)
    (comparisonAdjunction A Y) (comparisonAdjunction A Z)
    (Etale.upperStarLowerStarAdjunction A p) (Etale.upperStarLowerStarAdjunction A q)
    (Etale.upperStarLowerStarAdjunction A (p ≫ q)) (ProEtale.upperStarLowerStarAdjunction A p)
    (ProEtale.upperStarLowerStarAdjunction A q) (ProEtale.upperStarLowerStarAdjunction A (p ≫ q))
    _ _ _ _ _ (fun N ↦ ?_) M
  rw [conjugateIsoEquiv_upperStarComp A p q, Etale.conjugateIsoEquiv_upperStarComp A p q,
    comparisonLowerStar_map_lowerStarComp_hom_app]
  simp [lowerStarComparisonLowerStarIso]

/-! ### The derived commutations -/

section Derived

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **The derived commutations of `D(ν^*)` with the pullbacks are compatible with
composition**: the isomorphisms `Lg^*_{ét} ⋙ D(ν^*) ≅ D(ν^*) ⋙ Lg^*_{proét}` (inverses of
`derivedComparisonUpperStarUpperStarIso`) are compatible with the composition isomorphisms of the
derived étale and pro-étale pullbacks. -/
theorem derivedComparisonUpperStarUpperStarIso_compCoherence {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) :
    CompCoherence (Etale.leftDerivedUpperStarComp A p q) (ProEtale.leftDerivedUpperStarComp A p q)
      (derivedComparisonUpperStarUpperStarIso A q).symm
      (derivedComparisonUpperStarUpperStarIso A p).symm
      (derivedComparisonUpperStarUpperStarIso A (p ≫ q)).symm := by
  intro M
  -- As in `ProEtale.finiteCoefficientDerivedUpperStarIso_compCoherence`, the unifications below
  -- only need to unfold reducible constants.
  with_reducible
    refine compCoherence_of_isoConj
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory A q)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory A p)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory A (p ≫ q))
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A q)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A p)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A (p ≫ q))
      ((Functor.mapDerivedCategoryCompIso (Etale.upperStar A q) ν^*(Y)[A]).hom ≫
        (Functor.mapDerivedCategoryNatIso (comparisonUpperStarUpperStarIso A q).symm).hom ≫
        (Functor.mapDerivedCategoryCompIso ν^*(Z)[A] (ProEtale.upperStar A q)).inv)
      ((Functor.mapDerivedCategoryCompIso (Etale.upperStar A p) ν^*(X)[A]).hom ≫
        (Functor.mapDerivedCategoryNatIso (comparisonUpperStarUpperStarIso A p).symm).hom ≫
        (Functor.mapDerivedCategoryCompIso ν^*(Y)[A] (ProEtale.upperStar A p)).inv)
      ((Functor.mapDerivedCategoryCompIso (Etale.upperStar A (p ≫ q)) ν^*(X)[A]).hom ≫
        (Functor.mapDerivedCategoryNatIso (comparisonUpperStarUpperStarIso A (p ≫ q)).symm).hom ≫
        (Functor.mapDerivedCategoryCompIso ν^*(Z)[A] (ProEtale.upperStar A (p ≫ q))).inv)
      ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso (Etale.upperStar A q) (Etale.upperStar A p)).inv)
      ((Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp A p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso (ProEtale.upperStar A q)
          (ProEtale.upperStar A p)).inv)
      ?_ (derivedComparisonUpperStarUpperStarIso A q).symm
      (derivedComparisonUpperStarUpperStarIso A p).symm
      (derivedComparisonUpperStarUpperStarIso A (p ≫ q)).symm ?_ ?_ ?_
      (Etale.leftDerivedUpperStarComp A p q) (ProEtale.leftDerivedUpperStarComp A p q)
      ?_ ?_ M
  · with_reducible
      exact Functor.mapDerivedCategory_compCoherence' _ _ _ _ _
        (comparisonUpperStarUpperStarIso_compCoherence A p q)
  · intro M
    simp [derivedComparisonUpperStarUpperStarIso, Functor.mapDerivedCategoryNatIso_symm]
  · intro M
    simp [derivedComparisonUpperStarUpperStarIso, Functor.mapDerivedCategoryNatIso_symm]
  · intro M
    simp [derivedComparisonUpperStarUpperStarIso, Functor.mapDerivedCategoryNatIso_symm]
  · intro M
    delta Etale.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso Etale.leftDerivedUpperStarIsoMapDerivedCategory
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]
  · intro M
    delta ProEtale.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]

/-- **The base change morphisms for `Rν_*` are compatible with composition**: for `p : X ⟶ Y`
and `q : Y ⟶ Z`, the base change morphism of `p ≫ q` followed by the composition isomorphism
of the derived pro-étale pullbacks is the composite of the base change morphisms of `q` and `p`
after the composition isomorphism of the derived étale pullbacks. -/
theorem rightDerivedComparisonBaseChange_comp {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (rightDerivedComparisonBaseChange A (p ≫ q)).app K ≫
        R(ν_*(X)[A]).map ((ProEtale.leftDerivedUpperStarComp A p q).hom.app K) =
      (Etale.leftDerivedUpperStarComp A p q).hom.app (R(ν_*(Z)[A]).obj K) ≫
        L(Etale.upperStar A p).map ((rightDerivedComparisonBaseChange A q).app K) ≫
        (rightDerivedComparisonBaseChange A p).app (L(ProEtale.upperStar A q).obj K) :=
  mateEquiv_app_comp_of_compCoherence (derivedComparisonAdjunction A Z)
    (derivedComparisonAdjunction A Y) (derivedComparisonAdjunction A X)
    (Etale.leftDerivedUpperStarComp A p q) (ProEtale.leftDerivedUpperStarComp A p q)
    (derivedComparisonUpperStarUpperStarIso A q).inv
    (derivedComparisonUpperStarUpperStarIso A p).inv
    (derivedComparisonUpperStarUpperStarIso A (p ≫ q)).inv
    (derivedComparisonUpperStarUpperStarIso_compCoherence A p q) K

end Derived

end AlgebraicGeometry.ProEtale
