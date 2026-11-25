/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.UnboundedSectionsLocalization.UnboundedSectionsLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# Coherence of the unbounded module direct-image compositor

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-cocycle.proof.md, "Refinement isomorphisms"; Stacks Project,
Tag 0D6E (blueprint: lem-sfb-module-derived-compositor-coherence).

The comparisons below specialize the existing total-right-derived universal construction
to the actual module-object pushforwards. Their K-injective normalization identifies them
with the ringed-topos comparisons transported through the internal/sectionwise module
equivalence: both are uniquely characterized by compatibility with the resolution units.
The derived categories are ordinary unbounded categories, with the published universe
convention: Scheme.{u}, abelian coefficients in u + 1, and the induced derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private lemma derivedComp_post
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H H' : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H) (d : H ≅ H') :
    Functor.rightDerivedFunctorCompIso' F G (e ≪≫ d) =
      Functor.rightDerivedFunctorCompIso' F G e ≪≫ Functor.rightDerivedFunctorNatIso d := by
  apply Iso.ext
  simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans_comp]

private lemma derivedId_eq
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] :
    (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso C =
      Functor.rightDerivedFunctorIdIso C := by
  apply Iso.ext
  apply (𝟭 C).rightDerivedFunctor.rightDerived_ext (𝟭 C).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K : 2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, ← Category.assoc,
    Functor.rightDerivedFunctorIdIso_fac_app]
  have hf := congr_app (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  erw [hf]
  have h := congrArg (fun e ↦ e.hom.app K) (Functor.mapDerivedCategoryIdIso_factorsh C)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at h
  erw [Category.comp_id, Category.comp_id, DerivedCategory.Qh.map_id,
    Category.comp_id] at h
  erw [h, Iso.inv_hom_id_app]

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical comparison `R(gf)_* ≅ Rf_* ⋙ Rg_*`, in inverse-compositor direction.
The existing exact inverse-image adjunction supplies K-injective preservation; the
comparison is the universal derived comparison of the existing ordinary compositor.
Source: Stacks 0D6E and blueprint proposition-construction-independence-rf-shriek, Refinement
isomorphisms (blueprint: lem-sfb-module-derived-compositor-coherence). -/
noncomputable def moduleDerivedCompositor {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStar Λ (f ≫ g)).rightDerivedFunctor ≅
      (lowerStar Λ f).rightDerivedFunctor ⋙ (lowerStar Λ g).rightDerivedFunctor :=
  letI := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  (Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ g)
    (lowerStarComp Λ f g)).symm

/-- Associativity of the normalized module-object derived compositor, including
functor associators and transport along associativity of scheme-map composition.
Source: Stacks 0D6E and blueprint proposition-construction-independence-rf-shriek, Refinement
isomorphisms (blueprint: lem-sfb-module-derived-compositor-coherence).

Proof plan: (1)-(3) identify the ordinary and derived sectionwise pushforwards and
normalize on K-injectives as in module_derived_compositor_normalization. (4) Apply
lem-pur-ringed-derived-composition-cocycle to the four ringed topoi. Conjugate the
two composites by the resolution-compatible equivalences supplied by
lem-pd-section-derived-pushpull-normalization. The intermediate comparison isomorphisms
cancel; naturality moves the remaining comparisons past each compositor. The sectionwise
cocycle identifies the results. Faithfulness of the derived equivalence then identifies
the original transformations. The displayed associator and lowerStarCongr account for
both functor parentheses and equality of the two composite scheme maps. -/
theorem module_derived_compositor_coherence (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    moduleDerivedCompositor Λ (f ≫ g) h ≪≫
        Functor.isoWhiskerRight (moduleDerivedCompositor Λ f g)
          (lowerStar Λ h).rightDerivedFunctor ≪≫
        Functor.associator (lowerStar Λ f).rightDerivedFunctor
          (lowerStar Λ g).rightDerivedFunctor (lowerStar Λ h).rightDerivedFunctor =
      Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h)) ≪≫
        moduleDerivedCompositor Λ f (g ≫ h) ≪≫
        Functor.isoWhiskerLeft (lowerStar Λ f).rightDerivedFunctor
          (moduleDerivedCompositor Λ g h) := by
  have _ := hΛ
  let := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction Λ g).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction Λ (f ≫ g)).preservesKInjectiveComplexes
  have ho := congrArg (fun e ↦ e.hom) (lowerStarComp_assoc Λ f g h)
  have hc := Functor.rightDerivedFunctorCompIso'_assoc
    (lowerStar Λ f) (lowerStar Λ g) (lowerStar Λ h)
    (lowerStar Λ (f ≫ g)) (lowerStar Λ (g ≫ h)) (lowerStar Λ (f ≫ g ≫ h))
    (lowerStarComp Λ f g) (lowerStarComp Λ g h)
    (lowerStarComp Λ (f ≫ g) h ≪≫ lowerStarCongr Λ (Category.assoc f g h))
    (lowerStarComp Λ f (g ≫ h)) (by
      apply NatTrans.ext
      funext M
      have hm := congr_app ho M
      simpa using hm.symm)
  rw [derivedComp_post] at hc
  have hci :
      Functor.isoWhiskerRight
          (Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ g)
            (lowerStarComp Λ f g)) (lowerStar Λ h).rightDerivedFunctor ≪≫
        Functor.rightDerivedFunctorCompIso' (lowerStar Λ (f ≫ g)) (lowerStar Λ h)
          (lowerStarComp Λ (f ≫ g) h) ≪≫
        Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h)) =
      Functor.isoWhiskerLeft (lowerStar Λ f).rightDerivedFunctor
          (Functor.rightDerivedFunctorCompIso' (lowerStar Λ g) (lowerStar Λ h)
            (lowerStarComp Λ g h)) ≪≫
        Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ (g ≫ h))
          (lowerStarComp Λ f (g ≫ h)) := Iso.ext hc
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi
    ((Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h))).inv.app
      M)).1
  have hi := congrArg (fun e ↦ e.inv.app M) hci
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.assoc] at hi
  simp only [moduleDerivedCompositor, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.comp_id]
  simpa only [Iso.inv_hom_id_app_assoc, Category.assoc] using hi

end AlgebraicGeometry.ProEtale.CondensedRing
