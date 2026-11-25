/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars

/-! # Unit normalization of scalar direct-image comparison

Source: Stacks Project, Tags 0D6E and 0D6J
(blueprint: lem-weil-compact-support-scalar-direct-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  constantSheaf presheafToSheaf Functor.leftAdjoint HasDerivedCategory.standard

-- The comparison passes through localization functors and K-injective resolutions.
/-- The specified scalar direct-image comparison satisfies the canonical unit equation.
Source: Stacks Project, Tags 0D6E and 0D6J.
(blueprint: lem-weil-compact-support-scalar-direct-normalization).
Proof: choose the all-complex unit-normalized comparison. On a K-injective complex,
resolve its scalar restriction by a K-injective complex. The unit equation and naturality
of the target unit give the same resolution equation as sfDerivedImageRestriction.
Cancel the direct-image quasi-isomorphism and the localization factors to identify the
comparisons on K-injective representatives. Their naturality gives equality on every
derived object. Substitute this equality into the all-complex normalization equation. -/
theorem compactSupportScalarDirectNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (φ : A →+* B) :
    CategoryTheory.ExactDerivedSquare.unitNormalized.{u + 1, u + 2}
      (proEtaleConstantModuleDirectImage g B) (proEtaleConstantModuleDirectImage g A)
      (proEtaleCoefficientRestrictScalars Z φ) (proEtaleCoefficientRestrictScalars Y φ)
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategoryFactors
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors
      (proEtaleCoefficientDirectImageComparison g φ).hom
      (sfDerivedImageRestriction g φ).inv := by
  let x := proEtaleCoefficientRestrictScalars Z φ
  let y := proEtaleCoefficientRestrictScalars Y φ
  let F := proEtaleConstantModuleDirectImage g B
  let H := proEtaleConstantModuleDirectImage g A
  let c := proEtaleCoefficientDirectImageComparison g φ
  obtain ⟨d, hd⟩ := coefficientDerivedComparison_exists g φ
  change CategoryTheory.ExactDerivedSquare.unitNormalized F H x y
    x.mapDerivedCategory y.mapDerivedCategory
    x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom d.hom at hd
  have he : sfDerivedImageRestriction g φ = d.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    change (sfDerivedImageRestriction g φ).hom.app N = d.inv.app N
    obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
    let := hJ
    have hj : (sfDerivedImageRestriction g φ).hom.app (DerivedCategory.Q.obj J) =
        d.inv.app (DerivedCategory.Q.obj J) := by
      obtain ⟨I, _, j, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
        ((x.mapHomologicalComplex (.up ℤ)).obj J)
      have hs := (proEtaleDerivedDirectImage_restrictScalars g φ).choose_spec J I j
      have hunit := hd J
      rw [Functor.rightDerivedFunctorUnitQ_eq] at hunit
      have hn := H.rightDerivedFunctorUnitQ_naturality j
      rw [Functor.rightDerivedFunctorUnitQ_eq] at hn
      have hcalc : d.inv.app (DerivedCategory.Q.obj J) ≫
          y.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
          y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app J) ≫
          DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map j) =
        H.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app J) ≫
          H.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫
          (H.rightDerivedFunctorObjQIso I).hom := by
        apply (cancel_mono (H.rightDerivedFunctorObjQIso I).inv).mp
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        erw [hn]
        have hh := congrArg (fun t ↦
          d.inv.app (DerivedCategory.Q.obj J) ≫
            y.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫ t ≫
            H.rightDerivedFunctor.map (DerivedCategory.Q.map j)) hunit
        simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id] at hh
        erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at hh
        convert hh.symm using 1
        rfl
      have hq : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map j) := hs.1
      let := hq
      have hmap : IsIso (DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map j)) :=
        inferInstance
      let ej := @asIso _ _ _ _ _ hmap
      let tail := y.mapDerivedCategory.mapIso (F.rightDerivedFunctorObjQIso J) ≪≫
        y.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≪≫
        DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex c (.up ℤ)).app J) ≪≫
        ej
      apply (cancel_mono tail.hom).mp
      have hh := hs.2.trans hcalc.symm
      dsimp only [tail, ej, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom]
      convert hh using 1
      rfl
    apply (cancel_mono ((F.rightDerivedFunctor ⋙ y.mapDerivedCategory).map e.hom)).mp
    rw [← (sfDerivedImageRestriction g φ).hom.naturality, ← d.inv.naturality, hj]
  rw [he]
  exact hd

end WeilConjectures
