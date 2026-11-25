/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-!
# The comparison isomorphisms of the compact support formalism on `D⁺(X_ét)`

The compact support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism` compares the
compactly supported direct images attached to two compactifications through its own comparison
along a refinement, `CompactSupportFormalism.refinementComparison`, built from the base change map
of the formalism (a mate of the composition isomorphisms of the pullbacks). This file shows that
it is the comparison
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`, built from
the base change isomorphism of the extension by zero on étale sheaves. Hence the
comparison isomorphism `CompactSupportFormalism.shriekIso` of the formalism is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`, and the coherences of
blueprint `proposition-construction-independence-rf-shriek` proved for one hold for the other.

The two base change maps are compared through their transposes under the derived adjunction
`D(c.i)_! ⊣ D(c.i)^*`: both are the unit of `D(d.i)_! ⊣ D(d.i)^*` followed by the composition
isomorphism `D(d.i)^* ≅ D(r.hom)^* ⋙ D(c.i)^*`
(`AlgebraicGeometry.Etale.unit_map_refinementLowerShriekBaseChangeDerivedPlusIso_hom_app`), which
is checked on complexes, where the derived unit is the levelwise unit
(`CategoryTheory.Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac`).

## Main results

- `AlgebraicGeometry.Etale.derivedPlusFormalism_refinementComparison`: the comparison along a
  refinement of the formalism is
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`.
- `AlgebraicGeometry.Etale.derivedPlusFormalism_shriekIso`: the comparison isomorphism of the
  formalism is `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

section Derived

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The transpose of the derived base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`
under `D(c.i)_! ⊣ D(c.i)^*` is the unit of `D(d.i)_! ⊣ D(d.i)^*` followed by the composition
isomorphism `D(d.i)^* ≅ D(r.hom)^* ⋙ D(c.i)^*`. -/
lemma unit_map_refinementLowerShriekBaseChangeDerivedPlusIso_hom_app
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (openImmersionLowerShriekUpperStarAdjunction A c.i).mapDerivedCategoryPlusAdjunction.unit.app
          K ≫
        D+((c.i)^*[A]).map ((refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).hom.app K) =
      (openImmersionLowerShriekUpperStarAdjunction A d.i).mapDerivedCategoryPlusAdjunction.unit.app
          K ≫
        (upperStarCompDerivedPlus A c.i r.hom d.i r.i_hom.symm).hom.app
          (D+((d.i)_!open[A]).obj K) := by
  let τ₁ : 𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) ⟶
      D+((d.i)_!open[A]) ⋙ D+((r.hom)^*[A]) ⋙ D+((c.i)^*[A]) :=
    (openImmersionLowerShriekUpperStarAdjunction A c.i).mapDerivedCategoryPlusAdjunction.unit ≫
      Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).hom
        D+((c.i)^*[A])
  let τ₂ : 𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) ⟶
      D+((d.i)_!open[A]) ⋙ D+((r.hom)^*[A]) ⋙ D+((c.i)^*[A]) :=
    (openImmersionLowerShriekUpperStarAdjunction A d.i).mapDerivedCategoryPlusAdjunction.unit ≫
      Functor.whiskerLeft D+((d.i)_!open[A])
        (upperStarCompDerivedPlus A c.i r.hom d.i r.i_hom.symm).hom
  suffices τ₁ = τ₂ from NatTrans.congr_app this K
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology A)) (fun K₀ ↦ ?_)
  have := r.isIso_openImmersionLowerShriekBaseChange A hcart
  have hunit := unit_map_openImmersionLowerShriekBaseChange_app A c.i r.hom d.i r.i_hom
  rw [upperStarCompIso_eq] at hunit
  have hhot := Adjunction.mapHomotopyCategoryPlus_unit_app_comp_whisker
    (openImmersionLowerShriekUpperStarAdjunction A c.i)
    (openImmersionLowerShriekUpperStarAdjunction A d.i) (r.openImmersionLowerShriekBaseChange A)
    (upperStarComp A c.i r.hom d.i r.i_hom.symm).hom
    hunit K₀
  rw [← cancel_mono (D+((c.i)^*[A]).map (D+((r.hom)^*[A]).map
      (((d.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K₀)) ≫
    D+((c.i)^*[A]).map (((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
      (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K₀)) ≫
    ((c.i)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
      (((r.hom)^*[A]).mapHomotopyCategoryPlus.obj
        (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K₀)))]
  simp only [τ₁, τ₂, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  have Uc := Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac
    (openImmersionLowerShriekUpperStarAdjunction A c.i) K₀
  have Ud := Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac
    (openImmersionLowerShriekUpperStarAdjunction A d.i) K₀
  have hbc := refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh A r hcart K₀
  have hup := upperStarCompDerivedPlus_hom_app_factorsh A c.i r.hom d.i r.i_hom.symm
    (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K₀)
  have hnatUp := (upperStarCompDerivedPlus A c.i r.hom d.i r.i_hom.symm).hom.naturality
    ((((d.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K₀))
  have hnatC : D+((c.i)^*[A]).map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (r.openImmersionLowerShriekBaseChange A)).app K₀)) ≫
      ((c.i)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((r.hom)^*[A]).mapHomotopyCategoryPlus.obj
          (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K₀)) =
      ((c.i)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K₀) ≫
        DerivedCategory.Plus.Qh.map (((c.i)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (r.openImmersionLowerShriekBaseChange A)).app K₀)) :=
    ((c.i)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus (r.openImmersionLowerShriekBaseChange A)).app K₀)
  simp only [Functor.comp_map, Functor.comp_obj] at hnatUp
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hbc,
    Functor.map_comp_assoc]
  rw [hnatC, reassoc_of% Uc, ← reassoc_of% hnatUp, hup, reassoc_of% Ud,
    ← Functor.map_comp, ← Functor.map_comp, hhot]

/-- The composition isomorphism `ExchangeFormalism.pbComp'` of the pullbacks in
`derivedPlusFormalism A` is `AlgebraicGeometry.Etale.upperStarCompDerivedPlus`. -/
lemma derivedPlusFormalism_pbComp' {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (w : h₁ ≫ h₂ = h₁₂) :
    (derivedPlusFormalism A).pbComp' h₁ h₂ h₁₂ w =
      upperStarCompDerivedPlus A h₁ h₂ h₁₂ w.symm := by
  subst w
  rw [ExchangeFormalism.pbComp'_rfl]
  rfl

/-- The base change map of the compact support formalism `derivedPlusFormalism A` for the square
of a refinement `r : c.Refinement d` is the base change isomorphism
`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso`, preceded by the identity
isomorphism `D(𝟙 X)^* ≅ 𝟭`. -/
lemma derivedPlusFormalism_baseChange_refinement (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    ((derivedPlusFormalism A).baseChange (𝟙 X) c.i d.i r.hom hcart.flip.w) =
      Functor.whiskerRight ((derivedPlusFormalism A).pbId X).hom
          ((derivedPlusFormalism A).sh c.i) ≫
        (Functor.leftUnitor _).hom ≫
          (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).hom := by
  have key := mateEquiv_eq_of_unit ((derivedPlusFormalism A).shAdj d.i)
    ((derivedPlusFormalism A).shAdj c.i)
    (TwoSquare.mk ((derivedPlusFormalism A).pb (𝟙 X)) _ _ ((derivedPlusFormalism A).pb r.hom)
      (Functor.whiskerRight ((derivedPlusFormalism A).pbId X).hom
      ((derivedPlusFormalism A).sh c.i) ≫ (Functor.leftUnitor _).hom ≫
        (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).hom))
    ((derivedPlusFormalism A).sqIso (𝟙 X) c.i d.i r.hom hcart.flip.w).hom (fun K ↦ ?_)
  · rw [ExchangeFormalism.baseChange, ← key]
    exact (Equiv.symm_apply_apply _ _)
  rw [ExchangeFormalism.sqIso_eq _ _ _ _ _ _ d.i (Category.id_comp _) r.i_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.map_comp]
  rw [ExchangeFormalism.pbComp'_id_left_inv_app, derivedPlusFormalism_pbComp']
  have h₁ := ((derivedPlusFormalism A).pbId X).hom.naturality
    (((derivedPlusFormalism A).shAdj d.i).unit.app K)
  have h₂ := ((derivedPlusFormalism A).shAdj c.i).unit_naturality
    ((upperStarIdDerivedPlus A X).hom.app K)
  have h₃ := unit_map_refinementLowerShriekBaseChangeDerivedPlusIso_hom_app A r hcart K
  erw [reassoc_of% h₁, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₂]
  exact congrArg (fun t ↦ _ ≫ t) h₃.symm

/-- The composition isomorphism of the pushforwards in the compact support formalism
`derivedPlusFormalism A`, the conjugate of `AlgebraicGeometry.Etale.upperStarCompDerivedPlus`, is
the composition isomorphism `Functor.rightDerivedFunctorPlusCompIso'` of the right derived
functors. -/
lemma derivedPlusFormalism_pfComp'_inv {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (w : h₁ ≫ h₂ = h₁₂) :
    haveI : ((h₁)_*[A]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (upperStarLowerStarAdjunction A h₁)
    ((derivedPlusFormalism A).pfComp' h₁ h₂ h₁₂ w).inv =
      (Functor.rightDerivedFunctorPlusCompIso' (h₁)_*[A] (h₂)_*[A]
        (lowerStarComp A h₁ h₂ h₁₂ w.symm)).hom := by
  subst w
  refine conjugateEquiv_eq_of_unit _ _ _ _ (fun Z ↦ ?_)
  rw [Adjunction.comp_unit_app, Iso.symm_inv, ExchangeFormalism.pbComp'_rfl,
    Category.assoc]
  exact (derivedPlus_unit_comp_upperStarCompDerivedPlus A h₁ h₂ (h₁ ≫ h₂) rfl Z).symm

end Derived

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {c d : Compactification f}

omit [Finite Λ] in
/-- The comparison along a refinement of the compact support formalism
`AlgebraicGeometry.Etale.derivedPlusFormalism` is the comparison
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`. -/
theorem derivedPlusFormalism_refinementComparison (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).refinementComparison r hr =
      rightDerivedLowerShriekOfCompactificationPlusComparison _ r hr := by
  rw [CompactSupportFormalism.refinementComparison_eq_of_baseChange
    (derivedPlusFormalism (ModuleCat.{u + 1} Λ)) r hr
    (refinementLowerShriekBaseChangeDerivedPlusIso (ModuleCat.{u + 1} Λ) r hr)
    (derivedPlusFormalism_baseChange_refinement (ModuleCat.{u + 1} Λ) r hr),
    derivedPlusFormalism_pfComp'_inv, ← refinementLowerStarComp_eq]
  rfl

/-- The comparison isomorphism of the compact support formalism
`AlgebraicGeometry.Etale.derivedPlusFormalism` between the compactly supported direct images
attached to two compactifications is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`. -/
theorem derivedPlusFormalism_shriekIso [QuasiCompact f] (c d : Compactification f) :
    (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso c d =
      rightDerivedLowerShriekOfCompactificationPlusIso Λ c d := by
  ext : 1
  simp only [CompactSupportFormalism.shriekIso, rightDerivedLowerShriekOfCompactificationPlusIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, derivedPlusFormalism_refinementComparison]

end Torsion

end Etale

end AlgebraicGeometry
