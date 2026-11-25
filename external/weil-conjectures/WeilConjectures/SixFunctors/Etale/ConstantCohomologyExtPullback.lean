/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.MapExactFunctorHom
public import WeilConjectures.SixFunctors.Etale.ConstantCohomologyExt
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# Pullback of the cohomology classes of the constant sheaf, as `Ext`-classes

Let `g : Z ⟶ X` be a morphism of schemes and `Λ` a ring. The derived pullback `Lg^*` acts on the
cohomology classes `Λ_X ⟶ Λ_X[n]` of `D(X_ét, Λ)` through the canonical identification
`ε : Lg^* Λ_X ≅ Λ_Z` (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`),
`x ↦ ε⁻¹ ≫ Lg^* x ≫ ε[n]`; for an endomorphism `g` this is the Frobenius operator of the
canonical Weil datum (`AlgebraicGeometry.Etale.frobeniusOperator`).

Read as classes of `Extⁿ(Λ_X, Λ_X)` of étale sheaves of `Λ`-modules, this is the pushforward of
`Ext`-classes along the exact functor `g^*`, conjugated by the induced isomorphism
`g^* Λ_X ≅ Λ_Z` of constant sheaves (`AlgebraicGeometry.Etale.upperStarConstantRingIso`):
`AlgebraicGeometry.Etale.unitShiftAddEquivExt_leftDerivedUpperStar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}

/-- The cohomology classes `Λ_X ⟶ Λ_X[n]` of `D(X_ét, Λ)` are the classes of
`Extⁿ(Λ_X, Λ_X)`, computed with étale sheaves of `Λ`-modules. -/
noncomputable def unitShiftAddEquivExt (X : Scheme.{u}) (n : ℕ) :
    (𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) ≃+
      Ext (Sheaf.constantRing X.smallEtaleTopology Λ)
        (Sheaf.constantRing X.smallEtaleTopology Λ) n :=
  (AddEquiv.mk' ((unitIsoSingleFunctorConstantSheaf Λ X).homCongr
      ((shiftFunctor _ (n : ℤ)).mapIso (unitIsoSingleFunctorConstantSheaf Λ X))) fun f g ↦ by
      simp [Iso.homCongr_apply]).trans
    (Ext.homAddEquiv (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm

-- The unfoldings of `unitShiftAddEquivExt` and `unitShiftAddEquivH` are separate declarations,
-- stated pointwise: the kernel then compares their bodies (whose instance proofs are abstracted
-- into auxiliary lemmas) with the elaborated statement once, at a moderate memory cost.
private lemma unitShiftAddEquivExt_apply (n : ℕ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) :
    unitShiftAddEquivExt Λ X n x =
      ((AddEquiv.mk' ((unitIsoSingleFunctorConstantSheaf Λ X).homCongr
        ((shiftFunctor _ (n : ℤ)).mapIso (unitIsoSingleFunctorConstantSheaf Λ X))) fun f g ↦ by
          simp [Iso.homCongr_apply]).trans
        (Ext.homAddEquiv (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm) x :=
  rfl

lemma unitShiftAddEquivExt_hom (n : ℕ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) :
    (unitShiftAddEquivExt Λ X n x).hom = (unitIsoSingleFunctorConstantSheaf Λ X).inv ≫ x ≫
      (unitIsoSingleFunctorConstantSheaf Λ X).hom⟦(n : ℤ)⟧' := by
  rw [unitShiftAddEquivExt_apply, AddEquiv.trans_apply, ← Ext.homAddEquiv_apply,
    AddEquiv.apply_symm_apply]
  rfl

private lemma unitShiftAddEquivH_apply [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) :
    unitShiftAddEquivH Λ X n x =
      ((AddEquiv.mk' ((unitIsoSingleFunctorConstantSheaf Λ X).homCongr
        ((shiftFunctor _ (n : ℤ)).mapIso (unitIsoSingleFunctorConstantSheaf Λ X))) fun f g ↦ by
          simp [Iso.homCongr_apply]).trans
        ((Ext.homAddEquiv (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm.trans <|
          AddEquiv.ofBijective _ (bijective_mapExtComp_constantIntToRing Λ X _ n))) x :=
  rfl

/-- `unitShiftAddEquivH` is `unitShiftAddEquivExt` followed by the comparison of `Ext` over `Λ`
with abelian cohomology. -/
lemma unitShiftAddEquivH_eq [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) :
    unitShiftAddEquivH Λ X n x = (sheafForget₂ Λ X).mapExtComp
      (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) _ n
        (unitShiftAddEquivExt Λ X n x) := by
  rw [unitShiftAddEquivExt_apply, unitShiftAddEquivH_apply, AddEquiv.trans_apply,
    AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.ofBijective_apply]

variable (g : Z ⟶ X)

/-- The isomorphism `Lg^* Λ_X ≅ Λ_Z` of `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`,
on the constant sheaves placed in degree `0`. -/
noncomputable def leftDerivedUpperStarSingleConstantRingIso :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj
        (Sheaf.constantRing X.smallEtaleTopology Λ)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Sheaf.constantRing Z.smallEtaleTopology Λ) :=
  (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso (unitIsoSingleFunctorConstantSheaf Λ X).symm ≪≫
    leftDerivedUpperStarUnitIso _ g ≪≫ unitIsoSingleFunctorConstantSheaf Λ Z

/-- The isomorphism `g^* Λ_X ≅ Λ_Z` of constant étale sheaves of `Λ`-modules underlying the
canonical isomorphism `Lg^* Λ_X ≅ Λ_Z` (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`). -/
noncomputable def upperStarConstantRingIso :
    ((g)^*[ModuleCat.{u + 1} Λ]).obj (Sheaf.constantRing X.smallEtaleTopology Λ) ≅
      Sheaf.constantRing Z.smallEtaleTopology Λ :=
  (DerivedCategory.singleFunctor _ 0).preimageIso
    (((((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app
      (Sheaf.constantRing X.smallEtaleTopology Λ)).symm ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ g).symm.app _ ≪≫
        leftDerivedUpperStarSingleConstantRingIso Λ g)

lemma leftDerivedUpperStarSingleConstantRingIso_hom :
    (leftDerivedUpperStarSingleConstantRingIso Λ g).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory _ g).hom.app _ ≫
        (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map (upperStarConstantRingIso Λ g).hom := by
  -- Unfolding `upperStarConstantRingIso` at the level of isomorphisms is cheap for the kernel;
  -- rewriting with its equation lemma instead compares the morphisms of the derived category.
  have hU : upperStarConstantRingIso Λ g = (DerivedCategory.singleFunctor _ 0).preimageIso
      (X := ((g)^*[ModuleCat.{u + 1} Λ]).obj (Sheaf.constantRing X.smallEtaleTopology Λ))
      (Y := Sheaf.constantRing Z.smallEtaleTopology Λ)
      (((((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app
        (Sheaf.constantRing X.smallEtaleTopology Λ)).symm ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ g).symm.app _ ≪≫
          leftDerivedUpperStarSingleConstantRingIso Λ g) := rfl
  rw [hU, Functor.preimageIso_hom, Functor.map_preimage]
  simp

/-- **The derived pullback of cohomology classes is the pullback of `Ext`-classes.** For
`g : Z ⟶ X` and a class `x : Λ_X ⟶ Λ_X[n]`, the class `ε⁻¹ ≫ Lg^* x ≫ ε[n]` of `D(Z_ét, Λ)` is,
as a class of `Extⁿ(Λ_Z, Λ_Z)`, the pushforward of `x` along the exact functor `g^*`,
conjugated by `g^* Λ_X ≅ Λ_Z`. -/
theorem unitShiftAddEquivExt_leftDerivedUpperStar (n : ℕ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) :
    unitShiftAddEquivExt Λ Z n ((leftDerivedUpperStarUnitIso _ g).inv ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map x ≫
          ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (n : ℤ)).hom.app _ ≫
            (leftDerivedUpperStarUnitIso _ g).hom⟦(n : ℤ)⟧') =
      (Ext.mk₀ (upperStarConstantRingIso Λ g).inv).comp
        (((unitShiftAddEquivExt Λ X n x).mapExactFunctor ((g)^*[ModuleCat.{u + 1} Λ])).comp
          (Ext.mk₀ (upperStarConstantRingIso Λ g).hom) (add_zero n)) (zero_add n) := by
  refine Ext.ext ?_
  rw [Ext.mapExactFunctor_conj_hom _ (leftDerivedUpperStarIsoMapDerivedCategory _ g) _ _
    (leftDerivedUpperStarSingleConstantRingIso Λ g) (leftDerivedUpperStarSingleConstantRingIso Λ g)
    (leftDerivedUpperStarSingleConstantRingIso_hom Λ g)
    (leftDerivedUpperStarSingleConstantRingIso_hom Λ g), unitShiftAddEquivExt_hom,
    unitShiftAddEquivExt_hom]
  simp only [leftDerivedUpperStarSingleConstantRingIso, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  simp only [← Functor.map_comp_assoc]
  simp [← Functor.map_comp]

end AlgebraicGeometry.Etale
