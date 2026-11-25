/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExactCounit
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsRestrictScalarsMate
public import WeilConjectures.SixFunctors.Etale.Derived.TensorSheaf
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.ProjectionIso

/-!
# Derived extension of scalars of étale sheaves as a tensor product

Let `S` be an `R`-algebra and write `Ψ = L(S ⊗_R -)` for derived extension of scalars of étale
sheaves, with right adjoint the restriction of scalars `Res`. Restricted back to `R`, derived
extension of scalars is the derived tensor product with the sheaf `S_X` of `R`-modules underlying
the unit sheaf of `S`-modules: the projection map `K ⊗ S_X ⟶ res (S ⊗_R K)` of
`AlgebraicGeometry.Etale.sheafExtendScalarsProjection` induces an isomorphism
`L(- ⊗ S_X) ≅ Ψ ⋙ Res` of left derived functors.

We also compute the transpose `Ψ (K ⊗ᴸ S_X) ⟶ Ψ K` of this isomorphism along `Ψ ⊣ Res` on the
image of a complex: it is induced by the transpose `S ⊗_R (K ⊗ S_X) ⟶ S ⊗_R K` of the
projection map along extension and restriction of scalars of sheaves.

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Projection`.

## Main definitions and results

- `AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection`: the isomorphism
  `L(- ⊗ S_X) ⟶ Ψ ⋙ Res`.
- `AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection_transpose`: its transpose
  on the image of a complex.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace CategoryTheory

section MapHomotopyCategoryTranspose

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  {T : C ⥤ C} [T.Additive] (π : T ⟶ f ⋙ g)

/-- On homotopy categories, the transpose along `f ⊣ g` of the image of `π : T ⟶ f ⋙ g` is the
image of the transpose `f ∘ π ≫ ε` of `π`. -/
private lemma Adjunction.mapHomotopyCategory_map_comp_counit_app_of_eq (π' : T ⋙ f ⟶ f)
    (hπ' : π' = Functor.whiskerRight π f ≫ Functor.whiskerLeft f adj.counit)
    (K : HomotopyCategory C (.up ℤ)) :
    (f.mapHomotopyCategory (.up ℤ)).map ((NatTrans.mapHomotopyCategory π (.up ℤ)).app K) ≫
      (adj.mapHomotopyCategory (.up ℤ)).counit.app ((f.mapHomotopyCategory (.up ℤ)).obj K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ f)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory π' (.up ℤ)).app K := by
  subst hπ'
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  erw [Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp]
  congr 1

end MapHomotopyCategoryTranspose

section ProjectionTranspose

variable {𝒟₁ 𝒟₂ ℋ₁ ℋ₂ : Type*} [Category 𝒟₁] [Category 𝒟₂] [Category ℋ₁] [Category ℋ₂]
  {Q₁ : ℋ₁ ⥤ 𝒟₁} {Q₂ : ℋ₂ ⥤ 𝒟₂} {LE : 𝒟₁ ⥤ 𝒟₂} {LRes : 𝒟₂ ⥤ 𝒟₁} {LT : 𝒟₁ ⥤ 𝒟₁}
  {TH : ℋ₁ ⥤ ℋ₁} {EH : ℋ₁ ⥤ ℋ₂} {ResH : ℋ₂ ⥤ ℋ₁} {TEH : ℋ₁ ⥤ ℋ₂}

/-- The diagram chase behind `leftDerivedSheafExtendScalarsProjection_transpose`, for arbitrary
categories and functors: `Qᵢ` are localization functors, `κE` and `κT` counits of derived
functors, `fac` identifies the derived functor of `Res` on the image of `Q₂`, `θ` is a
derived projection map with defining property `hθ`, and `adj` is the derived adjunction, with
counit computed by `hadj` from the adjunction `adjH` on homotopy categories. -/
private lemma leftDerived_projection_transpose_aux (κE : Q₁ ⋙ LE ⟶ EH ⋙ Q₂) (κT : Q₁ ⋙ LT ⟶ TH ⋙ Q₁)
    (fac : Q₂ ⋙ LRes ≅ ResH ⋙ Q₁) (θ : LT ⟶ LE ⋙ LRes) (adj : LE ⊣ LRes) (adjH : EH ⊣ ResH)
    (e : TH ⋙ EH ≅ TEH) (p : TEH ⟶ EH)
    (hadj : ∀ K, adj.counit.app (Q₂.obj K) =
      LE.map (fac.hom.app K) ≫ κE.app (ResH.obj K) ≫ Q₂.map (adjH.counit.app K))
    (K : ℋ₁) (πK : TH.obj K ⟶ ResH.obj (EH.obj K))
    (εK : LRes.obj (LE.obj (Q₁.obj K)) ⟶ Q₁.obj (ResH.obj (EH.obj K)))
    (hε : εK = LRes.map (κE.app K) ≫ fac.hom.app (EH.obj K))
    (hθ : θ.app (Q₁.obj K) ≫ εK = κT.app K ≫ Q₁.map πK)
    (hkey : EH.map πK ≫ adjH.counit.app (EH.obj K) = e.hom.app K ≫ p.app K) :
    LE.map (θ.app (Q₁.obj K)) ≫ adj.counit.app (LE.obj (Q₁.obj K)) ≫ κE.app K =
      LE.map (κT.app K) ≫ κE.app (TH.obj K) ≫ Q₂.map (e.hom.app K ≫ p.app K) := by
  subst hε
  have hθ' := congrArg LE.map hθ
  simp only [Functor.map_comp] at hθ'
  have hnat := adj.counit.naturality (κE.app K)
  have hκ := κE.naturality πK
  dsimp at hnat hκ
  rw [← hnat, hadj, reassoc_of% hθ', reassoc_of% hκ, ← Functor.map_comp, hkey]

end ProjectionTranspose

end CategoryTheory

-- The braiding of `ModuleCat` found by instance search (`instBraidedCategory`) is not syntactically
-- the one underlying the derived tensor product of étale sheaves; with these instances, instance
-- search produces exactly the monoidal structure used by `AlgebraicGeometry.Etale.derivedTensor`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- Extension of scalars `S ⊗_R -` of étale sheaves on `X`. -/
local notation "𝓔" => sheafExtendScalars (algebraMap R S) X

set_option hygiene false in
/-- Restriction of scalars of étale sheaves on `X`. -/
local notation "𝓡" =>
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))

/-- The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules. -/
local notation "𝓢" => sheafRestrictScalarsUnit R S X

/-- Extension followed by restriction of scalars sends quasi-isomorphisms between K-flat
complexes to quasi-isomorphisms. -/
instance preservesKFlatQuasiIso_sheafExtendScalars_comp_restrictScalars :
    (𝓔 ⋙ 𝓡).PreservesKFlatQuasiIso :=
  Functor.preservesKFlatQuasiIso_comp_of_exact 𝓔 𝓡

/-- The counit exhibiting `Ψ ⋙ Res` as a total left derived functor of `S ⊗_R - ⋙ res`: the
counit of `Ψ` followed by the identification of `Res` with the levelwise restriction of scalars. -/
noncomputable def leftDerivedSheafExtendScalarsRestrictScalarsCounit :
    DerivedCategory.Qh ⋙ L(𝓔) ⋙ D(𝓡) ⟶ (𝓔 ⋙ 𝓡).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.leftDerivedFunctorCompExactCounit 𝓔 𝓡

lemma leftDerivedSheafExtendScalarsRestrictScalarsCounit_app
    (K : HomotopyCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X).app K =
      D(𝓡).map ((𝓔).leftDerivedFunctorCounit.app K) ≫
        (𝓡).mapDerivedCategoryFactorsh.hom.app (((𝓔).mapHomotopyCategory (.up ℤ)).obj K) := by
  rw [show leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X =
    Functor.leftDerivedFunctorCompExactCounit 𝓔 𝓡 from rfl]
  exact Functor.leftDerivedFunctorCompExactCounit_app _ _ K

instance isLeftDerivedFunctor_leftDerivedSheafExtendScalarsRestrictScalars :
    (L(𝓔) ⋙ D(𝓡)).IsLeftDerivedFunctor
      (leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X)
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_leftDerivedFunctorCompExactCounit 𝓔 𝓡

/-- **Derived extension of scalars is a tensor product**: the natural transformation
`L(- ⊗ S_X) ⟶ Ψ ⋙ Res` induced by the projection map `K ⊗ S_X ⟶ res (S ⊗_R K)` of sheaves
(`AlgebraicGeometry.Etale.sheafExtendScalarsProjection`). -/
noncomputable def leftDerivedSheafExtendScalarsProjection : L(tensorRight 𝓢) ⟶ L(𝓔) ⋙ D(𝓡) :=
  Functor.leftDerivedNatTrans _ _ (tensorRight 𝓢).leftDerivedFunctorCounit
    (leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X)
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjection R S X) (.up ℤ))
      DerivedCategory.Qh)

/-- The defining property of `leftDerivedSheafExtendScalarsProjection` on the image of an
object of the homotopy category. -/
@[reassoc]
lemma leftDerivedSheafExtendScalarsProjection_app_comp_counit
    (K : HomotopyCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedSheafExtendScalarsProjection R S X).app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X).app K =
      (tensorRight 𝓢).leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (sheafExtendScalarsProjection R S X) (.up ℤ)).app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ _ _ K

instance isIso_leftDerivedSheafExtendScalarsProjection :
    IsIso (leftDerivedSheafExtendScalarsProjection R S X) := by
  let e : (tensorRight 𝓢).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      (𝓔 ⋙ 𝓡).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    { hom := Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjection R S X) (.up ℤ))
        DerivedCategory.Qh
      inv := Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (inv (sheafExtendScalarsProjection R S X)) (.up ℤ))
        DerivedCategory.Qh
      hom_inv_id := by
        rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]
        simp
      inv_hom_id := by
        rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]
        simp }
  exact (Functor.leftDerivedNatIso _ _ (tensorRight 𝓢).leftDerivedFunctorCounit
    (leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X)
    (HomotopyCategory.quasiIso _ (.up ℤ)) e).isIso_hom

/-- The transpose `S ⊗_R (K ⊗ S_X) ⟶ S ⊗_R K` of the projection map `K ⊗ S_X ⟶ res (S ⊗_R K)`
along the adjunction between extension and restriction of scalars. -/
noncomputable def sheafExtendScalarsProjectionTranspose : tensorRight 𝓢 ⋙ 𝓔 ⟶ 𝓔 :=
  Functor.whiskerRight (sheafExtendScalarsProjection R S X) 𝓔 ≫
    Functor.whiskerLeft 𝓔 (sheafExtendScalarsAdjunction (algebraMap R S) X).counit

/-- **The transpose of the derived projection map**: on the image `Qh K` of an object of the
homotopy category, the transpose `Ψ (L(- ⊗ S_X) (Qh K)) ⟶ Ψ (Qh K)` along `Ψ ⊣ Res` of
`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection` is induced by the transpose
`S ⊗_R (K ⊗ S_X) ⟶ S ⊗_R K` of the projection map of sheaves. -/
lemma leftDerivedSheafExtendScalarsProjection_transpose
    (K : HomotopyCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (L(𝓔)).map ((leftDerivedSheafExtendScalarsProjection R S X).app (DerivedCategory.Qh.obj K)) ≫
        (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) X).counit.app
          ((L(𝓔)).obj (DerivedCategory.Qh.obj K)) ≫
        (𝓔).leftDerivedFunctorCounit.app K =
      (L(𝓔)).map ((tensorRight 𝓢).leftDerivedFunctorCounit.app K) ≫
        (𝓔).leftDerivedFunctorCounit.app (((tensorRight 𝓢).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (tensorRight 𝓢 ⋙ 𝓔)) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S X)
              (.up ℤ)).app K) :=
  leftDerived_projection_transpose_aux (TH := (tensorRight 𝓢).mapHomotopyCategory (.up ℤ))
    (EH := (𝓔).mapHomotopyCategory (.up ℤ)) (ResH := (𝓡).mapHomotopyCategory (.up ℤ))
    (𝓔).leftDerivedFunctorCounit (tensorRight 𝓢).leftDerivedFunctorCounit
    (𝓡).mapDerivedCategoryFactorsh (leftDerivedSheafExtendScalarsProjection R S X)
    (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) X)
    ((sheafExtendScalarsAdjunction (algebraMap R S) X).mapHomotopyCategory (.up ℤ))
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (tensorRight 𝓢 ⋙ 𝓔)) (.up ℤ))
    (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S X) (.up ℤ))
    (leftDerivedEtaleSheafExtendScalarsAdjunction_counit_app_Qh_obj (algebraMap R S) X) K
    ((NatTrans.mapHomotopyCategory (sheafExtendScalarsProjection R S X) (.up ℤ)).app K)
    ((leftDerivedSheafExtendScalarsRestrictScalarsCounit R S X).app K)
    (leftDerivedSheafExtendScalarsRestrictScalarsCounit_app R S X K)
    (leftDerivedSheafExtendScalarsProjection_app_comp_counit R S X K)
    (Adjunction.mapHomotopyCategory_map_comp_counit_app_of_eq
      (sheafExtendScalarsAdjunction (algebraMap R S) X) (sheafExtendScalarsProjection R S X)
      (sheafExtendScalarsProjectionTranspose R S X) rfl K)

end AlgebraicGeometry.Etale
