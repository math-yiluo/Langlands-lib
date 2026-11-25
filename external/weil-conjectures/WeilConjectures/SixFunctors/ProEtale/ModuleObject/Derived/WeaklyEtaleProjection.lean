/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.ProjectionMap
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale
import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom

/-!
# The derived projection formula along a weakly étale morphism

Let `Λ` be a commutative condensed ring and `g : W ⟶ X` a weakly étale morphism. This file
shows that the derived extension by zero `Dg_!` (the exact extension by zero
`ProEtale.CondensedRing.weaklyEtaleLowerShriek` applied levelwise) is left adjoint to the
derived pullback `Lg^*` on derived categories of module objects over `Λ`, and that this
adjunction satisfies the projection formula: the projection map
`Dg_!(Lg^* M ⊗ᴸ T) ⟶ M ⊗ᴸ Dg_! T` is an isomorphism.

## The argument

* On module objects, `g^*` commutes with internal homs: it is the transport `mapMod(g^*)` of
  module objects along the pullback of sheaves, which commutes with internal homs
  (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`,
  `CategoryTheory.Mod.isIso_ihomComparison_mapMod`), followed by an extension of scalars along
  an isomorphism. Hence the projection maps of `g_! ⊣ g^*` are isomorphisms.
* On cochain complexes the projection maps are then isomorphisms degreewise
  (`CategoryTheory.Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex`).
* On a K-flat complex `K` (whose pullback `g^* K` is again K-flat), the derived projection
  map is the image of the projection map on cochain complexes, up to the tensor comparison
  maps of `Qh`, which are isomorphisms on K-flat complexes.

## Main results

- `ProEtale.CondensedRing.derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction`:
  the adjunction `Dg_! ⊣ Lg^*`.
- `ProEtale.CondensedRing.isIso_projectionMap_derivedWeaklyEtaleLowerShriek`: the derived
  projection formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

-- Cancel the inverse tensor comparison before specializing to derived categories.
private theorem tensorComparison_of_oplax
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {A B : C} {X Y U V : D} (d : A ⟶ B) (m : B ⟶ A) (e : X ≅ Y)
    (f : X ⟶ U) (f' : U ⟶ Q.obj A) (t : Y ⟶ V) (t' : V ⟶ Q.obj B)
    (h : e.hom ≫ t ≫ t' = f ≫ f' ≫ Q.map d) (hd : d ≫ m = 𝟙 _) :
    e.inv ≫ f ≫ f' = t ≫ t' ≫ Q.map m := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc, reassoc_of% h,
    ← Q.map_comp, hd, Q.map_id, Category.comp_id]

-- The formal mate calculation only uses the comparison squares and their unit/counit formulas.
private theorem projectionMap_of_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    {L : D ⥤ C} {G : C ⥤ D} {L' : D' ⥤ C'} {G' : C' ⥤ D'} [G'.Monoidal]
    (adj : L ⊣ G) (adj' : L' ⊣ G') (Q : C ⥤ C') (R : D ⥤ D')
    [Q.LaxMonoidal] [R.LaxMonoidal]
    (a : R ⋙ L' ≅ L ⋙ Q) (b : Q ⋙ G' ≅ G ⋙ R) (A : C) (T : D)
    (m : G.obj A ⊗ G.obj (L.obj T) ⟶ G.obj (A ⊗ L.obj T))
    (hu : adj'.unit.app (R.obj T) =
      R.map (adj.unit.app T) ≫ b.inv.app (L.obj T) ≫ G'.map (a.inv.app T))
    (hc : adj'.counit.app (Q.obj (A ⊗ L.obj T)) =
      L'.map (b.hom.app (A ⊗ L.obj T)) ≫ a.hom.app (G.obj (A ⊗ L.obj T)) ≫
        Q.map (adj.counit.app (A ⊗ L.obj T)))
    (hm : Functor.LaxMonoidal.μ G' (Q.obj A) (Q.obj (L.obj T)) ≫
      G'.map (Functor.LaxMonoidal.μ Q A (L.obj T)) ≫ b.hom.app (A ⊗ L.obj T) =
      (b.hom.app A ⊗ₘ b.hom.app (L.obj T)) ≫
        Functor.LaxMonoidal.μ R (G.obj A) (G.obj (L.obj T)) ≫ R.map m)
    (p : L.obj (G.obj A ⊗ T) ⟶ A ⊗ L.obj T)
    (hp : L.map (G.obj A ◁ adj.unit.app T ≫ m) ≫ adj.counit.app (A ⊗ L.obj T) = p) :
    (Functor.Monoidal.projectionMap adj' (Q.obj A)).app (R.obj T) ≫
      (Q.obj A ◁ a.hom.app T) ≫ Functor.LaxMonoidal.μ Q A (L.obj T) =
    L'.map ((b.hom.app A ▷ R.obj T) ≫ Functor.LaxMonoidal.μ R (G.obj A) T) ≫
      a.hom.app (G.obj A ⊗ T) ≫ Q.map p := by
  rw [← hp]
  simp only [Functor.Monoidal.projectionMap, Category.assoc]
  have hn := (adj'.counit.naturality
    (Q.obj A ◁ a.hom.app T ≫ Functor.LaxMonoidal.μ Q A (L.obj T))).symm
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hn
  rw [hn, hc, hu]
  simp only [Functor.map_comp, Category.assoc]
  have ha' {Y Y' : D} (f : Y ⟶ Y') :
      a.hom.app Y ≫ Q.map (L.map f) = L'.map (R.map f) ≫ a.hom.app Y' :=
    (a.hom.naturality f).symm
  rw [reassoc_of% ha', reassoc_of% ha']
  simp only [← Functor.map_comp_assoc]
  congr 2
  have ha : (Q.obj A ◁ a.inv.app T) ≫ (Q.obj A ◁ a.hom.app T) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
      MonoidalCategory.whiskerLeft_id]
  simp only [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (Functor.LaxMonoidal.μ_natural_right G' (Q.obj A) (a.inv.app T))]
  rw [← Functor.map_comp_assoc G', ha]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, hm, MonoidalCategory.tensorHom_def, Category.assoc]
  erw [whisker_exchange_assoc]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_app,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, whisker_exchange_assoc]
  erw [reassoc_of% (Functor.LaxMonoidal.μ_natural_right R (G.obj A) (adj.unit.app T))]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {W X : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]

/-! ### The underived projection formula -/

/-- The pullback of module objects along a weakly étale morphism commutes with internal homs:
the comparison `g^* Hom_{Λ_X}(M, N) ⟶ Hom_{Λ_W}(g^* M, g^* N)` is an isomorphism. -/
instance isIso_ihomComparison_upperStar_of_weaklyEtale
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (Functor.LaxMonoidal.ihomComparison (g)^*⟦Λ⟧ M) := by
  have (Z : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      IsIso (Functor.LaxMonoidal.ihomComparison (g)^*[Ab.{u + 1}] Z) :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} g Z
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  erw [Functor.LaxMonoidal.ihomComparison_comp_app ((g)^*[Ab.{u + 1}].mapMod _)
    (Mod.extendScalars (condensedPullbackHom Λ g))]
  infer_instance

/-- The projection map `g_!(g^* M ⊗ T) ⟶ M ⊗ g_! T` of the adjunction `g_! ⊣ g^*` on module
objects along a weakly étale morphism is an isomorphism. -/
instance isIso_projectionMap_weaklyEtaleLowerShriekUpperStarAdjunction
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (Functor.Monoidal.projectionMap (weaklyEtaleLowerShriekUpperStarAdjunction Λ g) M) :=
  Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison _ M

/-! ### The derived adjunction -/

/-- The derived adjunction `Dg_! ⊣ Lg^*` along a weakly étale morphism `g`, with the right
adjoint the left derived functor `Lg^*` (isomorphic to the levelwise `D(g^*)`, `g^*` being
exact): the localization of the adjunction `g_! ⊣ g^*` on homotopy categories. -/
noncomputable def derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction :
    (weaklyEtaleLowerShriek Λ g).mapDerivedCategory ⊣ L((g)^*⟦Λ⟧) :=
  let _ : CatCommSq ((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh (weaklyEtaleLowerShriek Λ g).mapDerivedCategory :=
    ⟨(weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.symm⟩
  let _ : CatCommSq (((g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh L((g)^*⟦Λ⟧) :=
    ⟨(asIso ((g)^*⟦Λ⟧).leftDerivedFunctorCounit).symm⟩
  ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory
    (.up ℤ)).localization DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ _

/-! ### The derived projection formula -/

/-- The pullback of module objects preserves the coproducts defining the tensor product of
cochain complexes, being a left adjoint. -/
instance preservesColimitsOfShape_upperStar_discrete_π (j : ℤ) :
    PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) (g)^*⟦Λ⟧ :=
  inferInstance

/-- The extension by zero of module objects preserves the coproducts defining the tensor
product of cochain complexes, being a left adjoint. -/
instance preservesColimitsOfShape_weaklyEtaleLowerShriek_discrete_π (j : ℤ) :
    PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) (weaklyEtaleLowerShriek Λ g) :=
  have : PreservesColimitsOfSize.{0, 0} (weaklyEtaleLowerShriek Λ g) :=
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ g).leftAdjoint_preservesColimits
  inferInstance

/-- The pullback of module objects is monoidal on cochain complexes. -/
noncomputable instance monoidal_upperStar_mapHomologicalComplex :
    ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).Monoidal :=
  Functor.mapCochainComplexMonoidal _

open HomotopyCategory DerivedCategory in
private lemma weaklyEtaleProjection_unit
    (T : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) (.up ℤ)) :
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g).unit.app (Qh.obj T) =
      Qh.map (((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory
        (.up ℤ)).unit.app T) ≫
      (asIso ((g)^*⟦Λ⟧.leftDerivedFunctorCounit)).inv.app
        (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj T) ≫
      L((g)^*⟦Λ⟧).map ((weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.inv.app T) := by
  unfold derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction
  rw [Adjunction.localization_unit_app]
  rfl

open HomotopyCategory DerivedCategory in
private lemma weaklyEtaleProjection_counit
    (A : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (.up ℤ)) :
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g).counit.app (Qh.obj A) =
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map
        ((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app A) ≫
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app
        (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ≫
      Qh.map (((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory
        (.up ℤ)).counit.app A) := by
  unfold derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction
  rw [Adjunction.localization_counit_app]
  rfl

omit [WeaklyEtale g] in
open HomotopyCategory DerivedCategory in
private lemma weaklyEtaleProjection_tensorComparison
    (K₁ K₂ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) :
    Functor.LaxMonoidal.μ L((g)^*⟦Λ⟧) (Qh.obj ((quotient _ _).obj K₁))
      (Qh.obj ((quotient _ _).obj K₂)) ≫
    L((g)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
      ((quotient _ _).obj K₂)) ≫
    (g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((quotient _ _).obj K₁ ⊗
      (quotient _ _).obj K₂) =
    ((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ⊗ₘ
      (g)^*⟦Λ⟧.leftDerivedFunctorCounit.app
        ((quotient _ _).obj K₂)) ≫
    Functor.LaxMonoidal.μ Qh (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
        ((quotient _ _).obj K₁))
      (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
        ((quotient _ _).obj K₂)) ≫
    Qh.map ((quotient _ _).map (Functor.LaxMonoidal.μ ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ))
      K₁ K₂)) := by
  have h := leftDerivedUpperStarTensor_laxSquare Λ g
    ((quotient _ _).obj K₁) ((quotient _ _).obj K₂)
  exact tensorComparison_of_oplax Qh
    ((quotient _ _).map (Functor.OplaxMonoidal.δ
      ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)) K₁ K₂))
    ((quotient _ _).map (Functor.LaxMonoidal.μ
      ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)) K₁ K₂))
    (Functor.Monoidal.μIso L((g)^*⟦Λ⟧) _ _).symm
    _ _ _ _ h (by rw [← Functor.map_comp, Functor.Monoidal.δ_μ,
      CategoryTheory.Functor.map_id])

open HomotopyCategory in
private lemma weaklyEtaleProjection_mapProjection
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (T : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) ℤ) :
    ((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).map
      ((((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K) ◁
        ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory (.up ℤ)).unit.app
          ((quotient _ _).obj T)) ≫
        (quotient _ _).map (Functor.LaxMonoidal.μ ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ))
          K (((weaklyEtaleLowerShriek Λ g).mapHomologicalComplex (.up ℤ)).obj T))) ≫
      ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory (.up ℤ)).counit.app
        ((quotient _ _).obj K ⊗
          ((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj T)) =
    (quotient _ _).map
      ((Functor.Monoidal.projectionMap
        ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomologicalComplex
          (.up ℤ)) K).app T) := by
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  erw [← HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft']
  rw [← Functor.map_comp, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  rfl

open HomotopyCategory DerivedCategory in
/-- On objects coming from cochain complexes, the derived projection map of `Dg_! ⊣ Lg^*` is
the image of the projection map on cochain complexes, up to the tensor comparison maps of
`Qh`. -/
lemma projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh
    (K₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (T₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) ℤ) :
    (Functor.Monoidal.projectionMap (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction
        Λ g) (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁)) ≫
      (Qh.obj ((quotient _ _).obj K₁) ◁
        (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app
          ((quotient _ _).obj T₁)) ≫
      Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
    (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map
        (((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ▷
          Qh.obj ((quotient _ _).obj T₁)) ≫
          Functor.LaxMonoidal.μ Qh _ ((quotient _ _).obj T₁)) ≫
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app _ ≫
        Qh.map ((quotient _ _).map ((Functor.Monoidal.projectionMap
          ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomologicalComplex
            (.up ℤ)) K₁).app T₁)) := by
  exact projectionMap_of_comparison
    ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory (.up ℤ))
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) Qh Qh
    (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh
    (asIso ((g)^*⟦Λ⟧.leftDerivedFunctorCounit))
    ((quotient _ _).obj K₁) ((quotient _ _).obj T₁)
    ((quotient _ _).map (Functor.LaxMonoidal.μ ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ))
      K₁ (((weaklyEtaleLowerShriek Λ g).mapHomologicalComplex (.up ℤ)).obj T₁)))
    (weaklyEtaleProjection_unit Λ g _) (weaklyEtaleProjection_counit Λ g _)
    (weaklyEtaleProjection_tensorComparison Λ g K₁
      (((weaklyEtaleLowerShriek Λ g).mapHomologicalComplex (.up ℤ)).obj T₁))
    _ (weaklyEtaleProjection_mapProjection Λ g K₁ T₁)

-- the K-flat derivability structure on complexes of module objects is found by instance search
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh` on complexes of module
objects over `Λ_Z` is an isomorphism when `K` is K-flat. The case of a K-flat `M` is
`CategoryTheory.Functor.isIso_μNatTrans_Qh_app_app_of_kFlat`. -/
lemma isIso_μ_Qh_of_kFlat_left {Z : Scheme.{u}}
    (K M : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) (.up ℤ))
    (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh K M) := by
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Z
  have := DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
  exact (MorphismProperty.kFlat_prod_id_derives_curriedTensor
    (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh).isIso_of_isLeftDerivabilityStructure
      (LF := curriedTensor (DerivedCategory _)) (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      ⟨K, hK⟩ M

-- the instances on complexes of module objects make the elaboration slow
open HomotopyCategory DerivedCategory in
/-- The derived projection map of `Dg_! ⊣ Lg^*` is an isomorphism at `M = Qh K₁` for a K-flat
complex `K₁`: it is then the image of the projection map on cochain complexes, which is an
isomorphism degreewise, up to the tensor comparison maps of `Qh`, which are isomorphisms since
`K₁` and `g^* K₁` are K-flat. -/
lemma isIso_projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh
    (K₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (hK₁ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K₁)
    (T₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) ℤ) :
    IsIso ((Functor.Monoidal.projectionMap
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g)
        (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁))) := by
  have h := projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh Λ g K₁ T₁
  have := isIso_μ_Qh_of_kFlat_left Λ ((quotient _ _).obj K₁)
    (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj T₁))
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hK₁)
  have := isIso_μ_Qh_of_kFlat_left Λ
    (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K₁))
    ((quotient _ _).obj T₁) (kFlat_upperStar_mapHomotopyCategory_obj Λ g hK₁)
  have := Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex (g)^*⟦Λ⟧
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ g) K₁
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- **The derived projection formula along a weakly étale morphism**: the projection map
`Dg_!(Lg^* M ⊗ᴸ T) ⟶ M ⊗ᴸ Dg_! T` of the adjunction `Dg_! ⊣ Lg^*` is an isomorphism. -/
instance isIso_projectionMap_derivedWeaklyEtaleLowerShriek
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (Functor.Monoidal.projectionMap
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M) := by
  obtain ⟨P, hP, ⟨eM⟩⟩ := exists_kFlat_iso_Qh_obj Λ M
  obtain ⟨K₁, rfl⟩ := P.quotient_obj_surjective
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  let T₀ := DerivedCategory.Q.objPreimage T
  let eT : T ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀) :=
    (DerivedCategory.Q.objObjPreimageIso T).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app T₀
  have := isIso_projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh Λ g K₁
    ((HomotopyCategory.kFlat_quotient_obj_iff _).1 hP) T₀
  have := Functor.Monoidal.isIso_projectionMap_app_of_iso
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) eM.symm
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀))
  have hn := (Functor.Monoidal.projectionMap
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M).naturality eT.hom
  have : IsIso ((Functor.Monoidal.projectionMap
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M).app T ≫
      M ◁ (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map eT.hom) := by
    erw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (M ◁ (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map eT.hom)

end AlgebraicGeometry.ProEtale.CondensedRing
