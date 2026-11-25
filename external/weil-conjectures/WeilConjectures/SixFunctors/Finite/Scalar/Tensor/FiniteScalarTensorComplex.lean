/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackComparison
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce

/-! # Tensor realization constructed from signed total comparisons

Source: Stacks Project, Tags 0GMW, 06YN, 07A4 and 04VK.
(blueprint: lem-sf-finite-scalar-tensor-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

/-- Countable colimits for the signed total, with the actual index universe cached.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarCountableColimits
    (T : Scheme.{u}) (R : Type u) [CommRing R] :
    HasColimitsOfSize.{0, 0}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) := by
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ T
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
    IsGrothendieckAbelian.hasColimits _
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _

attribute [local instance] finiteScalarCountableColimits

/-- Resolve the total-bifunctor colimit instance from the cached countable colimits.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarTensorTotal
    (T : Scheme.{u}) (R : Type u) [CommRing R]
    (V W : CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    HomologicalComplex.HasMapBifunctor V W (curriedTensor _) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (finiteScalarCountableColimits T R) _ _) _

attribute [local instance] finiteScalarTensorTotal

/-- Cache the intrinsic countable-colimit proof used by the total comparison.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarIntrinsicCountableColimits (T : Scheme.{u}) (R : Type u) [CommRing R] :
    HasColimitsOfSize.{0, 0} (proEtaleRingModules T (proEtaleConstantRing T R)) :=
  inferInstance

/-- Cache the realization's additive instance before specializing the total comparison.
Source: Stacks 0GMW (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarFunctorAdditive (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    (sfIntrinsicModuleEquivalence T R).functor.Additive := inferInstance

/-- Cache the realization's equivalence instance.
Source: Stacks 00YV (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarFunctorEquivalence (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    (sfIntrinsicModuleEquivalence T R).functor.IsEquivalence := inferInstance

/-- Cache the fixed-scalar tensor's additivity proof.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarFixedTensorPreadditive (T : Scheme.{u}) (R : Type u) [CommRing R] :
    MonoidalPreadditive
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) := inferInstance

attribute [local instance 10000] finiteScalarIntrinsicCountableColimits
  finiteScalarFunctorAdditive finiteScalarFunctorEquivalence finiteScalarFixedTensorPreadditive

/-- Flat-term K-flat fixed-scalar complexes. Source: Stacks 06YS.
(blueprint: lem-sf-finite-scalar-tensor-complex). -/
def finiteScalarFlatRepresentatives (T : Scheme.{u}) (R : Type u) [CommRing R] :
    ObjectProperty (CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :=
  fun P ↦ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
    ∀ n : ℤ, ObjectProperty.flat (P.X n)

/-- The realization's module sheafification inverts the fixed-scalar sheafification unit.
Source: Stacks 00YV (blueprint: lem-sf-finite-scalar-tensor-complex). -/
theorem finiteScalarModuleSheafificationUnit_isIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (P : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} R)) :
    let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)
    let S := PresheafOfModules.sheafification.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R)
    IsIso (S.map (E.map (toSheafify (ProEt.topology T) P))) := by
  dsimp only
  rw [← MorphismProperty.isomorphisms.iff]
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R))) _
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  change (ProEt.topology T).W
    (Functor.whiskerRight (toSheafify (ProEt.topology T) P)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) AddCommGrpCat.{u + 1}))
  let : (ProEt.topology T).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1} R))
  exact (ProEt.topology T).W_of_preservesSheafification _ _
    ((ProEt.topology T).W_toSheafify P)

/-- The sectionwise constant-module monoidal structure.
Source: Stacks 00CV (blueprint: lem-sf-finite-scalar-tensor-complex). -/
@[instance_reducible] def finiteScalarPresheafMonoidal (T : Scheme.{u}) (R : Type u)
    [CommRing R] :
    MonoidalCategory (PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} R)))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u + 1}
    (((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R))) ⋙
      forget₂ CommRingCat RingCat)))

attribute [local instance] finiteScalarPresheafMonoidal

/-- Curry an ordinary tensor isomorphism, retaining its actual components.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
def finiteScalarCurryTensorIso {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) :
    (postcompose₂.obj F).obj (curriedTensor C) ≅
      (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun N ↦ e.app (M, N))
      (by
        intro N N' f
        simpa using e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, f)))
    (by
      intro M M' f
      ext N
      simpa using e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N))

/-- Postcomposition commutes with uncurrying by the functor composition equation.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
def finiteScalarUncurryPostcomposeIso {C : Type u₁} {D : Type u₂} {E : Type u₃} {H : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} H]
    (F : C ⥤ D ⥤ E) (G : E ⥤ H) :
    uncurry.obj F ⋙ G ≅ uncurry.obj ((postcompose₂.obj G).obj F) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp [Functor.comp_map, Functor.uncurry, Functor.postcompose₂])

/-- The uncurrying conversion has identity components.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
@[simp] theorem finiteScalarUncurryPostcomposeIso_hom_app
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {H : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} H]
    (F : C ⥤ D ⥤ E) (G : E ⥤ H) (Z : C × D) :
    (finiteScalarUncurryPostcomposeIso F G).hom.app Z = 𝟙 _ := rfl

/-- The uncurried lax tensorator, without unfolding the monoidal structures.
Source: Stacks 07A4 (blueprint: lem-sf-finite-scalar-tensor-complex). -/
def finiteScalarLaxTensorNatTrans {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    F.prod F ⋙ uncurry.obj (curriedTensor D) ⟶ uncurry.obj (curriedTensor C) ⋙ F where
  app P := Functor.LaxMonoidal.μ F P.1 P.2
  naturality X Y f := by
    change (F.map f.1 ▷ F.obj X.2 ≫ F.obj Y.1 ◁ F.map f.2) ≫
        Functor.LaxMonoidal.μ F Y.1 Y.2 =
      Functor.LaxMonoidal.μ F X.1 X.2 ≫ F.map (f.1 ▷ X.2 ≫ Y.1 ◁ f.2)
    simpa only [← MonoidalCategory.tensorHom_def] using
      Functor.LaxMonoidal.μ_natural F f.1 f.2

/-- The actual sheafification tensor comparison used by realization.
Its inverse is determined on pure tensors by the sheafification units.
Source: Stacks 0GMW (blueprint: lem-sf-finite-scalar-tensor-complex). -/
@[irreducible] def finiteScalarOrdinaryTensorIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    tensor _ ⋙ (sfIntrinsicModuleEquivalence T R).functor ≅
      ((sfIntrinsicModuleEquivalence T R).functor.prod
        (sfIntrinsicModuleEquivalence T R).functor) ⋙
          @tensor (proEtaleRingModules T (proEtaleConstantRing T R)) _
            (SheafOfModules.monoidalCategory (proEtaleConstantRing T R)) := by
  let J := ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1} R)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)
  let S := PresheafOfModules.sheafification.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R)
  let U := sheafToPresheaf J B
  let L := presheafToSheaf J B
  let F := ProEtale.finiteCoefficientIntrinsicRealization T R
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T R)
  let t : E ⋙ S ⟶ L ⋙ F :=
    Functor.whiskerRight (sheafificationAdjunction J B).unit (E ⋙ S)
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact finiteScalarModuleSheafificationUnit_isIso T R P
  let h : E ⋙ S ≅ L ⋙ F := asIso t
  let c := asIso (sheafificationAdjunction J B).counit
  let e : U.prod U ⋙ tensor _ ⋙ L ≅ tensor _ :=
    isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
      isoWhiskerRight (NatIso.prod c c) (tensor _)
  let eE : tensor _ ⋙ E ≅ E.prod E ⋙ tensor _ := Iso.refl _
  let eS := Classical.choose
    (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R))
  exact (isoWhiskerRight e F).symm ≪≫
    isoWhiskerLeft (U.prod U ⋙ tensor _) h.symm ≪≫
    isoWhiskerLeft (U.prod U) (isoWhiskerRight eE S) ≪≫
    isoWhiskerLeft ((U ⋙ E).prod (U ⋙ E)) eS.symm

/-- The total tensor comparison built in abstract categories, to keep specialization small.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
@[irreducible] def finiteScalarTotalTensorIsoOfOrdinary
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) :
    uncurry.obj ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        uncurry.obj ((curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) := by
  let τ := finiteScalarCurryTensorIso F e
  exact finiteScalarUncurryPostcomposeIso
      ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) ≪≫
    uncurry.mapIso (asIso
      (HomologicalComplex.mapBifunctorComparisonNatTrans
        (F := curriedTensor C) (F' := curriedTensor D) (G₁ := F) (G₂ := F) (G := F)
        (c₁ := .up ℤ) (c₂ := .up ℤ) τ.hom (.up ℤ)))

/-- The signed total of the specified ordinary tensor map, as a natural isomorphism.
Source: Stacks 06YN (blueprint: lem-sf-finite-scalar-tensor-complex). -/
@[irreducible] def finiteScalarTotalTensorIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :=
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T R)
  finiteScalarTotalTensorIsoOfOrdinary
    (sfIntrinsicModuleEquivalence T R).functor (finiteScalarOrdinaryTensorIso T R)

end WeilConjectures
