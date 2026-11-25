/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.DerivedCompAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory DerivedCategory Functor.LaxMonoidal

open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- the images of complexes in the homotopy category are unfolded
lemma leftDerivedUpperStarTensor_comp_aux
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    ((leftDerivedUpperStarTensor Λ (f ≫ g)).app
      (Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
        (Qh.obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      ((f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A) ⊗ₘ
        (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) ≫
      μ Qh (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
        (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B)) =
    ((leftDerivedUpperStarComp Λ f g).hom.app (Qh.obj ((HomotopyCategory.quotient _ _).obj A) ⊗
        Qh.obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      L((f)^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app
        (Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
          (Qh.obj ((HomotopyCategory.quotient _ _).obj B))) ≫
      ((leftDerivedUpperStarTensor Λ f).app _).app _ ≫
      ((leftDerivedUpperStarComp Λ f g).inv.app (Qh.obj ((HomotopyCategory.quotient _ _).obj A)) ⊗ₘ
        (leftDerivedUpperStarComp Λ f g).inv.app
          (Qh.obj ((HomotopyCategory.quotient _ _).obj B)))) ≫
      ((f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A) ⊗ₘ
        (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) ≫
      μ Qh (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
        (((f ≫ g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B)) := by
  have : IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (.up ℤ)).app (A ⊗ B))) :=
    inferInstanceAs (IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (upperStarComp Λ f g) (.up ℤ)).app (A ⊗ B)).hom))
  have : IsIso ((NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj A ⊗
        (HomotopyCategory.quotient _ (.up ℤ)).obj B)) :=
    ⟨(NatTrans.mapHomotopyCategory (upperStarComp Λ f g).inv (.up ℤ)).app _, by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      rfl, by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]
      rfl⟩
  exact derivedComp_tensor_aux (g)^*⟦Λ⟧.leftDerivedFunctorCounit (f)^*⟦Λ⟧.leftDerivedFunctorCounit
    (f ≫ g)^*⟦Λ⟧.leftDerivedFunctorCounit (leftDerivedUpperStarComp Λ f g)
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ g).app K).app M)
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ f).app K).app M)
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ (f ≫ g)).app K).app M)
    ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)
    (fun K ↦ (NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app K)
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ g A B))
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f
      (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj A) (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj B)))
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (f ≫ g) A B))
    (leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit Λ f g)
    (leftDerivedUpperStarTensor_app_app_comp Λ (f ≫ g) _ _)
    (leftDerivedUpperStarTensor_app_app_comp Λ g _ _)
    (leftDerivedUpperStarTensor_app_app_comp Λ f _ _)
    (leftDerivedUpperStarTensor_naturality Λ f _ _)
    (quotient_map_upperStarTensorComplexHom_comp Λ f g A B)

-- the derived tensor products of module objects are unfolded
/-- The composite `L(f ≫ g)^*(K ⊗ᴸ M) ≅ Lf^* Lg^*(K ⊗ᴸ M) ⟶ Lf^*(Lg^* K ⊗ᴸ Lg^* M) ⟶
Lf^* Lg^* K ⊗ᴸ Lf^* Lg^* M ≅ L(f ≫ g)^* K ⊗ᴸ L(f ≫ g)^* M` of the tensor comparisons of `Lg^*` and
`Lf^*`, read through the composition isomorphism. -/
noncomputable def leftDerivedUpperStarTensorComp :
    leftDerivedUpperStarTensorLeft Λ (f ≫ g) ⟶ leftDerivedUpperStarTensorRight Λ (f ≫ g) :=
  Functor.whiskerLeft (curriedTensor _)
      ((Functor.whiskeringRight _ _ _).map (leftDerivedUpperStarComp Λ f g).hom) ≫
    Functor.whiskerRight (leftDerivedUpperStarTensor Λ g)
      ((Functor.whiskeringRight _ _ _).obj L((f)^*⟦Λ⟧)) ≫
    (((Functor.whiskeringLeft₂ _).obj L((g)^*⟦Λ⟧)).obj L((g)^*⟦Λ⟧)).map
      (leftDerivedUpperStarTensor Λ f) ≫
    (((Functor.whiskeringLeft₂ _).map (leftDerivedUpperStarComp Λ f g).inv).app
      (L((g)^*⟦Λ⟧) ⋙ L((f)^*⟦Λ⟧))).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj L((f ≫ g)^*⟦Λ⟧)).map
      (leftDerivedUpperStarComp Λ f g).inv).app (curriedTensor _)

lemma leftDerivedUpperStarTensorComp_app_app
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    ((leftDerivedUpperStarTensorComp Λ f g).app K).app M =
      (leftDerivedUpperStarComp Λ f g).hom.app (K ⊗ M) ≫
        L((f)^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app K).app M) ≫
        ((leftDerivedUpperStarTensor Λ f).app _).app _ ≫
        ((leftDerivedUpperStarComp Λ f g).inv.app K ⊗ₘ
          (leftDerivedUpperStarComp Λ f g).inv.app M) := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

-- the images of complexes in the homotopy category are unfolded
lemma leftDerivedUpperStarTensor_comp_eq :
    leftDerivedUpperStarTensor Λ (f ≫ g) = leftDerivedUpperStarTensorComp Λ f g := by
  refine Functor.leftDerived₂_ext (leftDerivedUpperStarTensorRight Λ (f ≫ g))
    (leftDerivedUpperStarTensorRightCounit Λ (f ≫ g)) (HomotopyCategory.quasiIso _ _)
    (HomotopyCategory.quasiIso _ _) _ _ _ ?_
  ext P Q
  change ((leftDerivedUpperStarTensor Λ (f ≫ g)).app (Qh.obj P)).app (Qh.obj Q) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ (f ≫ g)).app P).app Q =
    ((leftDerivedUpperStarTensorComp Λ f g).app (Qh.obj P)).app (Qh.obj Q) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ (f ≫ g)).app P).app Q
  rw [leftDerivedUpperStarTensorRightCounit_app_app_eq_tensorHom]
  rw [leftDerivedUpperStarTensorComp_app_app]
  exact leftDerivedUpperStarTensor_comp_aux Λ f g P.as Q.as

/-- **The composition isomorphism of the derived pullbacks of module objects is monoidal**: it
commutes with the tensor comparisons `m : Lh^* (K ⊗ᴸ M) ⟶ Lh^* K ⊗ᴸ Lh^* M`. -/
@[reassoc]
lemma leftDerivedUpperStarTensor_comp
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    ((leftDerivedUpperStarTensor Λ (f ≫ g)).app K).app M ≫
        ((leftDerivedUpperStarComp Λ f g).hom.app K ⊗ₘ (leftDerivedUpperStarComp Λ f g).hom.app M) =
      (leftDerivedUpperStarComp Λ f g).hom.app (K ⊗ M) ≫
        L((f)^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app K).app M) ≫
        ((leftDerivedUpperStarTensor Λ f).app _).app _ := by
  refine comp_tensorHom_hom_eq_of_eq_comp_tensorHom_inv
    ((leftDerivedUpperStarComp Λ f g).app K) ((leftDerivedUpperStarComp Λ f g).app M) ?_
  rw [leftDerivedUpperStarTensor_comp_eq, leftDerivedUpperStarTensorComp_app_app]
  simp only [Category.assoc]
  rfl

/-- `leftDerivedUpperStarTensor_comp` for a morphism `h` equal to `f ≫ g`. -/
lemma leftDerivedUpperStarTensor_comp_of_eq {h : X ⟶ Z} (hh : h = f ≫ g)
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    ((leftDerivedUpperStarTensor Λ h).app K).app M ≫
        ((eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarComp Λ f g).hom.app K) ⊗ₘ
          (eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarComp Λ f g).hom.app M)) =
      (eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarComp Λ f g).hom.app (K ⊗ M)) ≫
        L((f)^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app K).app M) ≫
        ((leftDerivedUpperStarTensor Λ f).app _).app _ := by
  subst hh
  simp only [eqToHom_refl, Category.id_comp]
  exact leftDerivedUpperStarTensor_comp Λ f g K M

/-! ### The identity isomorphism -/

variable (W : Scheme.{u})

/-- The composite `L(𝟙 W)^*(K ⊗ᴸ M) ≅ K ⊗ᴸ M ≅ L(𝟙 W)^* K ⊗ᴸ L(𝟙 W)^* M` of the identity
isomorphisms. It is the tensor comparison of `L(𝟙 W)^*` (`leftDerivedUpperStarTensor_id_eq`). -/
noncomputable def leftDerivedUpperStarTensorId :
    leftDerivedUpperStarTensorLeft Λ (𝟙 W) ⟶ leftDerivedUpperStarTensorRight Λ (𝟙 W) :=
  Functor.whiskerLeft (curriedTensor _)
      ((Functor.whiskeringRight _ _ _).map (leftDerivedUpperStarId Λ W).hom) ≫
    (((Functor.whiskeringLeft₂ _).map (leftDerivedUpperStarId Λ W).inv).app (𝟭 _)).app
      (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj L((𝟙 W)^*⟦Λ⟧)).map
      (leftDerivedUpperStarId Λ W).inv).app (curriedTensor _)

lemma leftDerivedUpperStarTensorId_app_app
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))) :
    ((leftDerivedUpperStarTensorId Λ W).app K).app M =
      (leftDerivedUpperStarId Λ W).hom.app (K ⊗ M) ≫
        ((leftDerivedUpperStarId Λ W).inv.app K ⊗ₘ (leftDerivedUpperStarId Λ W).inv.app M) := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

-- the images of complexes in the homotopy category are unfolded
lemma leftDerivedUpperStarTensor_id_aux
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ℤ) :
    ((leftDerivedUpperStarId Λ W).hom.app (Qh.obj ((HomotopyCategory.quotient _ _).obj A) ⊗
          Qh.obj ((HomotopyCategory.quotient _ _).obj B)) ≫
        ((leftDerivedUpperStarId Λ W).inv.app (Qh.obj ((HomotopyCategory.quotient _ _).obj A)) ⊗ₘ
          (leftDerivedUpperStarId Λ W).inv.app (Qh.obj ((HomotopyCategory.quotient _ _).obj B)))) ≫
      ((𝟙 W)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A) ⊗ₘ
        (𝟙 W)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) ≫
      μ Qh (((𝟙 W)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
        (((𝟙 W)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B)) ≫
      Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (𝟙 W) A B)) =
    L((𝟙 W)^*⟦Λ⟧).map (μ Qh ((HomotopyCategory.quotient _ _).obj A)
        ((HomotopyCategory.quotient _ _).obj B)) ≫
      (𝟙 W)^*⟦Λ⟧.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj A ⊗ (HomotopyCategory.quotient _ _).obj B) := by
  have : IsIso (Qh.map ((NatTrans.mapHomotopyCategory (upperStarId Λ W).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj A ⊗ (HomotopyCategory.quotient _ (.up ℤ)).obj B) ≫
      (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj A ⊗
          (HomotopyCategory.quotient _ (.up ℤ)).obj B))) := by
    have : IsIso ((NatTrans.mapHomotopyCategory (upperStarId Λ W).hom (.up ℤ)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj A ⊗
          (HomotopyCategory.quotient _ (.up ℤ)).obj B)) :=
      inferInstanceAs (IsIso ((NatIso.mapHomotopyCategory (upperStarId Λ W) (.up ℤ)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj A ⊗
          (HomotopyCategory.quotient _ (.up ℤ)).obj B)).hom)
    infer_instance
  exact derivedId_tensor_aux (𝟙 W)^*⟦Λ⟧.leftDerivedFunctorCounit (leftDerivedUpperStarId Λ W)
    ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)
    (fun K ↦ (NatTrans.mapHomotopyCategory (upperStarId Λ W).hom (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app K)
    ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ (𝟙 W) A B))
    (Functor.leftDerivedFunctorIdIso_hom_app_Qh_obj (upperStarId Λ W))
    (quotient_map_upperStarTensorComplexHom_id Λ W A B)

-- the images of complexes in the homotopy category are unfolded
lemma leftDerivedUpperStarTensor_id_eq :
    leftDerivedUpperStarTensor Λ (𝟙 W) = leftDerivedUpperStarTensorId Λ W := by
  refine Functor.leftDerived₂_ext (leftDerivedUpperStarTensorRight Λ (𝟙 W))
    (leftDerivedUpperStarTensorRightCounit Λ (𝟙 W)) (HomotopyCategory.quasiIso _ _)
    (HomotopyCategory.quasiIso _ _) _ _ _ ?_
  ext P Q
  change ((leftDerivedUpperStarTensor Λ (𝟙 W)).app (Qh.obj P)).app (Qh.obj Q) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ (𝟙 W)).app P).app Q =
    ((leftDerivedUpperStarTensorId Λ W).app (Qh.obj P)).app (Qh.obj Q) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ (𝟙 W)).app P).app Q
  rw [leftDerivedUpperStarTensorRightCounit_app_app_eq_tensorHom]
  rw [leftDerivedUpperStarTensorId_app_app, leftDerivedUpperStarTensor_app_app_comp]
  exact (leftDerivedUpperStarTensor_id_aux Λ W P.as Q.as).symm

/-- **The identity isomorphism of the derived pullbacks of module objects is monoidal**:
`L(𝟙 W)^*(K ⊗ᴸ M) ⟶ L(𝟙 W)^* K ⊗ᴸ L(𝟙 W)^* M ⟶ K ⊗ᴸ M` is the identity isomorphism. -/
lemma leftDerivedUpperStarTensor_id
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))) :
    ((leftDerivedUpperStarTensor Λ (𝟙 W)).app K).app M ≫
        ((leftDerivedUpperStarId Λ W).hom.app K ⊗ₘ (leftDerivedUpperStarId Λ W).hom.app M) =
      (leftDerivedUpperStarId Λ W).hom.app (K ⊗ M) := by
  refine comp_tensorHom_hom_eq_of_eq_comp_tensorHom_inv
    ((leftDerivedUpperStarId Λ W).app K) ((leftDerivedUpperStarId Λ W).app M) ?_
  rw [leftDerivedUpperStarTensor_id_eq, leftDerivedUpperStarTensorId_app_app]
  rfl

/-- `leftDerivedUpperStarTensor_id` for a morphism `h` equal to `𝟙 W`. -/
lemma leftDerivedUpperStarTensor_id_of_eq {h : W ⟶ W} (hh : h = 𝟙 W)
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))) :
    ((leftDerivedUpperStarTensor Λ h).app K).app M ≫
        ((eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarId Λ W).hom.app K) ⊗ₘ
          (eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarId Λ W).hom.app M)) =
      eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarId Λ W).hom.app (K ⊗ M) := by
  subst hh
  simp only [eqToHom_refl, Category.id_comp]
  exact leftDerivedUpperStarTensor_id Λ W K M

end AlgebraicGeometry.ProEtale.CondensedRing
