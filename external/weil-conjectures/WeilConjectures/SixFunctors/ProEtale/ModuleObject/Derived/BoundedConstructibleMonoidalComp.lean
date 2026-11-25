/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided

/-!
# The composition isomorphisms of the derived pullbacks of bounded constructible complexes are
monoidal

The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp`) commutes with the tensor comparisons
of the strong monoidal pullbacks
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp_hom_app_tensor_δ`). It is the
restriction of the corresponding statement on the ambient derived categories
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory

lemma eqToHom_comp_of_self {C : Type*} [Category C] {A B : C} (p : A = A) (x : A ⟶ B) :
    eqToHom p ≫ x = x := by
  simp

end CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

/-! ### The ambient statements in terms of the tensor comparisons `δ`

The statements on bounded constructible complexes are restrictions of statements on the ambient
derived categories. Those are stated here with the tensor comparisons `δ` of the strong monoidal
functors `L((f)^*⟦Λ⟧)` rather than with `ProEtale.CondensedRing.leftDerivedUpperStarTensor`, and
for a general coefficient ring `Λ`: then the objects in their types have the same form as in the
restricted statements, and the kernel does not have to unfold the derived pullbacks of the
concrete coefficient ring `ℚ̲̄_ℓ` to compare them. -/

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- `ProEtale.CondensedRing.leftDerivedUpperStarTensor_comp_of_eq` in terms of the tensor
comparisons `δ`: the composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` commutes with the
tensor comparisons `δ : Lh^* (K ⊗ᴸ M) ⟶ Lh^* K ⊗ᴸ Lh^* M`. -/
lemma δ_leftDerivedUpperStar_comp_of_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (hh : h = f ≫ g)
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    δ L((h)^*⟦Λ⟧) K M ≫
        ((eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarComp Λ f g).hom.app K) ⊗ₘ
          (eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarComp Λ f g).hom.app M)) =
      (eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarComp Λ f g).hom.app (K ⊗ M)) ≫
        L((f)^*⟦Λ⟧).map (δ L((g)^*⟦Λ⟧) K M) ≫ δ L((f)^*⟦Λ⟧) _ _ :=
  leftDerivedUpperStarTensor_comp_of_eq Λ f g hh K M

/-- `ProEtale.CondensedRing.leftDerivedUpperStarTensor_id_of_eq` in terms of the tensor
comparisons `δ`: `L(𝟙 W)^*(K ⊗ᴸ M) ⟶ L(𝟙 W)^* K ⊗ᴸ L(𝟙 W)^* M ⟶ K ⊗ᴸ M` is the identity
isomorphism. -/
lemma δ_leftDerivedUpperStar_id_of_eq {W : Scheme.{u}} {h : W ⟶ W} (hh : h = 𝟙 W)
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))) :
    δ L((h)^*⟦Λ⟧) K M ≫
        ((eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarId Λ W).hom.app K) ⊗ₘ
          (eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarId Λ W).hom.app M)) =
      eqToHom (by subst hh; rfl) ≫ (leftDerivedUpperStarId Λ W).hom.app (K ⊗ M) :=
  leftDerivedUpperStarTensor_id_of_eq Λ W hh K M

/-- `ProEtale.CondensedRing.leftDerivedUpperStarTensor_braiding` in terms of the tensor
comparisons `δ`: `Lf^* β_{K, M} ≫ δ_{M, K} = δ_{K, M} ≫ β_{Lf^* K, Lf^* M}`. -/
lemma leftDerivedUpperStar_map_braiding_hom_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K M).hom ≫
        δ L((f)^*⟦Λ⟧) M K =
      δ L((f)^*⟦Λ⟧) K M ≫ (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _)
        (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj M)).hom :=
  leftDerivedUpperStarTensor_braiding Λ f K M

end Ambient

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The tensor comparison of the derived pullback of bounded constructible complexes is the
tensor comparison of the ambient derived pullback. -/
lemma boundedConstructibleUpperStar_δ_hom (K M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M).hom =
      δ L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) K.obj M.obj :=
  ObjectProperty.monoidalLift_δ_hom _ _ K M

/-- `ProEtale.CondensedRing.boundedConstructibleUpperStar_δ_hom` with the ambient tensor
comparison written as `ProEtale.CondensedRing.leftDerivedUpperStarTensor`. -/
lemma δ_boundedConstructibleUpperStar_hom (K M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M).hom =
      ((leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj ℓ) f.left).app K.obj).app M.obj :=
  (boundedConstructibleUpperStar_δ_hom ℓ f K M).trans rfl

/-- **The composition isomorphism of the derived pullbacks of bounded constructible complexes is
monoidal**: it commutes with the tensor comparisons. -/
lemma boundedConstructibleUpperStarComp_hom_app_tensor_δ (K M :
    Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)) K M ≫
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app M) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app (K ⊗ M) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (δ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) K M) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) _ _ := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStar_δ_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    ObjectProperty.tensorHom_hom']
  have key := δ_leftDerivedUpperStar_comp_of_eq (Profinite.padicAlgClRingObj ℓ) f.left g.left
      (Over.comp_left _ _ _ f g) K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

variable (X) in
/-- **The identity isomorphism of the derived pullback of bounded constructible complexes is
monoidal**: `L(𝟙 X)^*(K ⊗ M) ⟶ L(𝟙 X)^* K ⊗ L(𝟙 X)^* M ⟶ K ⊗ M` is the identity isomorphism. -/
lemma boundedConstructibleUpperStarId_hom_app_tensor_δ (K M :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)) K M ≫
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app M) =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app (K ⊗ M) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_δ_hom,
    boundedConstructibleUpperStarId_hom_app_hom, ObjectProperty.tensorHom_hom']
  have key := δ_leftDerivedUpperStar_id_of_eq (Profinite.padicAlgClRingObj ℓ)
      (Over.id_left X) K.obj M.obj
  simp only [eqToHom_comp_of_self] at key
  exact key

section Braided

attribute [local instance] boundedConstructibleBraiding

omit [IsSeparated X.hom] in
lemma boundedConstructible_braiding_hom_hom (K M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (β_ K M).hom.hom =
      (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K.obj M.obj).hom :=
  @ObjectProperty.fullBraidedSubcategory_braiding_hom_hom _ _ _ _ _
    (DerivedCategory.braidedCategory' _) K M

/-- **The derived pullback of bounded constructible complexes is braided** for the Koszul
braidings: `Lf^* β_{K, M} ≫ δ_{M, K} = δ_{K, M} ≫ β_{Lf^* K, Lf^* M}`. -/
lemma boundedConstructibleUpperStar_map_braiding_hom_δ (K M :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (β_ K M).hom ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) M K =
      δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) K M ≫
        (β_ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K)
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)).hom := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_δ_hom,
    boundedConstructibleUpperStar_map_hom, boundedConstructible_braiding_hom_hom]
  exact leftDerivedUpperStar_map_braiding_hom_δ (Profinite.padicAlgClRingObj ℓ) f.left K.obj M.obj

end Braided

end AlgebraicGeometry.ProEtale.CondensedRing
