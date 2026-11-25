/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ExactFunctorShiftMap
public import WeilConjectures.TraceFormula.WeilDistTriang
public import WeilConjectures.WeilObject.BoundedConstructible.Homology

/-!

# The connecting morphisms of the homology sequence of a triangle of Weil objects

Let `A ⟶ B ⟶ C ⟶ A[1]` be a triangle of Weil objects of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an automorphism `e`
whose connecting morphism `δ` commutes with the Frobenius structures, as in
`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang`. The connecting morphisms
`Hʲ(C) ⟶ Hʲ'(A)` (`j' = j + 1`) of the long exact homology sequence, computed in the ambient
derived category, are morphisms of Weil sheaves
(`ProEtale.CondensedRing.WeilBoundedConstructible.homologyδ`): the structure isomorphisms of the
homology sheaves are built from the commutation `Functor.mapDerivedCategoryHomologyFunctorIso`
of the exact functor `e^*` with homology, which is compatible with the connecting morphisms
(`CategoryTheory.Functor.map_shiftMap_homologyFunctor_comp_mapDerivedCategoryHomologyFunctorIso`),
and from the identification of the derived pullback with the levelwise pullback, which commutes
with the shifts.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyδ`: the connecting morphism
  `Hʲ(C) ⟶ Hʲ'(A)` as a morphism of Weil sheaves.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The components of the Frobenius comparison `Hⁿ ⋙ e^* ≅ Le^* ⋙ Hⁿ` of the homology sheaves:
the commutation of `e^*` with homology, followed by the identification of the derived pullback
with the levelwise pullback and the compatibility of `Le^*` with the inclusion of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. Unlike `weilHomologyComparison_hom_app`, the compatibility isomorphism is kept
explicit, as it occurs in `WeilBoundedConstructible.IsDistTriang`. -/
lemma weilHomologyComparison_hom_app_compatibility_inv (e : X ≅ X) (n : ℤ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilHomologyComparison ℓ e n).hom.app K =
      ((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapDerivedCategoryHomologyFunctorIso
          n).hom.app ((boundedConstructible _).ι.obj K) ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            e.hom.left).inv.app ((boundedConstructible _).ι.obj K)) ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
            e.hom).inv.app K) := by
  simp [weilHomologyComparison]

/-- The structure isomorphism of the `n`-th homology sheaf of a Weil object `K` is
`e^* Hⁿ(K) ≅ Hⁿ(Le^* K) --Hⁿ(φ_K)--> Hⁿ(K)`. -/
lemma WeilBoundedConstructible.homologyFunctor_obj_str_hom (e : X ≅ X) (n : ℤ)
    (K : WeilBoundedConstructible ℓ e.hom) :
    ((WeilBoundedConstructible.homologyFunctor ℓ e n).obj K).str.hom =
      (weilHomologyComparison ℓ e n).hom.app K.carrier ≫
        (DerivedCategory.homologyFunctor _ n).map ((boundedConstructible _).ι.map K.str.hom) :=
  rfl

section Connecting

variable {e : X ≅ X} {A C : WeilBoundedConstructible ℓ e.hom}
  (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
      C.carrier ⟶ (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          A.carrier))

/-- If the connecting morphism `δ : C ⟶ A[1]` commutes with the Frobenius structures, so does
its image under the levelwise pullback `D(e^*)`: through the identification
`L(e^*) ≅ D(e^*)`, which commutes with the shifts, `D(e^*) δ` followed by the structure
isomorphism of `A[1]` is the structure isomorphism of `C` followed by `δ`. -/
lemma WeilBoundedConstructible.mapDerivedCategory_map_comp_str_eq
    (hδ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          C.str.hom ≫ δ =
        connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            L((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
            (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
            δ ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
              A.str.hom)) :
    D((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map δ ≫
        (D((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso (1 : ℤ)).hom.app _ ≫
        (shiftFunctor _ (1 : ℤ)).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            e.hom.left).inv.app _ ≫
          (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
            e.hom).inv.app A.carrier ≫
          (boundedConstructible _).ι.map A.str.hom) =
      (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            e.hom.left).inv.app _ ≫
          (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
            e.hom).inv.app C.carrier ≫
          (boundedConstructible _).ι.map C.str.hom ≫ δ := by
  rw [hδ]
  simp only [connectingOfIso, Category.assoc, Iso.inv_hom_id_app_assoc]
  have h₁ := (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
    e.hom.left).inv.naturality δ
  have h₂ := NatTrans.shift_app_comm (leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.padicAlgClRingObj ℓ) e.hom.left).symm.hom (1 : ℤ)
    ((boundedConstructible _).ι.obj A.carrier)
  simp only [Iso.symm_hom] at h₂
  have h₃ := h₂ =≫ (shiftFunctor _ (1 : ℤ)).map
    ((boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
      e.hom).inv.app A.carrier ≫ (boundedConstructible _).ι.map A.str.hom)
  have h₄ := D((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map δ ≫= h₃
  simp only [Category.assoc, reassoc_of% h₁] at h₄
  simp only [Functor.map_comp] at h₄ ⊢
  exact h₄

/-- If the connecting morphism `δ : C ⟶ A[1]` commutes with the Frobenius structures, the
induced morphism `Hʲ(C) ⟶ Hʲ'(A)` in homology commutes with the structure isomorphisms of the
Weil homology sheaves. -/
lemma WeilBoundedConstructible.upperStar_map_shiftMap_comp_str_hom
    (hδ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          C.str.hom ≫ δ =
        connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            L((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
            (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
            δ ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
              A.str.hom))
    (j j' : ℤ) (h : 1 + j = j') :
    (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((DerivedCategory.homologyFunctor _ 0).shiftMap δ j j' h) ≫
        ((WeilBoundedConstructible.homologyFunctor ℓ e j').obj A).str.hom =
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj C).str.hom ≫
        (DerivedCategory.homologyFunctor _ 0).shiftMap δ j j' h := by
  rw [WeilBoundedConstructible.homologyFunctor_obj_str_hom,
    WeilBoundedConstructible.homologyFunctor_obj_str_hom,
    weilHomologyComparison_hom_app_compatibility_inv,
    weilHomologyComparison_hom_app_compatibility_inv]
  have h₁ := Functor.map_shiftMap_homologyFunctor_comp_mapDerivedCategoryHomologyFunctorIso
    (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ δ j j' h
  simp only [Category.assoc]
  refine (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans (Category.assoc _ _ _)) |>.trans ?_
  refine congrArg (_ ≫ ·) ?_
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  refine ((DerivedCategory.homologyFunctor _ 0).shiftMap_comp _ _ j j' h).symm.trans
    (Eq.trans ?_ ((DerivedCategory.homologyFunctor _ 0).shiftMap_comp' _ _ j j' h))
  refine congrArg (fun t ↦ (DerivedCategory.homologyFunctor _ 0).shiftMap t j j' h) ?_
  simp only [Category.assoc]
  exact WeilBoundedConstructible.mapDerivedCategory_map_comp_str_eq ℓ δ hδ

/-- The connecting morphism `Hʲ(C) ⟶ Hʲ'(A)` (`j' = j + 1`) of the homology sequence of a
triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects, as a morphism of Weil sheaves, when the
connecting morphism `δ` of the triangle commutes with the Frobenius structures. -/
noncomputable def WeilBoundedConstructible.homologyδ
    (hδ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          C.str.hom ≫ δ =
        connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            L((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
            (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
            δ ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
              A.str.hom))
    (j j' : ℤ) (h : 1 + j = j') :
    (WeilBoundedConstructible.homologyFunctor ℓ e j).obj C ⟶
      (WeilBoundedConstructible.homologyFunctor ℓ e j').obj A :=
  ObjectProperty.homMk
    { f := (DerivedCategory.homologyFunctor _ 0).shiftMap δ j j' h
      h := WeilBoundedConstructible.upperStar_map_shiftMap_comp_str_hom ℓ δ hδ j j' h }

end Connecting

end AlgebraicGeometry.ProEtale.CondensedRing
