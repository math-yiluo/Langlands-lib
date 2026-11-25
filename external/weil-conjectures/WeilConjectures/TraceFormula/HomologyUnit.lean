/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.TraceFormula.Main
public import WeilConjectures.WeilObject.BoundedConstructible.Homology

/-!
# The `0`-th homology sheaf of the canonical Weil unit

Let `ℓ` be a prime, `X` a separated scheme of finite type over a field `k` with an automorphism
`e : X ≅ X` over `Spec k`, and write `e^* = (e.hom.left)^*⟦ℚ̲̄_ℓ⟧`. The canonical Weil unit
`ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ProEtale.CondensedRing.WeilBoundedConstructible.unit`) is the unit
module object placed in degree `0`, with structure isomorphism the inverse of the unit comparison
of the derived pullback `Le^*`. This file computes the structure isomorphism of its `0`-th
homology sheaf `H⁰(ℚ̲̄_ℓ,X)`: under the identification `H⁰(ℚ̲̄_ℓ[0]) ≅ ℚ̲̄_ℓ`, it is the inverse of
the unit comparison `ε : ℚ̲̄_ℓ ≅ e^* ℚ̲̄_ℓ` of the monoidal functor `e^*`.

The computation is reduced to a general statement about an exact functor `F` between abelian
categories (`DerivedCategory.mapDerivedCategoryHomologyFunctorIso_hom_app_comp_singleHom`): the
commutation `H⁰ ⋙ F ≅ D(F) ⋙ H⁰` at `A[0]`, followed by the morphism `F(A[0]) ⟶ B[0]` induced by
a morphism `φ : F A ⟶ B`, is `F(H⁰(A[0]) ≅ A) ≫ φ`.

## Main results

- `DerivedCategory.homologyFunctorZeroQhSingleIso`: the identification `H⁰(A[0]) ≅ A`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor_obj_unit_str_hom_comp`: the
  structure isomorphism of `H⁰(ℚ̲̄_ℓ,X)` is the inverse of the unit comparison of `e^*`.
-/

@[expose] public section

universe w w' u u' v v'

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι)
  (j : ι) [DecidableEq ι]

/-- The inverse form of `Functor.mapHomologicalComplexHomologyIso_hom_app_single`. -/
@[reassoc]
lemma mapHomologicalComplexHomologyIso_inv_app_single (A : C) :
    (F.mapHomologicalComplexHomologyIso c j).inv.app ((HomologicalComplex.single C c j).obj A) ≫
        HomologicalComplex.homologyMap
          ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app A) j ≫
        (HomologicalComplex.homologyFunctorSingleIso D c j).hom.app (F.obj A) =
      F.map ((HomologicalComplex.homologyFunctorSingleIso C c j).hom.app A) := by
  rw [← mapHomologicalComplexHomologyIso_hom_app_single, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

variable (C) in
/-- The `0`-th homology of the image `Qh(A[0])` of a complex concentrated in degree `0` is
`H⁰(A[0]) ≅ A`. -/
noncomputable def homologyFunctorZeroQhSingleIso (A : C) :
    (homologyFunctor C 0).obj (Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj A))) ≅ A :=
  (homologyFunctor C 0).mapIso ((quotientCompQhIso C).app _) ≪≫
    (homologyFunctorFactors C 0).app _ ≪≫
      (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).app A

lemma homologyFunctorZeroQhSingleIso_hom (A : C) :
    (homologyFunctorZeroQhSingleIso C A).hom =
      (homologyFunctor C 0).map ((quotientCompQhIso C).hom.app _) ≫
        (homologyFunctorFactors C 0).hom.app _ ≫
          (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).hom.app A :=
  rfl

/-- For an exact functor `F`, the commutation `H⁰ ⋙ F ≅ D(F) ⋙ H⁰` at `A[0]`, followed by the
morphism `D(F)(A[0]) ⟶ B[0]` induced by `φ : F A ⟶ B`, is `F(H⁰(A[0]) ≅ A) ≫ φ` up to the
identifications `H⁰(-[0]) ≅ -`. -/
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_comp_singleHom (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {A : C} {B : D}
    (φ : F.obj A ⟶ B) :
    (F.mapDerivedCategoryHomologyFunctorIso 0).hom.app _ ≫
      (homologyFunctor D 0).map (F.mapDerivedCategoryFactorsh.hom.app _ ≫
        Qh.map (F.mapHomotopyCategorySingleHom φ)) ≫ (homologyFunctorZeroQhSingleIso D B).hom =
      F.map (homologyFunctorZeroQhSingleIso C A).hom ≫ φ := by
  have hnat := (F.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality
    ((quotientCompQhIso C).hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj A))
  have hq := quotientCompQhIso_hom_naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app A ≫
      (HomologicalComplex.single D (.up ℤ) 0).map φ)
  have hφ : HomologicalComplex.homologyMap ((HomologicalComplex.single D (.up ℤ) 0).map φ) 0 ≫
      (HomologicalComplex.homologyFunctorSingleIso D (.up ℤ) 0).hom.app B =
      (HomologicalComplex.homologyFunctorSingleIso D (.up ℤ) 0).hom.app (F.obj A) ≫ φ :=
    (HomologicalComplex.homologyFunctorSingleIso D (.up ℤ) 0).hom.naturality φ
  have hs := F.mapHomologicalComplexHomologyIso_inv_app_single (.up ℤ) 0 A
  have key : F.mapDerivedCategoryFactorsh.hom.app _ ≫ Qh.map (F.mapHomotopyCategorySingleHom φ) ≫
      (quotientCompQhIso D).hom.app _ =
      F.mapDerivedCategory.map ((quotientCompQhIso C).hom.app _) ≫
        F.mapDerivedCategoryFactors.hom.app _ ≫
          Q.map ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app A ≫
            (HomologicalComplex.single D (.up ℤ) 0).map φ) := by
    rw [Functor.mapHomotopyCategorySingleHom, F.mapDerivedCategoryFactorsh_hom_app,
      Functor.map_comp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc Qh ((F.mapHomotopyCategoryFactors _).inv.app _),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, hq]
    erw [Iso.inv_hom_id_app_assoc]
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [homologyFunctorZeroQhSingleIso_hom, homologyFunctorZeroQhSingleIso_hom,
    ← Functor.map_comp_assoc, Category.assoc, key, Functor.map_comp, Functor.map_comp,
    Category.assoc, ← reassoc_of% hnat, F.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [Category.assoc, Functor.map_comp]
  have hc := ((homologyFunctor D 0).mapIso
    (F.mapDerivedCategoryFactors.app ((HomologicalComplex.single C (.up ℤ) 0).obj A))).inv_hom_id
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hc
  rw [reassoc_of% hc, homologyFunctorFactors_hom_naturality_assoc,
    homologyFunctorFactors_hom_naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [hφ, reassoc_of% hs]

/-- A version of `DerivedCategory.mapDerivedCategoryHomologyFunctorIso_hom_app_comp_singleHom`
for a functor `LF` identified with `D(F)` by an isomorphism `β` compatible with a transformation
`α : Qh ⋙ LF ⟶ K(F) ⋙ Qh` (typically the counit of the left derived functor of `F`). -/
lemma homologyFunctor_map_comp_singleHom_of_iso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {LF : DerivedCategory C ⥤ DerivedCategory D}
    (β : LF ≅ F.mapDerivedCategory)
    (α : Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ Qh)
    (hα : Functor.whiskerLeft Qh β.hom ≫ F.mapDerivedCategoryFactorsh.hom = α) {A : C} {B : D}
    (φ : F.obj A ⟶ B) :
    ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app _ ≫
      (homologyFunctor D 0).map (β.inv.app _)) ≫
      (homologyFunctor D 0).map (α.app _ ≫ Qh.map (F.mapHomotopyCategorySingleHom φ)) ≫
        (homologyFunctorZeroQhSingleIso D B).hom =
      F.map (homologyFunctorZeroQhSingleIso C A).hom ≫ φ := by
  subst hα
  rw [Category.assoc, ← Functor.map_comp_assoc, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  exact mapDerivedCategoryHomologyFunctorIso_hom_app_comp_singleHom F φ

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The identification `L(f^*) ≅ D(f^*)` of the derived pullback with the levelwise pullback is
compatible with the counit of the left derived functor. -/
lemma leftDerivedUpperStarIsoMapDerivedCategory_hom_fac
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    Functor.whiskerLeft DerivedCategory.Qh (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ≫
      (f)^*⟦Λ⟧.mapDerivedCategoryFactorsh.hom = (f)^*⟦Λ⟧.leftDerivedFunctorCounit :=
  (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_fac

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X) (n : ℤ)

/-- The Frobenius comparison of the `n`-th homology sheaf at `K` is the commutation
`e^* Hⁿ(K) ≅ Hⁿ(D(e^*) K)` followed by the identification of `D(e^*)` with `Le^*`. -/
lemma weilHomologyComparison_hom_app (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilHomologyComparison ℓ e n).hom.app K =
      ((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapDerivedCategoryHomologyFunctorIso n).hom.app
          K.obj ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            e.hom.left).inv.app K.obj) := by
  simp [weilHomologyComparison, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- The structure isomorphism of the `n`-th homology sheaf `Hⁿ(K)` is `e^* Hⁿ(K) ≅ Hⁿ(Le^* K)`
followed by `Hⁿ(φ_K)`. -/
lemma WeilBoundedConstructible.homologyFunctor_obj_str (K : WeilBoundedConstructible ℓ e.hom) :
    ((WeilBoundedConstructible.homologyFunctor ℓ e n).obj K).str =
      (weilHomologyComparison ℓ e n).app K.carrier ≪≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ _

/-- The structure isomorphism of the canonical Weil unit is the inverse of the unit comparison
`ε : ℚ̲̄_ℓ,X ≅ Le^* ℚ̲̄_ℓ,X`, computed on the ambient derived category by
`ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`. -/
lemma WeilBoundedConstructible.unit_str_hom_hom :
    (WeilBoundedConstructible.unit ℓ e.hom).str.hom.hom =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) e.hom.left).hom := by
  rfl

/-- The structure isomorphism `e^* H⁰(ℚ̲̄_ℓ,X) ≅ H⁰(ℚ̲̄_ℓ,X)` of the `0`-th homology sheaf of the
canonical Weil unit is, under the identification `H⁰(ℚ̲̄_ℓ[0]) ≅ ℚ̲̄_ℓ`, the inverse of the unit
comparison `ε : ℚ̲̄_ℓ ≅ e^* ℚ̲̄_ℓ` of the monoidal functor `e^*`. -/
lemma WeilBoundedConstructible.homologyFunctor_obj_unit_str_hom_comp :
    ((WeilBoundedConstructible.homologyFunctor ℓ e 0).obj
        (WeilBoundedConstructible.unit ℓ e.hom)).str.hom ≫
      (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _)).hom =
    (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _)).hom ≫
      (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv := by
  rw [WeilBoundedConstructible.homologyFunctor_obj_str, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, ObjectProperty.ι_map, WeilBoundedConstructible.unit_str_hom_hom,
    leftDerivedUpperStarUnitIso_hom_eq, Iso.app_hom, weilHomologyComparison_hom_app]
  have h1 := DerivedCategory.homologyFunctor_map_comp_singleHom_of_iso
    (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ) e.hom.left)
  have h3 := leftDerivedUpperStarIsoMapDerivedCategory_hom_fac (Profinite.padicAlgClRingObj ℓ)
    e.hom.left
  have h4 := h1 _ h3 (A := 𝟙_ _) (B := 𝟙_ _)
  have h5 := h4 (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv
  exact h5

end AlgebraicGeometry.ProEtale.CondensedRing
