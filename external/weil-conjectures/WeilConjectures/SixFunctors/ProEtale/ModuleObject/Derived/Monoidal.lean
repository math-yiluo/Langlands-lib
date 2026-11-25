/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!

# The monoidal structure of the derived pullback on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧) : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is strong monoidal for
the derived tensor products `- ⊗ᴸ_{Λ} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`:
```
m_{K,L} : Lf^* (K ⊗ᴸ_{Λ_Y} L) ≅ Lf^* K ⊗ᴸ_{Λ_X} Lf^* L,    Lf^* Λ_Y ≅ Λ_X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

The pullback `f^*` of module objects over `Λ` is strong monoidal for the relative tensor products
(`ProEtale.CondensedRing.monoidal_upperStar`), with comparison isomorphisms
`μ : f^* M ⊗_{Λ_X} f^* N ≅ f^* (M ⊗_{Λ_Y} N)`. The comparison `m` is constructed from `μ`
(`ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`) in three steps:

1. **Complexes.** For complexes `A` and `B` of module objects over `Λ_Y`, `μ` applied degreewise
   gives a map of complexes `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` for the total tensor product of
   complexes (`ProEtale.CondensedRing.upperStarTensorComplexHom`): on the summand
   `f^* A^p ⊗ f^* B^q` of degree `n = p + q` it is `μ` followed by the inclusion of
   `f^* (A^p ⊗ B^q)` into `f^* ((A ⊗ B)^n)`.
2. **Homotopy category.** Composing with the lax structure `Qh A' ⊗ᴸ Qh B' ⟶ Qh (A' ⊗ B')` of
   the localization `Qh : K(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`, this gives a natural transformation of
   bifunctors `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` on the homotopy category of
   `Mod_{Λ_Y}` (`ProEtale.CondensedRing.upperStarTensorCounit`).
3. **Derived categories.** The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`, with the
   transformation of step 2 precomposed with the counits of `Lf^*`, is a left derived bifunctor
   of `(A, B) ↦ Qh (f^* (A ⊗ B))` (`ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`).
   The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` receives a canonical transformation to the same
   bifunctor, so the universal property of left derived bifunctors
   (`Functor.leftDerived₂Lift`) gives the comparison
   `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` (`ProEtale.CondensedRing.leftDerivedUpperStarTensor`),
   characterized by its compatibility with the counits.

The unit comparison `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso` is
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙) ≅ Qh 𝟙`: the counit of `Lf^*`, an isomorphism since `f^*` is exact,
followed by the unit comparison of `monoidal_upperStar` in degree `0`. Together with the inverse
of `m` as tensorator, it makes `Lf^*` strong monoidal
(`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`).

## Proofs

- `ProEtale.CondensedRing.upperStarTensorComplexHom_comm`: the degreewise comparison is a section
  of the comparison induced by the comonoidal structure `δ` of `f^*`, which commutes with the
  differentials and is an isomorphism; so `upperStarTensorComplexHom` is its inverse
  (`ProEtale.CondensedRing.upperStarTensorComplexHom_eq_inv`) and is natural.
- `ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor` and
  `ProEtale.CondensedRing.isIso_leftDerivedUpperStarTensor` are computed on pairs of K-flat
  complexes, `f^*` preserving K-flat complexes
  (`ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj`): on such a pair the
  counits of `Lf^*` and the lax structure of `Qh` are isomorphisms.
- The coherences of `monoidal_leftDerivedUpperStar` are those of the oplax monoidal structure
  `ProEtale.CondensedRing.leftDerivedUpperStarOplaxMonoidal` with comonoidal structure `m`,
  obtained from `CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'` by checking them on
  K-flat complexes; its counit is `leftDerivedUpperStarUnitIso`
  (`ProEtale.CondensedRing.leftDerivedUpperStarOplaxMonoidal_η`).

## Main definitions

- `ProEtale.CondensedRing.leftDerivedUpperStarTensor`: the comparison
  `Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L`, as a natural transformation of bifunctors.
- `ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`: the comparison isomorphism.
- `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`: the unit comparison `Lf^* 𝟙 ≅ 𝟙`.
- `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`: the strong monoidal structure on `Lf^*`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Instances

Direct instances for complexes of module objects over `Λ_Z`. -/

omit [IsCommMonObj Λ] in
private lemma hasColimitsOfShape_monoidalModule (Z : Scheme.{u})
    (J : Type) [Category.{0} J] :
    HasColimitsOfShape J
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  have := Mod.hasColimitsOfSize (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (R := condensedRingObj Λ Z)
  inferInstance

private lemma preservesColimitsOfSize_tensorLeft_monoidalModule (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance

private lemma preservesColimitsOfSize_tensorRight_monoidalModule (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := inferInstance

private lemma hasTensor_gradedModule (Z : Scheme.{u})
    (A B : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasTensor A B := by
  have := hasColimitsOfShape_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ Z
  infer_instance

private lemma hasTensor₄ObjExt_gradedModule (Z : Scheme.{u})
    (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasTensor₄ObjExt A B C D := by
  have := hasColimitsOfShape_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ Z
  infer_instance

private lemma hasGoodTensor₁₂Tensor_gradedModule (Z : Scheme.{u})
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  have := hasColimitsOfShape_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ Z
  infer_instance

private lemma hasGoodTensorTensor₂₃_gradedModule (Z : Scheme.{u})
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  have := hasColimitsOfShape_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ Z
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ Z
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
instance hasTensor_cochainComplex (Z : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    HomologicalComplex.HasTensor A B :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategoryStruct_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategoryStruct
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategory_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategory
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

/-! ### K-flatness of pullbacks -/

-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
/-- The K-flat complexes of module objects over `Λ_Z` form a left derivability structure for the
quasi-isomorphisms of the homotopy category. It is not an instance: it would change the instance
found for the existence of the derived pullbacks of module objects. -/
lemma isLeftDerivabilityStructure_localizerMorphismKFlat (Z : Scheme.{u}) :
    (HomotopyCategory.quasiIso
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  have (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have h₁ : HasColimitsOfShape ℤ
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₂ : HasExactColimitsOfShape ℤ
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₃ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := inferInstance
  have h₄ : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₅ (X₁ X₂ X₃ X₄ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  have h₆ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have h₇ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  infer_instance

/-- The extension of scalars along the isomorphism `α_f : f^* Λ_Y ⟶ Λ_X` is an equivalence. -/
instance isEquivalence_extendScalars_condensedPullbackHom :
    (Mod.extendScalars (condensedPullbackHom Λ f)).IsEquivalence :=
  have : (Mod.comap (asIso (condensedPullbackHom Λ f)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm.isEquivalence_functor
  Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm

/-- The pullback of module objects preserves K-flat complexes. -/
lemma kFlat_upperStar_mapHomologicalComplex_obj
    {P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj P) :=
  ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl ((f)^*⟦Λ⟧)) (.up ℤ)).app P)
    ((Mod.extendScalars (condensedPullbackHom Λ f)).kFlat_mapHomologicalComplex_obj_of_isEquivalence
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).kFlat_mapHomologicalComplex_obj P hP))

/-- The pullback of module objects preserves K-flat objects of the homotopy category. -/
lemma kFlat_upperStar_mapHomotopyCategory_obj
    {R : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj R)) :=
  ObjectProperty.prop_of_iso _ (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (.up ℤ)).app R).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (kFlat_upperStar_mapHomologicalComplex_obj Λ f hR))

/-! ### Complexes -/

/-- The degreewise comparison `(f^* A ⊗ f^* B)^n ⟶ f^* ((A ⊗ B)^n)` for complexes `A` and `B`
of module objects over `Λ_Y`: on the summand `f^* A^p ⊗ f^* B^q` with `p + q = n`, the tensorator
`μ : f^* A^p ⊗ f^* B^q ⟶ f^* (A^p ⊗ B^q)` followed by `f^*` of the inclusion of the summand. -/
noncomputable def upperStarTensorComplexHomX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).X n ⟶
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ (A.X p) (B.X q) ≫
      (f)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h)

private lemma ιTensorObj_upperStarTensorComplexHomX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj B) p q n h ≫
      upperStarTensorComplexHomX Λ f A B n =
        Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ (A.X p) (B.X q) ≫
          (f)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h) := by
  exact HomologicalComplex.ι_mapBifunctorDesc _ p q h

private lemma upperStarTensorComplexHomX_eq_mapCochainComplexμIso
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    upperStarTensorComplexHomX Λ f A B n =
      ((f)^*⟦Λ⟧.mapCochainComplexμIso A B).hom.f n := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  exact (ιTensorObj_upperStarTensorComplexHomX Λ f A B p q n h).trans
    ((f)^*⟦Λ⟧.ιTensorObj_mapCochainComplexμIso_hom_f A B p q n h).symm

/-- The degreewise comparison `upperStarTensorComplexHomX` is a section of the comparison
`f^* ((A ⊗ B)^n) ⟶ (f^* A ⊗ f^* B)^n` induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHomX_comp_mapBifunctorComparisonX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    upperStarTensorComplexHomX Λ f A B n ≫
      (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B).f n =
      𝟙 _ := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  rw [upperStarTensorComplexHomX_eq_mapCochainComplexμIso]
  exact congrArg (fun φ ↦ φ.f n) ((f)^*⟦Λ⟧.mapCochainComplexμIso A B).hom_inv_id

/-- The degreewise comparisons `upperStarTensorComplexHomX` commute with the differentials. -/
lemma upperStarTensorComplexHom_comm
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n n' : ℤ)
    (_ : (ComplexShape.up ℤ).Rel n n') :
    upperStarTensorComplexHomX Λ f A B n ≫
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).d n n' =
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).d n n' ≫
        upperStarTensorComplexHomX Λ f A B n' := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  have hc := HomologicalComplex.Hom.comm
    (HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧)
      (.up ℤ) A B) n n'
  have hX := upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B
  simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app] at hX
  rw [← cancel_mono ((HomologicalComplex.mapBifunctorComparison
      (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) A B).f n'), Category.assoc,
    Category.assoc,
    hX, Category.comp_id]
  exact (congrArg (upperStarTensorComplexHomX Λ f A B n ≫ ·) hc).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hX n)).trans (Category.id_comp _)))

/-- The comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes of module objects, induced
degreewise by the tensorator of the strong monoidal pullback `f^*`. -/
noncomputable def upperStarTensorComplexHom
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ⟶
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B) where
  f n := upperStarTensorComplexHomX Λ f A B n
  comm' n n' h := upperStarTensorComplexHom_comm Λ f A B n n' h

/-- The comparison `upperStarTensorComplexHom` is the inverse of the comparison
`f^* (A ⊗ B) ⟶ f^* A ⊗ f^* B` induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHom_eq_inv
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B =
      inv (HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧)
        (.up ℤ) A B) := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  refine (IsIso.inv_eq_of_inv_hom_id (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)).symm
  exact upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B n

/-- The comparison `upperStarTensorComplexHom` is natural in both complexes. -/
lemma upperStarTensorComplexHom_naturality
    {A A' B B' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ⊗ₘ
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≫
        upperStarTensorComplexHom Λ f A' B' =
      upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ ⊗ₘ ψ) := by
  rw [upperStarTensorComplexHom_eq_inv, upperStarTensorComplexHom_eq_inv, IsIso.comp_inv_eq,
    Category.assoc, IsIso.eq_inv_comp]
  exact (HomologicalComplex.mapBifunctorComparison_naturality
    (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) φ ψ).symm

/-! ### The homotopy category -/

/-- The bifunctor `(A, B) ↦ Qh (f^* (A ⊗ B))` on the homotopy category of complexes of module
objects over `Λ_Y`, of which both sides of the comparison are left derived bifunctors. -/
noncomputable def upperStarTensorTarget :
    HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _ ⋙ (whiskeringRight _ _ _).obj
    ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- The naturality square of the components of `upperStarTensorCounit`, on complexes. -/
lemma upperStarTensorCounit_naturality_aux
    {A A' B B' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) ⊗ₘ
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ))) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A'))
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B')) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A' B')) =
    Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A B)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ ⊗ₘ ψ))) := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  have key : ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ⊗ₘ
      (HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ⊗ₘ
          ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Functor.map_comp]
    rfl
  rw [Functor.LaxMonoidal.μ_natural_assoc, key, ← DerivedCategory.Qh.map_comp,
    ← Functor.map_comp, upperStarTensorComplexHom_naturality, Functor.map_comp,
    DerivedCategory.Qh.map_comp]

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The transformation `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` of bifunctors on the
homotopy category of `Mod_{Λ_Y}`: the lax structure of `Qh` followed by `Qh` of the comparison
`upperStarTensorComplexHom`. -/
noncomputable def upperStarTensorCounit :
    (((whiskeringLeft₂ _).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        (curriedTensor _) ⟶
      upperStarTensorTarget Λ f where
  app A :=
    { app B := Functor.LaxMonoidal.μ DerivedCategory.Qh
          (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj B) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as))
      naturality B B' ψ := by
        obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
        obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
        obtain ⟨B', rfl⟩ := B'.quotient_obj_surjective
        obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
        have h := upperStarTensorCounit_naturality_aux Λ f (𝟙 A) ψ
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom,
          MonoidalCategory.id_tensorHom] at h
        rw [Category.assoc]
        exact h }
  naturality A A' φ := by
    ext B
    obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
    obtain ⟨A', rfl⟩ := A'.quotient_obj_surjective
    obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    have h := upperStarTensorCounit_naturality_aux Λ f φ (𝟙 B)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at h
    rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc]
    exact h

/-! ### Derived categories -/

/-- The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorRight :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  (((whiskeringLeft₂ _).obj L((f)^*⟦Λ⟧)).obj L((f)^*⟦Λ⟧)).obj (curriedTensor _)

/-- The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorLeft :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _ ⋙ (whiskeringRight _ _ _).obj L((f)^*⟦Λ⟧)

/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -`: the counits
`Qh ⋙ Lf^* ⟶ f^* ⋙ Qh` of the derived pullback in both variables, followed by
`upperStarTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorRightCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorRight Λ f) ⟶
      upperStarTensorTarget Λ f :=
  (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map (𝟙 _) ≫
    whiskeringLeft₂Equiv.symm
      (whiskeringLeft₂Equiv (𝟙 _) ≫ whiskerRight
        (NatTrans.prod (f)^*⟦Λ⟧.leftDerivedFunctorCounit (f)^*⟦Λ⟧.leftDerivedFunctorCounit)
          (uncurry.obj (curriedTensor _)) ≫ whiskeringLeft₂Equiv (upperStarTensorCounit Λ f))

/-- The comparison `f^* A ⊗ f^* B ⟶ f^*(A ⊗ B)` of complexes is a section of the comparison
induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHom_δ
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B =
      𝟙 _ := by
  exact HomologicalComplex.hom_ext _ _
    (upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B)

open DerivedCategory in
/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -` on objects of the homotopy category. -/
lemma leftDerivedUpperStarTensorRightCounit_app_app (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensorRightCounit Λ f).app A).app B =
      ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B) ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A.as B.as)) := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  dsimp only [leftDerivedUpperStarTensorRightCounit, NatTrans.comp_app]
  erw [Category.id_comp]
  refine (?_ : _ = 𝟙 _ ≫ (((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B)) ≫
        (Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as)))).trans ?_
  · rfl
  · exact (Category.id_comp _).trans (Category.assoc _ _ _)

/-- On K-flat complexes, the counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -` is an isomorphism. -/
lemma isIso_leftDerivedUpperStarTensorRightCounit_app_app
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj A))
    (hB : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj B)) :
    IsIso (((leftDerivedUpperStarTensorRightCounit Λ f).app
      ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B)) := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  have hB' := (HomotopyCategory.kFlat_quotient_obj_iff B).1 hB
  rw [leftDerivedUpperStarTensorRightCounit_app_app]
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hA
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hB
  have h₃ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B))) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f hB')
  have h₄ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f A B))) := by
    rw [upperStarTensorComplexHom_eq_inv]
    infer_instance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h₃ h₄))

/-- The bifunctor `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor of `(A, B) ↦ Qh (f^* (A ⊗ B))`,
for the counit `leftDerivedUpperStarTensorRightCounit`. See the module docstring. -/
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Y
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  obtain ⟨A, hA⟩ := X₁
  obtain ⟨B, hB⟩ := X₂
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
  exact isIso_leftDerivedUpperStarTensorRightCounit_app_app Λ f A B hA hB

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The counit of the bifunctor `Lf^* (- ⊗ᴸ -)`: `Lf^*` of the lax structure
`Qh A ⊗ᴸ Qh B ⟶ Qh (A ⊗ B)` of the localization, followed by the counit
`Lf^* (Qh (A ⊗ B)) ⟶ Qh (f^* (A ⊗ B))` of the derived pullback. -/
noncomputable def leftDerivedUpperStarTensorLeftCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorLeft Λ f) ⟶
      upperStarTensorTarget Λ f where
  app A :=
    { app B := L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B)
      naturality B B' ψ := by
        have h₁ := Functor.LaxMonoidal.μ_natural_right DerivedCategory.Qh A ψ
        have h₂ := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (A ◁ ψ)
        dsimp only [Functor.comp_map] at h₂
        change L((f)^*⟦Λ⟧).map (DerivedCategory.Qh.obj A ◁ DerivedCategory.Qh.map ψ) ≫
            L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B') ≫ _ =
          (L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫ _) ≫
            DerivedCategory.Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map (A ◁ ψ))
        rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc, h₂] }
  naturality A A' φ := by
    ext B
    have h₁ := Functor.LaxMonoidal.μ_natural_left DerivedCategory.Qh φ B
    have h₂ := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (φ ▷ B)
    dsimp only [Functor.comp_map] at h₂
    change L((f)^*⟦Λ⟧).map (DerivedCategory.Qh.map φ ▷ DerivedCategory.Qh.obj B) ≫
        L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A' B) ≫ _ =
      (L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫ _) ≫
        DerivedCategory.Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map (φ ▷ B))
    rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc, h₂]

/-- The comparison `m_{K,L} : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` of the derived pullback with the
derived tensor product, as a natural transformation of bifunctors on `D(Mod_{Λ_Y})`: the
morphism to the left derived bifunctor `Lf^* - ⊗ᴸ Lf^* -` induced by the counit
`leftDerivedUpperStarTensorLeftCounit` (`Functor.leftDerived₂Lift`). -/
noncomputable def leftDerivedUpperStarTensor :
    leftDerivedUpperStarTensorLeft Λ f ⟶ leftDerivedUpperStarTensorRight Λ f :=
  (leftDerivedUpperStarTensorRight Λ f).leftDerived₂Lift
    (leftDerivedUpperStarTensorRightCounit Λ f)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (leftDerivedUpperStarTensorLeft Λ f) (leftDerivedUpperStarTensorLeftCounit Λ f)

/-- The comparison `m` is compatible with the counits. -/
lemma leftDerivedUpperStarTensor_fac :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map
        (leftDerivedUpperStarTensor Λ f) ≫ leftDerivedUpperStarTensorRightCounit Λ f =
      leftDerivedUpperStarTensorLeftCounit Λ f :=
  Functor.leftDerived₂_fac _ _ _ _ _ _

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
open DerivedCategory in
/-- The defining property of the tensor comparison of `Lf^*`, in the form used by
`DerivedCategory.commShift_of_tensorLeft_fac`. -/
lemma leftDerivedUpperStarTensor_app_app_fac (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) =
      L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) := by
  have h : ((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ f).app A).app B =
      ((leftDerivedUpperStarTensorLeftCounit Λ f).app A).app B :=
    congr_app (congr_app (leftDerivedUpperStarTensor_fac Λ f) A) B
  rw [leftDerivedUpperStarTensorRightCounit_app_app] at h
  have hδ : Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f A.as B.as)) ≫
      Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) = 𝟙 _ := by
    rw [← Functor.map_comp]
    erw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app]
    rw [← Functor.map_comp, upperStarTensorComplexHom_δ]
    exact (congrArg Qh.map ((HomotopyCategory.quotient _ _).map_id _)).trans (Qh.map_id _)
  calc _ = (((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as))) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) := by
        simp only [Category.assoc]
        erw [hδ, Category.comp_id]
    _ = _ := by
        erw [h]
        exact Category.assoc _ _ _

/-- Every object of `D(Mod_{Λ_Y})` is isomorphic to the image of a K-flat complex. -/
lemma exists_kFlat_iso_Qh_obj (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ∃ P, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P ∧
      Nonempty (DerivedCategory.Qh.obj P ≅ K) := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Y
  have := Localization.essSurj (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology Y)
    Ab.{u + 1}) (condensedRingObj Λ Y))) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat)
    (DerivedCategory.Qh.objPreimage K)
  have : IsIso (DerivedCategory.Qh.map R.w) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property,
    ⟨asIso (DerivedCategory.Qh.map R.w) ≪≫ DerivedCategory.Qh.objObjPreimageIso K⟩⟩

/-- On K-flat complexes, the comparison `m` is an isomorphism: both counits are isomorphisms. -/
lemma isIso_leftDerivedUpperStarTensor_app_app_Qh_obj
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hA : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj A))
    (hB : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj B)) :
    IsIso (((leftDerivedUpperStarTensor Λ f).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj B))) := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  have := isIso_leftDerivedUpperStarTensorRightCounit_app_app Λ f A B hA hB
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient _ _).obj A)
      ((HomotopyCategory.quotient _ _).obj B)) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat ((HomotopyCategory.quotient _ _).obj A)
      ((HomotopyCategory.quotient _ _).obj B) hB
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _
    ((HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.prop_tensor hA hB)
  have hL : IsIso (((leftDerivedUpperStarTensorLeftCounit Λ f).app
      ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B)) :=
    IsIso.comp_isIso' (Functor.map_isIso L((f)^*⟦Λ⟧) (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)))
      inferInstance
  have h := congr_app (congr_app (leftDerivedUpperStarTensor_fac Λ f)
    ((HomotopyCategory.quotient _ _).obj A)) ((HomotopyCategory.quotient _ _).obj B)
  rw [NatTrans.comp_app, NatTrans.comp_app] at h
  have : IsIso ((((leftDerivedUpperStarTensor Λ f).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj A))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj B))) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ f).app
        ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B)) := by
    rw [← h] at hL
    exact hL
  exact IsIso.of_isIso_comp_right _ (((leftDerivedUpperStarTensorRightCounit Λ f).app
    ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B))

/-- The comparison `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` is an isomorphism: every object is
isomorphic to the image of a K-flat complex, on which `m` is an isomorphism
(`isIso_leftDerivedUpperStarTensor_app_app_Qh_obj`). -/
instance isIso_leftDerivedUpperStarTensor : IsIso (leftDerivedUpperStarTensor Λ f) := by
  have hQ (P Q : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ))
      (hP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P)
      (hQ : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat Q) :
      IsIso (((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj P)).app
        (DerivedCategory.Qh.obj Q)) := by
    obtain ⟨P, rfl⟩ := P.quotient_obj_surjective
    obtain ⟨Q, rfl⟩ := Q.quotient_obj_surjective
    exact isIso_leftDerivedUpperStarTensor_app_app_Qh_obj Λ f P Q hP hQ
  have (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      IsIso ((leftDerivedUpperStarTensor Λ f).app K) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso_Qh_obj Λ K
    have (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
        IsIso (((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj P)).app M) := by
      obtain ⟨Q, hQ', ⟨e'⟩⟩ := exists_kFlat_iso_Qh_obj Λ M
      have := hQ P Q hP hQ'
      exact NatTrans.isIso_app_of_iso _ e'.symm
    have : IsIso ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj P)) :=
      NatIso.isIso_of_isIso_app _
    exact NatTrans.isIso_app_of_iso _ e.symm
  exact NatIso.isIso_of_isIso_app _

/-- The comparison isomorphism `m_{K,L} : Lf^* (K ⊗ᴸ L) ≅ Lf^* K ⊗ᴸ Lf^* L` of the derived
pullback with the derived tensor product. -/
noncomputable def leftDerivedUpperStarTensorIso :
    leftDerivedUpperStarTensorLeft Λ f ≅ leftDerivedUpperStarTensorRight Λ f :=
  asIso (leftDerivedUpperStarTensor Λ f)

/-! ### The monoidal structure -/

/-- The derived pullback of the tensor unit `Λ_Y` is the tensor unit `Λ_X`: the counit
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙)` of the derived pullback of the exact functor `f^*`, followed by the
unit comparison `f^* 𝟙 ≅ 𝟙` of the strong monoidal pullback of module objects, in degree `0`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦Λ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (f)^*⟦Λ⟧
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso (f)^*⟦Λ⟧).symm))

/-- The compatibility of the comparison `m` with the comonoidal structure of `f^*` on the
homotopy category, in the form of the hypothesis of
`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'`. -/
lemma leftDerivedUpperStarTensor_laxSquare (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Qh.obj A)).app
        (DerivedCategory.Qh.obj B) ≫
      ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ⊗ₘ (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) =
      L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B) ≫
        DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.δ ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)) A B) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  exact leftDerivedUpperStarTensor_app_app_fac Λ f A B

/-- The oplax monoidal structure on `Lf^*` whose comonoidal structure is the comparison `m`
(`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'`): its coherences are checked on K-flat
complexes, whose pullbacks are K-flat. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarOplaxMonoidal : L((f)^*⟦Λ⟧).OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  Functor.OplaxMonoidal.ofLaxSquare' (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
    (F := (f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)) (leftDerivedUpperStarTensor Λ f)
    (fun a ↦ (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app a)
    (fun _ _ g ↦ (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality g)
    (leftDerivedUpperStarTensor_laxSquare Λ f) (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
    (exists_kFlat_iso_Qh_obj Λ)
    (fun a ha ↦ (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' a ha)
    (fun x b hb ↦ by
      obtain ⟨B, rfl⟩ := b.quotient_obj_surjective
      exact isIso_μNatTrans_Qh_app_app_of_kFlat x _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f
        ((HomotopyCategory.kFlat_quotient_obj_iff B).1 hb)))

/-- The counit of the oplax monoidal structure `leftDerivedUpperStarOplaxMonoidal` is the unit
comparison `leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStarOplaxMonoidal_η :
    letI := leftDerivedUpperStarOplaxMonoidal Λ f
    Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧) = (leftDerivedUpperStarUnitIso Λ f).hom := by
  have := hasColimitsOfShape_monoidalModule Λ
  have := preservesColimitsOfSize_tensorLeft_monoidalModule Λ
  have := preservesColimitsOfSize_tensorRight_monoidalModule Λ
  have := hasTensor_gradedModule Λ
  have := hasTensor₄ObjExt_gradedModule Λ
  have := hasGoodTensor₁₂Tensor_gradedModule Λ
  have := hasGoodTensorTensor₂₃_gradedModule Λ
  let := leftDerivedUpperStarOplaxMonoidal Λ f
  have hY : Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj Λ Y))) = 𝟙 _ := rfl
  have hX : Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u + 1}) (condensedRingObj Λ X))) = 𝟙 _ := rfl
  have := DerivedCategory.isIso_ε_Qh
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  change L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map (Functor.OplaxMonoidal.η ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ))) ≫
          CategoryTheory.inv (Functor.LaxMonoidal.ε DerivedCategory.Qh) = _
  simp only [hY, hX, CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp]
  rw [Functor.mapHomotopyCategory_η, Functor.mapCochainComplex_η]
  erw [Category.comp_id]
  rfl

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over `Λ` is
strong monoidal for the derived tensor products, with tensorator the inverse of
`leftDerivedUpperStarTensorIso` and unit comparison `leftDerivedUpperStarUnitIso`. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦Λ⟧).Monoidal :=
  letI := leftDerivedUpperStarOplaxMonoidal Λ f
  haveI (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      IsIso (Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) K L) :=
    inferInstanceAs (IsIso (((leftDerivedUpperStarTensor Λ f).app K).app L))
  haveI : IsIso (Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧)) := by
    rw [leftDerivedUpperStarOplaxMonoidal_η]
    infer_instance
  have hμ (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      (((leftDerivedUpperStarTensorIso Λ f).app K).app L).symm =
        (asIso (Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) K L)).symm := by
    ext
    exact (IsIso.inv_eq_of_hom_inv_id
      (((leftDerivedUpperStarTensorIso Λ f).app K).app L).hom_inv_id).symm
  have hε : (leftDerivedUpperStarUnitIso Λ f).symm =
      (asIso (Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧))).symm := by
    ext
    refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
    rw [leftDerivedUpperStarOplaxMonoidal_η, Iso.symm_hom, Iso.hom_inv_id]
  Functor.CoreMonoidal.toMonoidal
    { εIso := (leftDerivedUpperStarUnitIso Λ f).symm
      μIso K L := (((leftDerivedUpperStarTensorIso Λ f).app K).app L).symm
      μIso_hom_natural_left φ L :=
        NatTrans.congr_app ((leftDerivedUpperStarTensorIso Λ f).inv.naturality φ) L
      μIso_hom_natural_right K ψ :=
        ((leftDerivedUpperStarTensorIso Λ f).inv.app K).naturality ψ
      associativity K L M := by
        rw [hμ, hμ, hμ, hμ]
        exact (Functor.CoreMonoidal.ofOplaxMonoidal L((f)^*⟦Λ⟧)).associativity K L M
      left_unitality K := by
        rw [hμ, hε]
        exact (Functor.CoreMonoidal.ofOplaxMonoidal L((f)^*⟦Λ⟧)).left_unitality K
      right_unitality K := by
        rw [hμ, hε]
        exact (Functor.CoreMonoidal.ofOplaxMonoidal L((f)^*⟦Λ⟧)).right_unitality K }

end AlgebraicGeometry.ProEtale.CondensedRing
