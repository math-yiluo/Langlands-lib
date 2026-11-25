/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# The essential image of the extension by zero on module objects

Let `Λ` be a commutative condensed ring and `j : U ⟶ X` an open immersion. This file shows that
the extension by zero `j_! : Mod_{Λ_U} ⥤ Mod_{Λ_X}` is fully faithful and that its essential
image, and the essential image of `Dj_!` on derived categories, contain the tensor products
`j_! K ⊗ N`. This is the input of the derived projection formula
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection`.

The argument runs as follows.

* On abelian sheaves, `j_! A ⊗ B ≅ j_!(j^* B ⊗ A)` by the projection formula, so `j_! A ⊗ B`
  lies in the essential image of `j_!`. This essential image is closed under colimits, `j_!`
  being a fully faithful left adjoint, so it contains the relative tensor product
  `j_! K ⊗_{Λ_X} N`, a coequalizer of such objects.
* A module object whose underlying sheaf lies in the essential image of `j_!` on sheaves lies in
  the essential image of `j_!` on module objects (`Adjunction.mapModLeft_essImage_of_essImage`),
  `j_!` on module objects being the linearization of `j_!` on sheaves after the restriction of
  scalars along the isomorphism `α_j`.
* The terms of the tensor product `j_! K ⊗ N` of complexes are coproducts of objects
  `j_! K^p ⊗_{Λ_X} N^q`, hence lie in the essential image of `j_!`; so the counit
  `j_! j^* (j_! K ⊗ N) ⟶ j_! K ⊗ N` is an isomorphism of complexes.
* Writing `N` as a K-flat complex, the derived tensor product `Dj_! K ⊗ᴸ N` is computed by the
  tensor product of complexes, hence lies in the essential image of `Dj_!`.

## Main results

- `ProEtale.CondensedRing.fullyFaithfulOpenImmersionLowerShriek`: `j_!` on module objects is
  fully faithful.
- `ProEtale.CondensedRing.tensorObj_mem_essImage_openImmersionLowerShriek`: `j_! K ⊗_{Λ_X} N`
  lies in the essential image of `j_!`.
- `ProEtale.CondensedRing.tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek`:
  `Dj_! K ⊗ᴸ N` lies in the essential image of `Dj_!`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-! ### The extension by zero on module objects is fully faithful -/

/-- The extension by zero `j_!` on module objects along an open immersion is fully faithful:
it is the restriction of scalars along the isomorphism `α_j`, an equivalence, followed by the
linearization of the fully faithful extension by zero on sheaves. -/
noncomputable def fullyFaithfulOpenImmersionLowerShriek : (j)_!open⟦Λ⟧.FullyFaithful :=
  (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).fullyFaithfulMapModLeft

instance full_openImmersionLowerShriek : (j)_!open⟦Λ⟧.Full :=
  (fullyFaithfulOpenImmersionLowerShriek Λ j).full

instance faithful_openImmersionLowerShriek : (j)_!open⟦Λ⟧.Faithful :=
  (fullyFaithfulOpenImmersionLowerShriek Λ j).faithful

/-! ### Objects in the essential image of the extension by zero -/

omit [IsCommMonObj Λ] in
/-- A module object over `Λ_X` whose underlying sheaf lies in the essential image of the
extension by zero `j_!` on sheaves lies in the essential image of `j_!` on module objects. -/
lemma mem_essImage_openImmersionLowerShriek_of_mem_essImage
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : (j)_!open[Ab.{u + 1}].essImage N.X) : (j)_!open⟦Λ⟧.essImage N := by
  obtain ⟨W, ⟨e⟩⟩ := (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1}
    j).mapModLeft_essImage_of_essImage N hN
  exact ⟨(Mod.comap (asIso (condensedPullbackHom Λ j)).inv).obj W,
    ⟨(linearOpenImmersionLowerShriek Λ j).mapIso
      ((Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).counitIso.app W) ≪≫ e⟩⟩

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- On abelian sheaves, `j_! A ⊗ B` lies in the essential image of the extension by zero `j_!`:
it is `j_!(j^* B ⊗ A)` by the projection formula. -/
lemma tensor_mem_essImage_openImmersionLowerShriek (A : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (j)_!open[Ab.{u + 1}].essImage ((j)_!open[Ab.{u + 1}].obj A ⊗ B) :=
  ⟨(j)^*[Ab.{u + 1}].obj B ⊗ A, ⟨asIso ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
    Ab.{u + 1} j).projectionFormulaMap B A) ≪≫ β_ _ _⟩⟩

/-- If the underlying sheaf of a module object `M` over `Λ_X` lies in the essential image of
the extension by zero `j_!`, then so does the underlying sheaf of `M ⊗_{Λ_X} N`: it is a
coequalizer of objects of the essential image. -/
lemma tensorObj_X_mem_essImage_openImmersionLowerShriek
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : (j)_!open[Ab.{u + 1}].essImage M.X) : (j)_!open[Ab.{u + 1}].essImage (M ⊗ N).X := by
  obtain ⟨A, ⟨e⟩⟩ := hM
  have h := ObjectProperty.prop_of_isColimit (j)_!open[Ab.{u + 1}].essImage
    (Mod.isColimitTensorπ M N)
  refine h ?_
  rintro (_ | _)
  · obtain ⟨B, ⟨e'⟩⟩ := tensor_mem_essImage_openImmersionLowerShriek j A (condensedRingObj Λ X)
    exact Functor.essImage.ofIso (whiskerRightIso (e' ≪≫ whiskerRightIso e _) N.X)
      (tensor_mem_essImage_openImmersionLowerShriek j B N.X)
  · exact Functor.essImage.ofIso (whiskerRightIso e N.X)
      (tensor_mem_essImage_openImmersionLowerShriek j A N.X)

/-- On module objects, `j_! K ⊗_{Λ_X} N` lies in the essential image of the extension by
zero `j_!`. -/
lemma tensorObj_mem_essImage_openImmersionLowerShriek
    (K : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (j)_!open⟦Λ⟧.essImage ((j)_!open⟦Λ⟧.obj K ⊗ N) :=
  mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ j _
    (tensorObj_X_mem_essImage_openImmersionLowerShriek Λ j _ _
      ((j)_!open[Ab.{u + 1}].obj_mem_essImage K.X))

/-- For complexes `K` of module objects over `Λ_U` and `N` over `Λ_X`, each term of the tensor
product of complexes `j_! K ⊗ N` lies in the essential image of `j_!`: it is a coproduct of
the objects `j_! K^p ⊗_{Λ_X} N^q`. -/
lemma tensorObj_X_mem_essImage_mapHomologicalComplex_openImmersionLowerShriek
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) ℤ)
    (N : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (n : ℤ) :
    (j)_!open⟦Λ⟧.essImage ((((j)_!open⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj K ⊗ N).X n) :=
  have : Limits.PreservesColimitsOfSize.{0, 0} (j)_!open⟦Λ⟧ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).leftAdjoint_preservesColimits
  ObjectProperty.prop_of_isColimit _ (GradedObject.isColimitCofanMapObj _ _ n)
    (fun i ↦ tensorObj_mem_essImage_openImmersionLowerShriek Λ j (K.X i.as.1.1) (N.X i.as.1.2))

/-- If every term of a complex `C` of module objects over `Λ_X` lies in the essential image of
the extension by zero `j_!`, then `C` lies in the essential image of `D(j_!)` in the derived
category: the counit `j_! j^* C ⟶ C` is then a termwise isomorphism. -/
lemma Q_obj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek
    (C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (hC : ∀ n, (j)_!open⟦Λ⟧.essImage (C.X n)) :
    D((j)_!open⟦Λ⟧).essImage (DerivedCategory.Q.obj C) := by
  have (n : ℤ) : IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app (C.X n)) :=
    (Adjunction.isIso_counit_app_iff_mem_essImage _).2 (hC n)
  let φ : ((j)_!open⟦Λ⟧.mapHomologicalComplex _).obj
      (((j)^*⟦Λ⟧.mapHomologicalComplex _).obj C) ⟶ C :=
    { f n := (openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app (C.X n)
      comm' _ _ _ := ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.naturality _).symm }
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  exact ⟨DerivedCategory.Q.obj (((j)^*⟦Λ⟧.mapHomologicalComplex _).obj C),
    ⟨((j)_!open⟦Λ⟧.mapDerivedCategoryFactors.app _) ≪≫ DerivedCategory.Q.mapIso (asIso φ)⟩⟩

open DerivedCategory in
/-- For `K` in `D(Mod_{Λ_U})` and `N` in `D(Mod_{Λ_X})`, the derived tensor product
`Dj_! K ⊗ᴸ N` lies in the essential image of `Dj_!`: writing `K = Q K₀` and `N = Qh P` with
`P` K-flat, it is `Q (j_! K₀ ⊗ P)`, whose terms lie in the essential image of `j_!`. -/
lemma tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    D((j)_!open⟦Λ⟧).essImage (D((j)_!open⟦Λ⟧).obj K ⊗ N) := by
  -- Needed to find the K-flat derivability structure on complexes of module objects.
  have (Y : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
      Limits.PreservesColimitsOfShape ℤ ((curriedTensor _).obj Y) := inferInstance
  obtain ⟨P, hP, ⟨eN⟩⟩ := DerivedCategory.exists_kFlat_iso N
  let K₀ := Q.objPreimage K
  let K₁ := (((j)_!open⟦Λ⟧).mapHomologicalComplex (.up ℤ)).obj K₀
  have := Functor.isIso_μNatTrans_Qh_app_app_of_kFlat ((HomotopyCategory.quotient _ _).obj K₁)
    P hP
  refine Functor.essImage.ofIso ?_
    (Q_obj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek Λ j (K₁ ⊗ P.as)
      (tensorObj_X_mem_essImage_mapHomologicalComplex_openImmersionLowerShriek Λ j K₀ P.as))
  exact ((quotientCompQhIso _).app (K₁ ⊗ P.as)).symm ≪≫
    Qh.mapIso (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) K₁ P.as) ≪≫
    (asIso (((Functor.LaxMonoidal.μNatTrans Qh).app
      ((HomotopyCategory.quotient _ _).obj K₁)).app P)).symm ≪≫
    tensorIso ((D((j)_!open⟦Λ⟧).mapIso (Q.objObjPreimageIso K).symm ≪≫
      (((j)_!open⟦Λ⟧).mapDerivedCategoryFactors.app K₀) ≪≫
      ((quotientCompQhIso _).app K₁).symm).symm) eN

end AlgebraicGeometry.ProEtale.CondensedRing
