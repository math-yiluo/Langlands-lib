/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison

/-!
# The derived tensor product with a sheaf

For a pro-étale sheaf `c` on `X`, the left derived functor `L(- ⊗ c)` of the tensor product with
`c` is the derived tensor product `- ⊗ᴸ c` with `c` placed in degree `0`: both are computed on a
K-flat complex `K` by the complex `K ⊗ c`.

For `g : Z ⟶ Y`, sheaves `c_Y` on `Y` and `c_Z` on `Z` and a morphism `κ : g^* c_Y ⟶ c_Z`, the
comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ g^* c_Y ⟶ g^* P ⊗ c_Z` induces a natural transformation
`Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` of left derived functors. Through `L(- ⊗ c) ≅ - ⊗ᴸ c`, it is the
comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ Lg^* c_Y` of the derived pullback with the derived
tensor product (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`) followed by
`Lg^* c_Y ⟶ c_Z`.

The constructions are made for a general coefficient category `A`: for a concrete category such
as `ModuleCat R`, the kernel is slow to check terms involving the tensor product of the homotopy
category.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.leftDerivedTensorRightIso`: `L(- ⊗ c) ≅ - ⊗ᴸ c`.
- `AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap`: the comparison
  `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` induced by `κ`.
- `AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap_app_comp`: its identification with
  the comparison of the derived pullback with the derived tensor product.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory HomologicalComplex Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Single

variable {X : Scheme.{u}} (c : Sheaf (ProEt.topology X) A)

/-- Tensoring with a fixed pro-étale sheaf sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. -/
instance preservesKFlatQuasiIso_tensorRight : (tensorRight c).PreservesKFlatQuasiIso :=
  Functor.PreservesKFlatQuasiIso.mk' _ fun K hK hK' ↦
    CochainComplex.acyclic_tensorRight_of_kFlat K hK hK' c

/-- A pro-étale sheaf `c` placed in degree `0`, as an object of `D(X_proét)`. -/
noncomputable abbrev derivedSingle : DerivedCategory (Sheaf (ProEt.topology X) A) :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c))

set_option linter.unusedSimpArgs false in
/-- On homotopy categories, the tensor product with `c` placed in degree `0` is the degreewise
tensor product with `c`. -/
noncomputable def tensorSingleIso :
    (curriedTensor (HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ))).flip.obj
        ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c)) ≅
      (tensorRight c).mapHomotopyCategory (.up ℤ) :=
  Quotient.natIsoLift _
    ((NatIso.ofComponents (F := HomotopyCategory.quotient _ (.up ℤ) ⋙
        (curriedTensor (HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ))).flip.obj
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c)))
      (G := (tensorRight c).mapHomologicalComplex (.up ℤ) ⋙ HomotopyCategory.quotient _ _)
      (fun K ↦ Functor.Monoidal.μIso (HomotopyCategory.quotient _ (.up ℤ)) K
          ((single _ (.up ℤ) 0).obj c) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _) c).app K))
      (fun {K L} f ↦ by
        have h := (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
          (curriedTensor (Sheaf (ProEt.topology X) A)) c).hom.naturality f
        have h' := Functor.LaxMonoidal.μ_natural_left (HomotopyCategory.quotient _ (.up ℤ)) f
          ((single (Sheaf (ProEt.topology X) A) (.up ℤ) 0).obj c)
        dsimp at h h' ⊢
        simp only [Functor.Monoidal.μIso_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
        rw [reassoc_of% h']
        congr 1
        exact (Functor.map_comp _ _ _).symm.trans
          ((congrArg (HomotopyCategory.quotient _ _).map h).trans (Functor.map_comp _ _ _))) :
      HomotopyCategory.quotient _ _ ⋙ _ ≅
        (tensorRight c).mapHomologicalComplex (.up ℤ) ⋙ HomotopyCategory.quotient _ _) ≪≫
    ((tensorRight c).mapHomotopyCategoryFactors (.up ℤ)).symm)

omit [Abelian.HasFunctorialFlatResolution A] in
/-- On the image of a complex `K`, the isomorphism `AlgebraicGeometry.ProEtale.tensorSingleIso`
is induced by `CochainComplex.mapBifunctorSingle₂Iso`. -/
lemma tensorSingleIso_hom_app_quotient_obj (K : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    (tensorSingleIso c).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c K).hom := by
  have hμ : Functor.LaxMonoidal.μ (HomotopyCategory.quotient (Sheaf (ProEt.topology X) A) (.up ℤ))
      K ((single _ (.up ℤ) 0).obj c) = 𝟙 _ := rfl
  have h : (tensorSingleIso c).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ)) K
          ((single _ (.up ℤ) 0).obj c) ≫
        (HomotopyCategory.quotient _ _).map
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c K).hom) ≫
        ((tensorRight c).mapHomotopyCategoryFactors (.up ℤ)).inv.app K := rfl
  rw [h, hμ]
  simp [Functor.mapHomotopyCategoryFactors]

/-- The counit exhibiting `- ⊗ᴸ c` as the left derived functor of `- ⊗ c`: the comparison
`Qh K ⊗ᴸ Qh c ⟶ Qh (K ⊗ c)` followed by `AlgebraicGeometry.ProEtale.tensorSingleIso`. -/
noncomputable def derivedTensorSingleCounit :
    DerivedCategory.Qh ⋙ (-⊗ᴸ-(X)[A]).flip.obj (derivedSingle c) ⟶
      (tensorRight c).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh where
  app K := Functor.LaxMonoidal.μ DerivedCategory.Qh K _ ≫
    DerivedCategory.Qh.map ((tensorSingleIso c).hom.app K)
  naturality K L f := by
    have h := (tensorSingleIso c).hom.naturality f
    have h' := Functor.LaxMonoidal.μ_natural_left DerivedCategory.Qh f
      ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c))
    dsimp [derivedTensor] at h h' ⊢
    rw [reassoc_of% h', Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h]

lemma derivedTensorSingleCounit_app (K : HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ)) :
    (derivedTensorSingleCounit c).app K = Functor.LaxMonoidal.μ DerivedCategory.Qh K _ ≫
      DerivedCategory.Qh.map ((tensorSingleIso c).hom.app K) :=
  rfl

/-- The counit `Qh K ⊗ᴸ Qh c ⟶ Qh (K ⊗ c)` is an isomorphism on K-flat complexes. -/
lemma isIso_derivedTensorSingleCounit_app
    {K : HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ)}
    (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
    IsIso ((derivedTensorSingleCounit c).app K) := by
  have := isIso_μ_Qh_of_kFlat K hK
    ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c))
  rw [derivedTensorSingleCounit_app]
  infer_instance

instance isLeftDerivedFunctor_derivedTensorSingle :
    ((-⊗ᴸ-(X)[A]).flip.obj (derivedSingle c)).IsLeftDerivedFunctor
      (derivedTensorSingleCounit c) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  rw [(tensorRight c).isLeftDerivedFunctor_iff_isIso_app_of_kFlat]
  exact fun K hK ↦ isIso_derivedTensorSingleCounit_app c
    ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)

/-- **`L(- ⊗ c) ≅ - ⊗ᴸ c`**: the left derived functor of the tensor product with a sheaf `c` is
the derived tensor product with `c` placed in degree `0`. -/
noncomputable def leftDerivedTensorRightIso :
    L(tensorRight c) ≅ (-⊗ᴸ-(X)[A]).flip.obj (derivedSingle c) :=
  Functor.leftDerivedUnique _ _ (tensorRight c).leftDerivedFunctorCounit
    (derivedTensorSingleCounit c) (HomotopyCategory.quasiIso _ (.up ℤ))

/-- The defining property of `AlgebraicGeometry.ProEtale.leftDerivedTensorRightIso`. -/
@[reassoc]
lemma leftDerivedTensorRightIso_hom_app_comp
    (K : HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ)) :
    (leftDerivedTensorRightIso c).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedTensorSingleCounit c).app K =
      (tensorRight c).leftDerivedFunctorCounit.app K := by
  simp [leftDerivedTensorRightIso]

end Single

section Pullback

variable [ProEtale.UpperStarPreservesFlat A] {Y Z : Scheme.{u}} (g : Z ⟶ Y)
  {c_Y : Sheaf (ProEt.topology Y) A} {c_Z : Sheaf (ProEt.topology Z) A}
  (κ : (g)^*[A].obj c_Y ⟶ c_Z)

/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` of pro-étale sheaves: the comonoidal structure of
the pullback followed by `κ : g^* c_Y ⟶ c_Z`. -/
noncomputable def tensorRightUpperStarMap :
    tensorRight c_Y ⋙ (g)^*[A] ⟶ (g)^*[A] ⋙ tensorRight c_Z where
  app P := δ (g)^*[A] P c_Y ≫ (_ ◁ κ)
  naturality P Q f := by
    dsimp
    rw [← δ_natural_left_assoc, Category.assoc, whisker_exchange]

/-- The counit of `L(- ⊗ c_Y) ⋙ Lg^*`: the counit of `L(- ⊗ c_Y)` followed by the counit of
`Lg^*`. -/
noncomputable def leftDerivedTensorRightUpperStarCounit :
    DerivedCategory.Qh ⋙ L(tensorRight c_Y) ⋙ L((g)^*[A]) ⟶
      (tensorRight c_Y).mapHomotopyCategory (.up ℤ) ⋙ (g)^*[A].mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.whiskerRight (tensorRight c_Y).leftDerivedFunctorCounit L((g)^*[A]) ≫
    Functor.whiskerLeft ((tensorRight c_Y).mapHomotopyCategory (.up ℤ))
      (g)^*[A].leftDerivedFunctorCounit

variable (c_Z) in
/-- The counit of `Lg^* ⋙ L(- ⊗ c_Z)`: the counit of `Lg^*` followed by the counit of
`L(- ⊗ c_Z)`. -/
noncomputable def leftDerivedUpperStarTensorRightCounit :
    DerivedCategory.Qh ⋙ L((g)^*[A]) ⋙ L(tensorRight c_Z) ⟶
      (g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ (tensorRight c_Z).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.whiskerRight (g)^*[A].leftDerivedFunctorCounit L(tensorRight c_Z) ≫
    Functor.whiskerLeft ((g)^*[A].mapHomotopyCategory (.up ℤ))
      (tensorRight c_Z).leftDerivedFunctorCounit

variable (c_Z) in
instance isLeftDerivedFunctor_leftDerivedUpperStarTensorRight :
    (L((g)^*[A]) ⋙ L(tensorRight c_Z)).IsLeftDerivedFunctor
      (leftDerivedUpperStarTensorRightCounit g c_Z) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) _ (fun X ↦ ?_)
  -- Stated for an arbitrary K-flat `K`: applying `Derives.isIso_of_isLeftDerivedFunctor` directly
  -- to the pullback of `X` is very slow for the kernel.
  have hk (K : HomotopyCategory (Sheaf (ProEt.topology Z) A) (.up ℤ))
      (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
      IsIso ((tensorRight c_Z).leftDerivedFunctorCounit.app K) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    exact (tensorRight c_Z).isIso_leftDerivedFunctorCounit_app_of_kFlat K
      ((HomotopyCategory.kFlat_quotient_obj_iff K).1 hK)
  have : IsIso ((tensorRight c_Z).leftDerivedFunctorCounit.app
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).functor.obj X))) :=
    hk _ X.property
  have : IsIso ((g)^*[A].leftDerivedFunctorCounit.app
      ((HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).functor.obj X)) :=
    NatIso.isIso_app_of_isIso _ _
  simp only [leftDerivedUpperStarTensorRightCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` on homotopy categories. -/
noncomputable def mapHomotopyCategoryTensorRightUpperStarMap :
    (tensorRight c_Y).mapHomotopyCategory (.up ℤ) ⋙ (g)^*[A].mapHomotopyCategory (.up ℤ) ⟶
      (g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ (tensorRight c_Z).mapHomotopyCategory (.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomotopyCategory (tensorRightUpperStarMap g κ) (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).inv

/-- The comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` induced by the comparison
`g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` of sheaves, where `- ⊗ᴸ c` is the left derived functor of `- ⊗ c`. -/
noncomputable def leftDerivedTensorRightUpperStarMap :
    L(tensorRight c_Y) ⋙ L((g)^*[A]) ⟶ L((g)^*[A]) ⋙ L(tensorRight c_Z) :=
  Functor.leftDerivedNatTrans _ _ (leftDerivedTensorRightUpperStarCounit g)
    (leftDerivedUpperStarTensorRightCounit g c_Z) (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight (mapHomotopyCategoryTensorRightUpperStarMap g κ) DerivedCategory.Qh)

/-- The defining property of `AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap`. -/
@[reassoc]
lemma leftDerivedTensorRightUpperStarMap_app_comp_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    (leftDerivedTensorRightUpperStarMap g κ).app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedUpperStarTensorRightCounit g c_Z).app K =
      (leftDerivedTensorRightUpperStarCounit g).app K ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryTensorRightUpperStarMap g κ).app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ _ _ K

/-- The morphism `Lg^* c_Y ⟶ c_Z` in the derived category induced by `κ`: the counit of `Lg^*`
at `c_Y` followed by `κ`. -/
noncomputable def leftDerivedUpperStarDerivedSingleMap :
    L((g)^*[A]).obj (derivedSingle c_Y) ⟶ derivedSingle c_Z :=
  (g)^*[A].leftDerivedFunctorCounit.app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫ (single _ (.up ℤ) 0).map κ))

instance isIso_leftDerivedUpperStarDerivedSingleMap [IsIso κ] :
    IsIso (leftDerivedUpperStarDerivedSingleMap g κ) := by
  have h₁ : IsIso ((g)^*[A].leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c_Y))) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
      (single _ (.up ℤ) 0).map κ) := IsIso.comp_isIso
  have h₂ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
        (single (Sheaf (ProEt.topology Z) A) (.up ℤ) 0).map κ))) := Functor.map_isIso _ _
  dsimp only [leftDerivedUpperStarDerivedSingleMap]
  exact IsIso.comp_isIso' h₁ h₂

/-- Every object of `D(Y_proét)` is represented by a complex whose pullback by `g` is K-flat. -/
lemma exists_iso_Qh_obj_kFlatUpperStar (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    ∃ P, kFlatUpperStar A g P ∧ Nonempty (DerivedCategory.Qh.obj P ≅ K) := by
  let Λ := (inferInstance :
    Abelian.HasFunctorialFlatResolution (Sheaf (ProEt.topology Y) A)).some.reduced
  have : DerivedCategory.Qh.EssSurj :=
    Localization.essSurj _ (HomotopyCategory.quasiIso (Sheaf (ProEt.topology Y) A) (.up ℤ))
  obtain ⟨K', ⟨e⟩⟩ : ∃ K' : CochainComplex (Sheaf (ProEt.topology Y) A) ℤ,
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K') ≅ K) := by
    obtain ⟨K', hK'⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage K)
    exact ⟨K', ⟨eqToIso (by rw [hK']) ≪≫ DerivedCategory.Qh.objObjPreimageIso K⟩⟩
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (Λ.resolutionNatTrans.app K'))) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ)) _ (by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
      infer_instance)
  exact ⟨_, kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ K',
    ⟨asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (Λ.resolutionNatTrans.app K'))) ≪≫ e⟩⟩

omit [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A] in
/-- The comparison `g^*(K ⊗ c_Y) ⟶ g^* K ⊗ c_Z` of complexes, computed through the
identifications `K ⊗ c[0] ≅ K ⊗ c` (`CochainComplex.mapBifunctorSingle₂Iso`). -/
lemma mapHomologicalComplex_map_mapBifunctorSingle₂Iso_hom_comp
    (K : CochainComplex (Sheaf (ProEt.topology Y) A) ℤ) :
    ((g)^*[A].mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Y K).hom ≫
      (NatTrans.mapHomologicalComplex (tensorRightUpperStarMap g κ) (.up ℤ)).app K =
    mapBifunctorComparison (δNatTrans (g)^*[A]) (.up ℤ) K ((single _ (.up ℤ) 0).obj c_Y) ≫
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁
        ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
          (single _ (.up ℤ) 0).map κ)) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Z
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom := by
  have h₁ : ((g)^*[A].mapHomologicalComplex _).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Y K).inv ≫
      mapBifunctorComparison (δNatTrans (g)^*[A]) (.up ℤ) K ((single _ (.up ℤ) 0).obj c_Y) ≫
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁
        (singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom =
      (NatTrans.mapHomologicalComplex (δRightNatTrans (g)^*[A] c_Y) (.up ℤ)).app K :=
    CochainComplex.mapBifunctorComparison_δNatTrans_single₂ (g)^*[A] K c_Y
  have h₂ : (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map κ) (.up ℤ)).app
        (((g)^*[A].mapHomologicalComplex _).obj K) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Z
        (((g)^*[A].mapHomologicalComplex _).obj K)).inv =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).inv ≫
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁ (single _ (.up ℤ) 0).map κ) :=
    CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂ (curriedTensor _) κ _
  have h₂' : (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁ (single _ (.up ℤ) 0).map κ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Z
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).hom ≫
      (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map κ) (.up ℤ)).app
        (((g)^*[A].mapHomologicalComplex _).obj K) := by
    rw [← cancel_epi (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) ((g)^*[A].obj c_Y)
        (((g)^*[A].mapHomologicalComplex _).obj K)).inv, ← reassoc_of% h₂, Iso.inv_hom_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  have h₃ : (NatTrans.mapHomologicalComplex (tensorRightUpperStarMap g κ) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex (δRightNatTrans (g)^*[A] c_Y) (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map κ) (.up ℤ)).app
          (((g)^*[A].mapHomologicalComplex _).obj K) := by
    rfl
  refine (cancel_epi (((g)^*[A].mapHomologicalComplex (.up ℤ)).map
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c_Y K).inv)).1 ?_
  erw [Iso.inv_hom_id_map_assoc]
  rw [h₃, MonoidalCategory.whiskerLeft_comp, Category.assoc, h₂']
  erw [reassoc_of% h₁]

omit [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A] in
/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` on homotopy categories, computed through
`AlgebraicGeometry.ProEtale.tensorSingleIso`. -/
lemma mapHomotopyCategory_map_tensorSingleIso_hom_app_comp
    (P : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    ((g)^*[A].mapHomotopyCategory (.up ℤ)).map ((tensorSingleIso c_Y).hom.app P) ≫
        (mapHomotopyCategoryTensorRightUpperStarMap g κ).app P =
      ((mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app P).app
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c_Y)) ≫
        (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P ◁
          (HomotopyCategory.quotient _ _).map
            ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
              (single _ (.up ℤ) 0).map κ)) ≫
        (tensorSingleIso c_Z).hom.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hinv (K' : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((g)^*[A] ⋙ tensorRight c_Z))
      (.up ℤ)).inv.app K' = 𝟙 _ := by
    refine (cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K')).1 ?_
    erw [Iso.hom_inv_id_app]
  have hw : ((g)^*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K) ◁
      (HomotopyCategory.quotient _ _).map
        ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
          (single _ (.up ℤ) 0).map κ) =
      (HomotopyCategory.quotient _ _).map (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K ◁
        ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫
          (single _ (.up ℤ) 0).map κ)) := rfl
  have hZ : (tensorSingleIso c_Z).hom.app
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) =
      (HomotopyCategory.quotient _ _).map (CochainComplex.mapBifunctorSingle₂Iso
        (curriedTensor _) c_Z (((g)^*[A].mapHomologicalComplex _).obj K)).hom :=
    tensorSingleIso_hom_app_quotient_obj c_Z _
  rw [tensorSingleIso_hom_app_quotient_obj, mapHomotopyCategoryTensorRightUpperStarMap,
    NatTrans.comp_app, NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app, hinv]
  erw [Category.id_comp, Category.comp_id]
  erw [hw]
  rw [mapHomotopyCategoryδNatTrans_app_app, hZ, NatTrans.mapHomotopyCategory_app]
  have h := congrArg (HomotopyCategory.quotient (Sheaf (ProEt.topology Z) A) (.up ℤ)).map
    (mapHomologicalComplex_map_mapBifunctorSingle₂Iso_hom_comp g κ K)
  refine Eq.trans ?_ (h.trans ((Functor.map_comp _ _ _).trans ?_))
  · exact ((HomotopyCategory.quotient (Sheaf (ProEt.topology Z) A) (.up ℤ)).map_comp _ _).symm
  · exact congrArg (_ ≫ ·) (Functor.map_comp _ _ _)

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor in
/-- The defining property of `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`,
on objects of the homotopy category. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_app_app_fac
    (X M : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (DerivedCategory.Qh.obj X)).app
        (DerivedCategory.Qh.obj M) ≫ ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M ≫
        DerivedCategory.Qh.map (((mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app X).app M) := by
  -- Compare the comparison with its definition as natural transformations, not componentwise:
  -- the componentwise comparison is very slow for the kernel.
  have e : leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A])
          DerivedCategory.Qh) :=
    rfl
  rw [e]
  exact Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A])
      DerivedCategory.Qh) X M

omit [ProEtale.UpperStarPreservesFlat A] in
/-- The counit `AlgebraicGeometry.ProEtale.leftDerivedUpperStarDerivedTensorCounit` on objects:
`Lg^*(μ Qh)` followed by the counit of `Lg^*`. -/
@[reassoc]
lemma leftDerivedUpperStarDerivedTensorCounit_app_app
    (X M : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M =
      L((g)^*[A]).map (Functor.LaxMonoidal.μ DerivedCategory.Qh X M) ≫
        (g)^*[A].leftDerivedFunctorCounit.app (X ⊗ M) :=
  rfl

omit [ProEtale.UpperStarPreservesFlat A] in
/-- The counit `AlgebraicGeometry.ProEtale.derivedTensorLeftDerivedUpperStarCounit` on objects:
the counits of `Lg^*` on both factors followed by `μ Qh`. -/
lemma derivedTensorLeftDerivedUpperStarCounit_app_app
    (X M : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((g)^*[A].leftDerivedFunctorCounit.app X ▷ L((g)^*[A]).obj (DerivedCategory.Qh.obj M)) ≫
        (DerivedCategory.Qh.obj (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj X) ◁
          (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ :=
  rfl

/-- **The comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` is induced by the comparison of the derived
pullback with the derived tensor product**: through `L(- ⊗ c) ≅ - ⊗ᴸ c`, the comparison
`AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap` is
`Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ Lg^* c_Y ⟶ Lg^* K ⊗ᴸ c_Z`. -/
lemma leftDerivedTensorRightUpperStarMap_app_comp
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedTensorRightUpperStarMap g κ).app K ≫
        (leftDerivedTensorRightIso c_Z).hom.app (L((g)^*[A]).obj K) =
      L((g)^*[A]).map ((leftDerivedTensorRightIso c_Y).hom.app K) ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app (derivedSingle c_Y) ≫
        ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).map (leftDerivedUpperStarDerivedSingleMap g κ) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_iso_Qh_obj_kFlatUpperStar g K
  have key {F G : DerivedCategory (Sheaf (ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (ProEt.topology Z) A)} (τ₁ τ₂ : F ⟶ G)
      (h : τ₁.app (DerivedCategory.Qh.obj P) = τ₂.app (DerivedCategory.Qh.obj P)) :
      τ₁.app K = τ₂.app K := by
    rw [← cancel_epi (F.map e.hom), τ₁.naturality, τ₂.naturality, h]
  refine key (leftDerivedTensorRightUpperStarMap g κ ≫
    Functor.whiskerLeft L((g)^*[A]) (leftDerivedTensorRightIso c_Z).hom)
    (Functor.whiskerRight (leftDerivedTensorRightIso c_Y).hom L((g)^*[A]) ≫
      (leftDerivedUpperStarTensorComparison A g).flipApp (derivedSingle c_Y) ≫
      Functor.whiskerLeft L((g)^*[A])
        ((-⊗ᴸ-(Z)[A]).flip.map (leftDerivedUpperStarDerivedSingleMap g κ))) ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.flipApp, flipFunctor_map_app_app, Functor.flip_map_app]
  have := isIso_derivedTensorSingleCounit_app c_Z hP
  have : IsIso ((g)^*[A].leftDerivedFunctorCounit.app P) := NatIso.isIso_app_of_isIso _ _
  have hL : (leftDerivedTensorRightUpperStarMap g κ).app (DerivedCategory.Qh.obj P) ≫
      (leftDerivedTensorRightIso c_Z).hom.app (L((g)^*[A]).obj (DerivedCategory.Qh.obj P)) ≫
      ((-⊗ᴸ-(Z)[A]).flip.obj (derivedSingle c_Z)).map
        ((g)^*[A].leftDerivedFunctorCounit.app P) ≫
      (derivedTensorSingleCounit c_Z).app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P) =
      L((g)^*[A]).map ((tensorRight c_Y).leftDerivedFunctorCounit.app P) ≫
        (g)^*[A].leftDerivedFunctorCounit.app
          (((tensorRight c_Y).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryTensorRightUpperStarMap g κ).app P) := by
    have h := leftDerivedTensorRightUpperStarMap_app_comp_counit g κ P
    rw [leftDerivedUpperStarTensorRightCounit, leftDerivedTensorRightUpperStarCounit,
      NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at h
    rw [← (leftDerivedTensorRightIso c_Z).hom.naturality_assoc]
    dsimp only [Functor.comp_obj]
    rw [leftDerivedTensorRightIso_hom_app_comp]
    exact h
  rw [← cancel_mono (((-⊗ᴸ-(Z)[A]).flip.obj (derivedSingle c_Z)).map
      ((g)^*[A].leftDerivedFunctorCounit.app P) ≫
        (derivedTensorSingleCounit c_Z).app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P)),
    Category.assoc, hL, ← leftDerivedTensorRightIso_hom_app_comp, Functor.map_comp,
    Category.assoc, Category.assoc, cancel_epi]
  have hε := (g)^*[A].leftDerivedFunctorCounit.naturality ((tensorSingleIso c_Y).hom.app P)
  simp only [Functor.comp_map] at hε
  rw [derivedTensorSingleCounit_app, derivedTensorSingleCounit_app, Functor.map_comp,
    Category.assoc, reassoc_of% hε, ← Functor.map_comp]
  erw [mapHomotopyCategory_map_tensorSingleIso_hom_app_comp]
  dsimp only [Functor.flip_obj_obj, curriedTensor_obj_obj]
  rw [Functor.map_comp, Functor.map_comp, ← leftDerivedUpperStarDerivedTensorCounit_app_app_assoc,
    ← leftDerivedUpperStarTensorComparison_app_app_fac_assoc,
    derivedTensorLeftDerivedUpperStarCounit_app_app]
  simp only [Category.assoc, leftDerivedUpperStarDerivedSingleMap, derivedTensor,
    curriedTensor_obj_map, Functor.flip_obj_map, curriedTensor_map_app]
  exact congrArg (_ ≫ ·)
    (Functor.LaxMonoidal.whiskerRight_whiskerLeft_μ_map_whiskerLeft_assoc DerivedCategory.Qh
      _ _ _ _)

end Pullback

end AlgebraicGeometry.ProEtale
