/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# The derived tensor product with an étale sheaf

For an étale sheaf `c` on `X`, the left derived functor `L(- ⊗ c)` of the tensor product with
`c` is the derived tensor product `- ⊗ᴸ c` with `c` placed in degree `0`: both are computed on a
K-flat complex `K` by the complex `K ⊗ c`.

For `g : Z ⟶ Y`, sheaves `c_Y` on `Y` and `c_Z` on `Z` and a morphism `κ : g^* c_Y ⟶ c_Z`, the
comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ g^* c_Y ⟶ g^* P ⊗ c_Z` induces a natural transformation
`Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` of left derived functors. Its identification with the
comparison of the derived pullback with the derived tensor product is
`AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap_app_comp`, in
`WeilConjectures.SixFunctors.Etale.Derived.TensorSheafUpperStar`.

The constructions are made for a general coefficient category `A`: for a concrete category such
as `ModuleCat R`, the kernel is slow to check terms involving the tensor product of the homotopy
category.

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf`.

## Main definitions and results

- `AlgebraicGeometry.Etale.leftDerivedTensorRightIso`: `L(- ⊗ c) ≅ - ⊗ᴸ c`.
- `AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap`: the comparison
  `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` induced by `κ`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedSingleMap`: the morphism
  `Lg^* c_Y ⟶ c_Z` in `D(Z_ét)` induced by `κ`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory HomologicalComplex Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Single

variable {X : Scheme.{u}} (c : Sheaf X.smallEtaleTopology A)

/-- Tensoring with a fixed étale sheaf sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. -/
instance preservesKFlatQuasiIso_tensorRight : (tensorRight c).PreservesKFlatQuasiIso :=
  Functor.PreservesKFlatQuasiIso.mk' _ fun K hK hK' ↦
    CochainComplex.acyclic_tensorRight_of_kFlat K hK hK' c

/-- A étale sheaf `c` placed in degree `0`, as an object of `D(X_ét)`. -/
noncomputable abbrev derivedSingle : DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c))

set_option linter.unusedSimpArgs false in
/-- On homotopy categories, the tensor product with `c` placed in degree `0` is the degreewise
tensor product with `c`. -/
noncomputable def tensorSingleIso :
    (curriedTensor (HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ))).flip.obj
        ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c)) ≅
      (tensorRight c).mapHomotopyCategory (.up ℤ) :=
  Quotient.natIsoLift _
    ((NatIso.ofComponents (F := HomotopyCategory.quotient _ (.up ℤ) ⋙
        (curriedTensor (HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ))).flip.obj
          ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c)))
      (G := (tensorRight c).mapHomologicalComplex (.up ℤ) ⋙ HomotopyCategory.quotient _ _)
      (fun K ↦ Functor.Monoidal.μIso (HomotopyCategory.quotient _ (.up ℤ)) K
          ((single _ (.up ℤ) 0).obj c) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _) c).app K))
      (fun {K L} f ↦ by
        have h := (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
          (curriedTensor (Sheaf X.smallEtaleTopology A)) c).hom.naturality f
        have h' := Functor.LaxMonoidal.μ_natural_left (HomotopyCategory.quotient _ (.up ℤ)) f
          ((single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj c)
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
/-- On the image of a complex `K`, the isomorphism `AlgebraicGeometry.Etale.tensorSingleIso`
is induced by `CochainComplex.mapBifunctorSingle₂Iso`. -/
lemma tensorSingleIso_hom_app_quotient_obj (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    (tensorSingleIso c).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) c K).hom := by
  have hμ : Functor.LaxMonoidal.μ (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ))
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
`Qh K ⊗ᴸ Qh c ⟶ Qh (K ⊗ c)` followed by `AlgebraicGeometry.Etale.tensorSingleIso`. -/
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

lemma derivedTensorSingleCounit_app (K : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (derivedTensorSingleCounit c).app K = Functor.LaxMonoidal.μ DerivedCategory.Qh K _ ≫
      DerivedCategory.Qh.map ((tensorSingleIso c).hom.app K) :=
  rfl

/-- The counit `Qh K ⊗ᴸ Qh c ⟶ Qh (K ⊗ c)` is an isomorphism on K-flat complexes. -/
lemma isIso_derivedTensorSingleCounit_app
    {K : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)}
    (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
    IsIso ((derivedTensorSingleCounit c).app K) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh K
      ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c))) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat_left K _ hK
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

/-- The defining property of `AlgebraicGeometry.Etale.leftDerivedTensorRightIso`. -/
@[reassoc]
lemma leftDerivedTensorRightIso_hom_app_comp
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedTensorRightIso c).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedTensorSingleCounit c).app K =
      (tensorRight c).leftDerivedFunctorCounit.app K := by
  simp [leftDerivedTensorRightIso]

end Single

section Pullback

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y) [(g)^*[A].PreservesFlat]
  {c_Y : Sheaf Y.smallEtaleTopology A} {c_Z : Sheaf Z.smallEtaleTopology A}
  (κ : (g)^*[A].obj c_Y ⟶ c_Z)

/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` of étale sheaves: the comonoidal structure of
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
  have hk (K : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ))
      (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
      IsIso ((tensorRight c_Z).leftDerivedFunctorCounit.app K) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    exact (tensorRight c_Z).isIso_leftDerivedFunctorCounit_app_of_kFlat K
      ((HomotopyCategory.kFlat_quotient_obj_iff K).1 hK)
  have h₁ : IsIso ((tensorRight c_Z).leftDerivedFunctorCounit.app
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).functor.obj X))) :=
    hk _ X.property
  have : IsIso ((g)^*[A].leftDerivedFunctorCounit.app
      ((HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).functor.obj X)) :=
    NatIso.isIso_app_of_isIso _ _
  dsimp only [leftDerivedUpperStarTensorRightCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) h₁

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

/-- The defining property of `AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap`. -/
@[reassoc]
lemma leftDerivedTensorRightUpperStarMap_app_comp_counit
    (K : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
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
        (single (Sheaf Z.smallEtaleTopology A) (.up ℤ) 0).map κ))) := Functor.map_isIso _ _
  dsimp only [leftDerivedUpperStarDerivedSingleMap]
  exact IsIso.comp_isIso' h₁ h₂

/-- Every object of `D(Y_ét)` is represented by a complex whose pullback by `g` is K-flat. -/
lemma exists_iso_Qh_obj_kFlatUpperStar (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ∃ P, kFlatUpperStar A g P ∧ Nonempty (DerivedCategory.Qh.obj P ≅ K) := by
  let Λ := (inferInstance :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some.reduced
  have : DerivedCategory.Qh.EssSurj :=
    Localization.essSurj _ (HomotopyCategory.quasiIso (Sheaf Y.smallEtaleTopology A) (.up ℤ))
  obtain ⟨K', ⟨e⟩⟩ : ∃ K' : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ,
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

end Pullback

end AlgebraicGeometry.Etale
