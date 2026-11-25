/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.DimensionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidue

/-!
# The comparison between derived and underived tensor products of sheaves

For sheaves `A`, `B` on the small étale site of `X`, placed in degree `0`, there is a natural
morphism `A[0] ⊗ᴸ B[0] ⟶ (A ⊗ B)[0]` (`AlgebraicGeometry.Etale.singleFunctorTensorToSingle`),
natural in `A`, obtained from the lax monoidal structure of `Qh : K(X_ét) ⥤ D(X_ét)`. It is an
isomorphism for `A` flat (compare `AlgebraicGeometry.Etale.singleFunctorObjTensorIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The lax monoidal structure `Qh K ⊗ Qh L ⟶ Qh (K ⊗ L)` of the localization functor
`Qh : K(X_ét) ⥤ D(X_ét)`, as a natural transformation in `K` for a fixed `L`. -/
@[simps]
noncomputable def qhTensorRightμ (L : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    DerivedCategory.Qh ⋙ tensorRight (DerivedCategory.Qh.obj L) ⟶
      tensorRight L ⋙ DerivedCategory.Qh where
  app K := Functor.LaxMonoidal.μ DerivedCategory.Qh K L
  naturality K K' f := by
    dsimp
    exact Functor.LaxMonoidal.μ_natural_left _ _ _

/-- The monoidal structure of the quotient functor `C(X_ét) ⥤ K(X_ét)`, as a natural isomorphism
in the first variable. -/
noncomputable def quotientTensorRightIso (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    HomotopyCategory.quotient _ (.up ℤ) ⋙
        tensorRight ((HomotopyCategory.quotient _ (.up ℤ)).obj L) ≅
      tensorRight L ⋙ HomotopyCategory.quotient _ (.up ℤ) :=
  NatIso.ofComponents (fun K ↦ Functor.Monoidal.μIso (HomotopyCategory.quotient _ (.up ℤ)) K L)
    (fun f ↦ by
      dsimp
      exact Functor.LaxMonoidal.μ_natural_left _ _ _)

variable (A X) in
/-- The functor `A ↦ A[0]` to the derived category, as the composite through the homotopy
category. -/
noncomputable def singleFunctorIsoQh :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ≅
      HomologicalComplex.single _ (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (.up ℤ) ⋙
        DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQ _ 0 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm

/-- On single complexes, tensoring with `B[0]` is the termwise tensor product with `B`. -/
noncomputable def singleTensorRightSingleIso (B : Sheaf X.smallEtaleTopology A) :
    HomologicalComplex.single _ (.up ℤ) 0 ⋙
        tensorRight ((HomologicalComplex.single _ (.up ℤ) 0).obj B) ≅
      tensorRight B ⋙ HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0 :=
  Functor.isoWhiskerLeft (HomologicalComplex.single _ (.up ℤ) 0)
      (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _) B) ≪≫
    HomologicalComplex.singleMapHomologicalComplex (tensorRight B) (.up ℤ) 0

/-- The comparison `A[0] ⊗ᴸ B[0] ⟶ (A ⊗ B)[0]` between the derived and the underived tensor
products of sheaves placed in degree `0`, as a natural transformation in `A`. -/
noncomputable def singleFunctorTensorToSingle (B : Sheaf X.smallEtaleTopology A) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ⟶
      tensorRight B ⋙ DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 :=
  let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0
  let qt := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)
  let a₁ : DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ≅
      (sg ⋙ qt ⋙ DerivedCategory.Qh) ⋙ tensorRight (DerivedCategory.Qh.obj (qt.obj (sg.obj B))) :=
    Functor.isoWhiskerRight (singleFunctorIsoQh A X) _ ≪≫
      Functor.isoWhiskerLeft _ ((tensoringRight _).mapIso ((singleFunctorIsoQh A X).app B))
  let a₂ : (sg ⋙ qt ⋙ DerivedCategory.Qh) ⋙
        tensorRight (DerivedCategory.Qh.obj (qt.obj (sg.obj B))) ⟶
      (sg ⋙ qt) ⋙ tensorRight (qt.obj (sg.obj B)) ⋙ DerivedCategory.Qh :=
    Functor.whiskerLeft (sg ⋙ qt) (qhTensorRightμ (qt.obj (sg.obj B)))
  let a₃ : (sg ⋙ qt) ⋙ tensorRight (qt.obj (sg.obj B)) ⋙ DerivedCategory.Qh ⟶
      ((sg ⋙ tensorRight (sg.obj B)) ⋙ qt) ⋙ DerivedCategory.Qh :=
    Functor.whiskerRight (Functor.whiskerLeft sg (quotientTensorRightIso (sg.obj B)).hom)
      DerivedCategory.Qh
  let a₄ : ((sg ⋙ tensorRight (sg.obj B)) ⋙ qt) ⋙ DerivedCategory.Qh ⟶
      ((tensorRight B ⋙ sg) ⋙ qt) ⋙ DerivedCategory.Qh :=
    Functor.whiskerRight (Functor.whiskerRight (singleTensorRightSingleIso B).hom qt)
      DerivedCategory.Qh
  let a₅ : ((tensorRight B ⋙ sg) ⋙ qt) ⋙ DerivedCategory.Qh ⟶
      tensorRight B ⋙ DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 :=
    Functor.whiskerLeft (tensorRight B) (singleFunctorIsoQh A X).inv
  a₁.hom ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅

/-- The comparison `A[0] ⊗ᴸ B[0] ⟶ (A ⊗ B)[0]` is an isomorphism for `A` flat. -/
lemma isIso_singleFunctorTensorToSingle_app (B : Sheaf X.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (hF : ObjectProperty.flat F) :
    IsIso ((singleFunctorTensorToSingle B).app F) := by
  have hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
        ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj F)) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 hF)
  have h := isIso_μNatTrans_Qh_app_app_of_kFlat_left _
    ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
      ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj B)) hK
  simp only [Functor.LaxMonoidal.μNatTrans_app_app] at h
  dsimp [singleFunctorTensorToSingle]
  rw [qhTensorRightμ_app]
  infer_instance

/-- The derived tensor product of sheaves placed in degree `0` is concentrated in degrees `≤ 0`. -/
instance isLE_singleFunctor_tensor_singleFunctor (F B : Sheaf X.smallEtaleTopology A) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗ (DerivedCategory.singleFunctor _ 0).obj B).IsLE
      0 :=
  have := DerivedCategory.isLE_tensor ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj B) 0 0
  this

/-- `F ↦ H⁰(F[0] ⊗ᴸ B[0])` sends short exact sequences to right exact sequences. -/
lemma epi_and_exact_homologyFunctor_zero_singleFunctor_tensor (B : Sheaf X.smallEtaleTopology A)
    (S : ShortComplex (Sheaf X.smallEtaleTopology A)) (hS : S.ShortExact) :
    Epi ((DerivedCategory.singleFunctor _ 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ⋙
          DerivedCategory.homologyFunctor _ 0).map S.g) ∧
      (S.map (DerivedCategory.singleFunctor _ 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ⋙
          DerivedCategory.homologyFunctor _ 0)).Exact := by
  have hT := ((-⊗ᴸ-(X)[A]).flip.obj ((DerivedCategory.singleFunctor _ 0).obj B)).map_distinguished
    _ hS.singleTriangle_distinguished
  refine ⟨?_, DerivedCategory.HomologySequence.exact₂ _ hT 0⟩
  refine (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT 0 1).2 ?_
  exact (DerivedCategory.isZero_of_isLE _ 0 1 (by lia)
    (hX := isLE_singleFunctor_tensor_singleFunctor S.X₁ B)).eq_of_tgt _ _

/-- **The degree zero homology of the derived tensor product of sheaves** is the tensor product:
the comparison `H⁰(F[0] ⊗ᴸ B[0]) ⟶ H⁰((F ⊗ B)[0]) = F ⊗ B` is an isomorphism for every sheaf `F`.
Both sides are right exact in `F` and agree for `F` flat, and every sheaf is a quotient of a flat
one. -/
lemma isIso_homologyFunctor_map_singleFunctorTensorToSingle_app
    (B F : Sheaf X.smallEtaleTopology A) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map ((singleFunctorTensorToSingle B).app F)) := by
  have := preservesFiniteColimits_tensorRight B
  let α : DerivedCategory.singleFunctor _ 0 ⋙
      tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ⋙
        DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) 0 ⟶ tensorRight B :=
    Functor.whiskerRight (singleFunctorTensorToSingle B) (DerivedCategory.homologyFunctor _ 0) ≫
      Functor.whiskerLeft (tensorRight B)
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom
  have key := isIso_app_of_rightExact _ _ α ObjectProperty.flat
    (fun Y hY ↦ by
      have := isIso_singleFunctorTensorToSingle_app B Y hY
      dsimp [α]
      infer_instance)
    (fun Y ↦ by
      let R := Classical.arbitrary (Abelian.LeftResolution
        (ObjectProperty.flat.ι : _ ⥤ Sheaf X.smallEtaleTopology A))
      exact ⟨_, R.π.app Y, (R.F.obj Y).property, inferInstance⟩)
    (fun S hS ↦ epi_and_exact_homologyFunctor_zero_singleFunctor_tensor B S hS)
    (fun S hS ↦ ⟨by have := hS.epi_g; exact Functor.map_epi _ _,
      hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance⟩) F
  dsimp [α] at key
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app (F ⊗ B))

end Etale

end AlgebraicGeometry
