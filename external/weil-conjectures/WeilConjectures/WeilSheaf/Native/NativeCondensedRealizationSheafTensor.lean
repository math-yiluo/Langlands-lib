/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedModelTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization
public import WeilConjectures.WeilSheaf.Native.NativeForgetTotalTensor
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# The condensed realization of the native sheaf tensor

The condensed realization `R = condensedRealization k₀ l X` of pro-étale Weil sheaves carries
the native sheaf tensor `nativeOpenSheafTensor k₀ l X` (left argument first) to the tensor
product of condensed module objects on the geometric fibre:
```
R (M ⊗ N) ≅ R M ⊗ R N
```
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationSheafTensorIso`). The underlying
`ℓ`-adic sheaf of the native tensor `M ⊗ N` is the coequalizer tensor
`(Mod.tensorLeft N).obj M` of the carriers, which is identified with the monoidal tensor product
by `Mod.relativeTensorRightIso`; the condensed model is then monoidal
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModTensorIso`).

On pure tensors the comparison is the lax monoidal structure of the forgetful functor from
sheaves of `ℚ̄_ℓ`-modules to abelian sheaves followed by the projection onto the native tensor
(`AlgebraicGeometry.ProEtaleWeilSheaf.tensorObjπ_condensedRealizationSheafTensorIso_inv_app_hom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

section RelativeTensor

variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
/-- On the projection `M ⊗ N ⟶ M ⊗_R N`, the comparison `Mod.relativeTensorRightIso` is the
projection of the monoidal tensor product. -/
@[reassoc]
private lemma tensorπ_relativeTensorRightIso_hom_app (M N : Mod C R) :
    Mod.tensorπ M N ≫ ((Mod.relativeTensorRightIso N).hom.app M).hom = Mod.tensorObjπ M N := by
  have h : colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
      (Mod.relativeTensorRightIso N).hom.app M = Mod.relativeTensorπ M N := by
    simp [Mod.relativeTensorRightIso, HasColimit.ι_isoOfNatIso_hom_assoc,
      Mod.relativeTensorCofork]
  exact congrArg Mod.Hom.hom h

omit [MonoidalPreadditive C] in
/-- The comparison `Mod.relativeTensorRightIso` is natural in both factors. -/
private lemma relativeTensorRightIso_hom_natural {M M' N N' : Mod C R} (f : M ⟶ M')
    (g : N ⟶ N') :
    (Mod.tensorLeftMap g).app M ≫ (Mod.tensorLeft N').map f ≫
        (Mod.relativeTensorRightIso N').hom.app M' =
      (Mod.relativeTensorRightIso N).hom.app M ≫ (f ⊗ₘ g) := by
  apply Mod.tensorLeft_obj_hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', Mod.tensorπ_tensorLeftMap_assoc,
    Mod.tensorπ_map_assoc, tensorπ_relativeTensorRightIso_hom_app,
    tensorπ_relativeTensorRightIso_hom_app_assoc, MonoidalCategory.tensorHom_def,
    Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft,
    whisker_exchange_assoc]

end RelativeTensor

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable [Fact (ringChar k₀ ≠ l)]

/-- The native sheaf tensor of pro-étale Weil sheaves, on underlying `ℓ`-adic sheaves. -/
lemma forget_map_nativeOpenSheafTensor_map
    {MN MN' : ProEtaleWeilSheaf k₀ l X × ProEtaleWeilSheaf k₀ l X} (fg : MN ⟶ MN') :
    (Endofunctor.IsoAlgebra.forget _).map ((nativeOpenSheafTensor k₀ l X).map fg) =
      (Mod.tensorLeftMap fg.2.hom.f).app MN.1.carrier ≫
        (Mod.tensorLeft MN'.2.carrier).map fg.1.hom.f := by
  simp [nativeOpenSheafTensor, nativeTensorBifunctor, nativeTensorMap_app_hom_f]
  rfl

/-- The underlying `ℓ`-adic sheaf of the native sheaf tensor `M ⊗ N` of pro-étale Weil sheaves is
the monoidal tensor product of the carriers of `M` and `N`, by `Mod.relativeTensorRightIso`. -/
noncomputable def forgetNativeOpenSheafTensorIso :
    nativeOpenSheafTensor k₀ l X ⋙ Endofunctor.IsoAlgebra.forget _ ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
        Functor.uncurry.obj (curriedTensor _) :=
  NatIso.ofComponents (fun MN ↦ (Mod.relativeTensorRightIso MN.2.carrier).app MN.1.carrier)
    (fun {MN MN'} fg ↦ by
      rw [Functor.comp_map, forget_map_nativeOpenSheafTensor_map, Category.assoc, Iso.app_hom,
        Iso.app_hom, relativeTensorRightIso_hom_natural, MonoidalCategory.tensorHom_def]
      rfl)

/-- The condensed realization carries the native sheaf tensor of pro-étale Weil sheaves (left
argument first) to the tensor product of condensed module objects on the geometric fibre. On
`(M, N)` it is the image of `Mod.relativeTensorRightIso`, identifying the coequalizer tensor of
the carriers with their monoidal tensor product, followed by the inverse of the monoidal
comparison of the condensed model. -/
noncomputable def condensedRealizationSheafTensorIso :
    nativeOpenSheafTensor k₀ l X ⋙ condensedRealization k₀ l X ≅
      (condensedRealization k₀ l X).prod (condensedRealization k₀ l X) ⋙
        Functor.uncurry.obj (curriedTensor _) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (forgetNativeOpenSheafTensorIso k₀ l X) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.uncurryTensorIsoOfTensorIso
        (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor
        (adicSheafEquivCondensedModTensorIso l _)
        (adicSheafEquivCondensedModTensorIso_hom_natural l _)) ≪≫
    (Functor.associator _ _ _).symm

/-- The inverse of `condensedRealizationSheafTensorIso` at `(M, N)` is the monoidal comparison of
the condensed model followed by the image of the inverse of `Mod.relativeTensorRightIso`. -/
lemma condensedRealizationSheafTensorIso_inv_app (M N : ProEtaleWeilSheaf k₀ l X) :
    (condensedRealizationSheafTensorIso k₀ l X).inv.app (M, N) =
      (adicSheafEquivCondensedModTensorIso l _ M.carrier N.carrier).hom ≫
        (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map
          ((Mod.relativeTensorRightIso N.carrier).inv.app M.carrier) := by
  simp [condensedRealizationSheafTensorIso, forgetNativeOpenSheafTensorIso]

/-- On pure tensors, the inverse of the condensed realization of the native sheaf tensor is the
lax monoidal structure of the forgetful functor from sheaves of `ℚ̄_ℓ`-modules to abelian sheaves
followed by the image of the projection `M ⊗ N ⟶ M ⊗_{ℚ̄_ℓ} N` onto the native tensor. -/
@[reassoc]
lemma tensorObjπ_condensedRealizationSheafTensorIso_inv_app_hom
    (M N : ProEtaleWeilSheaf k₀ l X) :
    Mod.tensorObjπ ((condensedRealization k₀ l X).obj M) ((condensedRealization k₀ l X).obj N) ≫
        ((condensedRealizationSheafTensorIso k₀ l X).inv.app (M, N)).hom =
      Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l _) M.carrier.X N.carrier.X ≫
        (weilCoefficientsForgetAb l _).map (Mod.tensorπ M.carrier N.carrier) := by
  have h : Mod.tensorObjπ M.carrier N.carrier ≫
      ((Mod.relativeTensorRightIso N.carrier).inv.app M.carrier).hom =
        Mod.tensorπ M.carrier N.carrier := by
    rw [← tensorπ_relativeTensorRightIso_hom_app, Category.assoc, ← Mod.comp_hom',
      Iso.hom_inv_id_app, Mod.id_hom', Category.comp_id]
  rw [condensedRealizationSheafTensorIso_inv_app, Mod.comp_hom']
  erw [tensorObjπ_adicSheafEquivCondensedModTensorIso_hom_hom_assoc]
  rw [← h, Functor.map_comp]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
