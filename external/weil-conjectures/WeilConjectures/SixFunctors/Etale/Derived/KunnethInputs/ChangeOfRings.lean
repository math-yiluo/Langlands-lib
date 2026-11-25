/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Change of rings for the derived tensor product

For a ring homomorphism `f : R →+* S`, an `R`-module `M` and an `S`-module `P` we construct the
natural isomorphism `M ⊗_R P ≅ (S ⊗_R M) ⊗_S P` of `R`-modules
(`ModuleCat.tensorRestrictScalarsIso`) and deduce, for `M` flat and a complex `N` of `S`-modules,
`M ⊗ᴸ_R N ≅ (S ⊗_R M) ⊗ᴸ_S N` in `D(R)` (`DerivedCategory.changeOfRingsTensorIso`, blueprint
`lem-kun-change-of-rings-tensor`).

For a homomorphism of commutative rings `f : R →+* S`, a flat `R`-module `M` and a complex `N`
of `S`-modules, `M ⊗ᴸ_R N ≅ (S ⊗_R M) ⊗ᴸ_S N` in `D(R)`
(`DerivedCategory.changeOfRingsTensorIso`, blueprint `lem-kun-change-of-rings-tensor`). The
module-level input is `ModuleCat.tensorRestrictScalarsIso`: `M ⊗_R P ≅ (S ⊗_R M) ⊗_S P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TensorProduct

open scoped ChangeOfRings

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The comparison `M ⊗_R P ⟶ (S ⊗_R M) ⊗_S P`, `m ⊗ p ↦ (1 ⊗ m) ⊗ p`, for an `R`-module `M`
and an `S`-module `P`, natural in `P`. -/
noncomputable def tensorRestrictScalarsHom (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    M ⊗ (restrictScalars f).obj P ⟶ (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) :=
  (extendRestrictScalarsAdj f).unit.app M ▷ _ ≫
    Functor.LaxMonoidal.μ (restrictScalars f) ((extendScalars f).obj M) P

set_option backward.isDefEq.respectTransparency false in
lemma tensorRestrictScalarsHom_tmul (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) (m : M)
    (p : P) :
    tensorRestrictScalarsHom f M P (m ⊗ₜ p) = ((1 : S) ⊗ₜ[R, f] m) ⊗ₜ p := by
  simp [tensorRestrictScalarsHom]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `ModuleCat.tensorRestrictScalarsHom` is bijective: it is the composite of the symmetries and
the inverse of the cancellation `P ⊗_S (S ⊗_R M) ≃ P ⊗_R M`. -/
lemma bijective_tensorRestrictScalarsHom (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    Function.Bijective (tensorRestrictScalarsHom f M P) := by
  let := f.toAlgebra
  let : Module R P := Module.compHom P f
  have : IsScalarTower R S P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : M ⊗[R] P ≃+ (S ⊗[R] M) ⊗[S] P :=
    ((TensorProduct.comm R M P).toAddEquiv.trans
      (AlgebraTensorModule.cancelBaseChange R S S P M).symm.toAddEquiv).trans
      (TensorProduct.comm S P (S ⊗[R] M)).toAddEquiv
  have key : ∀ x : M ⊗[R] P, tensorRestrictScalarsHom f M P x = e x := fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul m p =>
      rw [tensorRestrictScalarsHom_tmul]
      rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ _ hx hy).trans (map_add e x y).symm)
  exact ⟨fun a b hab ↦ e.injective ((key a).symm.trans (hab.trans (key b))),
    fun y ↦ ⟨e.symm y, (key _).trans (e.apply_symm_apply y)⟩⟩

/-- `M ⊗_R P ≅ (S ⊗_R M) ⊗_S P` as `R`-modules, for an `R`-module `M` and an `S`-module `P`,
`m ⊗ p ↦ (1 ⊗ m) ⊗ p`. -/
noncomputable def tensorRestrictScalarsIso (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    M ⊗ (restrictScalars f).obj P ≅ (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) :=
  have : IsIso (tensorRestrictScalarsHom f M P) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_tensorRestrictScalarsHom f M P)
  asIso (tensorRestrictScalarsHom f M P)

/-- The isomorphism `M ⊗_R P ≅ (S ⊗_R M) ⊗_S P` as a natural isomorphism of functors of the
`S`-module `P`. -/
noncomputable def restrictScalarsCompTensorLeftIso (M : ModuleCat.{u} R) :
    restrictScalars f ⋙ tensorLeft M ≅ tensorLeft ((extendScalars f).obj M) ⋙ restrictScalars f :=
  NatIso.ofComponents (tensorRestrictScalarsIso f M) fun {P P'} g ↦ by
    dsimp [tensorRestrictScalarsIso, tensorRestrictScalarsHom]
    rw [whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_right, Category.assoc]

end ModuleCat

namespace DerivedCategory

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} S)]

/-- Blueprint `lem-kun-change-of-rings-tensor`: change of rings for the derived tensor
product. Let `f : R →+* S` be a homomorphism of commutative rings, `M` a flat `R`-module and `N`
a complex of `S`-modules, viewed as a complex of `R`-modules by restriction of scalars. Then
`M ⊗ᴸ_R N ≅ (S ⊗_R M) ⊗ᴸ_S N` canonically in `D(R)`: both derived tensor products are computed
termwise, `M` and `S ⊗_R M` being flat, and `M ⊗_R N^i ≅ (S ⊗_R M) ⊗_S N^i`
(`ModuleCat.tensorRestrictScalarsIso`).

The blueprint states the case `R = ℤ/n`, `S = ℤ/ℓ` (`ℓ` a prime dividing `n`) and `N` a complex
of `R`-modules annihilated by `ℓ`, i.e. a complex of `𝔽_ℓ`-vector spaces; there
`S ⊗_R M ≅ M/ℓM`. -/
noncomputable def changeOfRingsTensorIso (M : ModuleCat.{u} R) [Module.Flat R M]
    (N : CochainComplex (ModuleCat.{u} S) ℤ) :
    (singleFunctor _ 0).obj M ⊗ (ModuleCat.restrictScalars f).mapDerivedCategory.obj (Q.obj N) ≅
      (ModuleCat.restrictScalars f).mapDerivedCategory.obj
        ((singleFunctor _ 0).obj ((ModuleCat.extendScalars f).obj M) ⊗ Q.obj N) := by
  letI := f.toAlgebra
  have hM : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) :=
    (CochainComplex.kFlat_single_obj_iff_flat _ 0).2 ((ModuleCat.flat_iff_flat M).2 inferInstance)
  have : Module.Flat S ((ModuleCat.extendScalars f).obj M) :=
    inferInstanceAs (Module.Flat S (S ⊗[R] M))
  have hM' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((HomologicalComplex.single _ (.up ℤ) 0).obj ((ModuleCat.extendScalars f).obj M)) :=
    (CochainComplex.kFlat_single_obj_iff_flat _ 0).2 ((ModuleCat.flat_iff_flat _).2 inferInstance)
  let res := ModuleCat.restrictScalars.{u} f
  exact whiskerLeftIso _ (res.mapDerivedCategoryFactors.app N) ≪≫
    QObjTensorQObjIsoOfKFlatLeft _ _ hM ≪≫
    Q.mapIso ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) M).app _ ≪≫
      (Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsCompTensorLeftIso f M) _).app
        N ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (tensorLeft _ ⋙ res)) _).app N).symm ≪≫
      (res.mapHomologicalComplex _).mapIso
        ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) _).app N).symm) ≪≫
    (res.mapDerivedCategoryFactors.app _).symm ≪≫
    res.mapDerivedCategory.mapIso (QObjTensorQObjIsoOfKFlatLeft _ _ hM').symm

end DerivedCategory
