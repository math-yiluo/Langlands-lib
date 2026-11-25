/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedComparisonTensorAdjunction
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.Monoidal.Conjugate

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarSectionRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarDerivedTensorSquare

/-! # Scalar adjunction and tensor realization in the coefficient square

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6; blueprint
main-20261015, proper-base-change-rational.proof.md (3)
(blueprint: lem-sfb-coefficient-scalar-tensor-realization).

The section realization retains the ordinary balanced generators, the derived Hom
bijection, and the signed total representative equation. The pullback path comparison
is constructed by localization of the ordinary coefficient square, independently of
the derived direct-image mate. All categories are ordinary unbounded derived categories.

## Main definitions

* `coefficientScalarPathIso`: the localized ordinary coefficient-square comparison.
* `CoefficientScalarSectionRealization`: the normalized scalar adjunction and tensor realization.

## Main statement

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

attribute [local semireducible] CategoryTheory.Mod.monoidalCategory in
private theorem scalarRightLax_eq (Z : Scheme.{u}) :
    letI := internalScalarMonoidal a Z
    (Mod.extendRestrictAdjunction (coefficientMap a Z)).rightAdjointLaxMonoidal =
      Mod.restrictionLaxMonoidal (coefficientMap a Z) := by
  letI := internalScalarMonoidal a Z
  let φ := coefficientMap a Z
  let adj := Mod.extendRestrictAdjunction φ
  have hδ (M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R Z)) :
      Functor.OplaxMonoidal.δ (Mod.extendScalars φ) M N =
        (Mod.canonicalOplax φ).δ M N := by
    apply (adj.homEquiv (M ⊗ N) _).injective
    apply Mod.hom_ext
    change Mod.extendUnitHom φ (M ⊗ N) ≫ _ =
      Mod.extendUnitHom φ (M ⊗ N) ≫ _
    apply (cancel_epi (Mod.tensorObjπ M N)).mp
    exact ((internalScalarMonoidalNormalized_existsUnique a Z).exists.choose_spec M N).trans
      (Mod.canonicalOplax_normalized φ M N).symm
  apply ModuleRingedComparison.laxMonoidal_ext_mu
  intro M N
  have h := congrArg (fun m : (Mod.comap φ).LaxMonoidal ↦ m.μ M N)
    (adj.laxMonoidalEquivOplaxMonoidal.left_inv (Mod.restrictionLaxMonoidal φ))
  change (letI := Mod.canonicalOplax φ; adj.rightAdjointLaxMonoidal.μ M N) = _ at h
  rw [Adjunction.rightAdjointLaxMonoidal_μ] at h ⊢
  rw [hδ]
  exact h

private theorem monoidalIso_of_tensor
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    (h : ∀ M N, Functor.LaxMonoidal.μ F M N ≫ e.hom.app (M ⊗ N) =
      (e.hom.app M ⊗ₘ e.hom.app N) ≫ Functor.LaxMonoidal.μ G M N) :
    NatTrans.IsMonoidal e.hom := by
  have he : Functor.LaxMonoidal.transport e = (inferInstance : G.LaxMonoidal) := by
    apply ModuleRingedComparison.laxMonoidal_ext_mu
    intro M N
    change (e.inv.app M ⊗ₘ e.inv.app N) ≫ _ = _
    rw [h, tensorHom_comp_tensorHom_assoc, e.inv_hom_id_app, e.inv_hom_id_app]
    simp
  have ht := Functor.LaxMonoidal.natTransIsMonoidal_of_transport e
  rwa [he] at ht

private theorem restriction_pure (Z : Scheme.{u})
    (M N : ModuleRingedComparison.internalModules S Z) (U : Z.ProEtᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((Mod.restrictionTensor (coefficientMap a Z) M N).hom.hom.app U)
        (ModuleRingedComparison.internalPureTensor R Z _ _ U x y) =
      ModuleRingedComparison.internalPureTensor S Z M N U x y := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.hom.app U) (Mod.restrictionTensor_π (coefficientMap a Z) M N))
    (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      M.X N.X).app U) (x ⊗ₜ[ℤ] y))

attribute [local semireducible] CategoryTheory.Mod.monoidalCategory in
private theorem comapPush_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := Mod.restrictionLaxMonoidal (coefficientMap a X)
    letI := Mod.restrictionLaxMonoidal (coefficientMap a Y)
    NatTrans.IsMonoidal (comapLowerStarIso a f).hom := by
  letI := Mod.restrictionLaxMonoidal (coefficientMap a X)
  letI := Mod.restrictionLaxMonoidal (coefficientMap a Y)
  apply monoidalIso_of_tensor
  intro M N
  apply ModuleRingedComparison.internalPureTensor_hom_ext R Y
  intro U x y
  have hi (H : ModuleRingedComparison.internalModules S X) :
      ((comapLowerStarIso a f).hom.app H).hom = 𝟙 _ :=
    Mod.comapMapModComapIso_hom_app_hom _ _ _ _ _ _ H
  have hpS := (ModuleRingedComparison.internalPushNormalized_existsUnique S f).exists.choose_spec
  have hpR := (ModuleRingedComparison.internalPushNormalized_existsUnique R f).exists.choose_spec
  have ht {M M' N N' : ModuleRingedComparison.internalModules R Y}
      (b : M ⟶ M') (c : N ⟶ N') (U : Y.ProEtᵒᵖ)
      (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
      ((b ⊗ₘ c).hom.hom.app U) (ModuleRingedComparison.internalPureTensor R Y M N U x y) =
        ModuleRingedComparison.internalPureTensor R Y M' N' U
          ((b.hom.hom.app U) x) ((c.hom.hom.app U) y) :=
    by
      let F := sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}
      have hh : Mod.tensorObjπ M N ≫ (b ⊗ₘ c).hom =
          (b.hom ⊗ₘ c.hom) ≫ Mod.tensorObjπ M' N' := by
        have hf := congrArg (fun z : M ⊗ N ⟶ M' ⊗ N' ↦ Mod.tensorObjπ M N ≫ z.hom)
          (MonoidalCategory.tensorHom_def b c)
        refine hf.trans ?_
        change Mod.tensorObjπ M N ≫ (b ▷ N).hom ≫ (M' ◁ c).hom = _
        rw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft,
          MonoidalCategory.tensorHom_def, Category.assoc]
      have hn := Functor.LaxMonoidal.μ_natural F b.hom c.hom
      have hz : Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫
          F.map (b ⊗ₘ c).hom =
            (F.map b.hom ⊗ₘ F.map c.hom) ≫
              Functor.LaxMonoidal.μ F M'.X N'.X ≫ F.map (Mod.tensorObjπ M' N') := by
        rw [← F.map_comp, hh, F.map_comp, ← Category.assoc, ← hn, Category.assoc]
      exact congrArg (fun z ↦ (z.app U).hom (x ⊗ₜ[ℤ] y)) hz
  change (((Functor.LaxMonoidal.μ (lowerStar S f) M N).hom.hom.app U)
      (((Mod.restrictionTensor (coefficientMap a Y) _ _).hom.hom.app U)
        (ModuleRingedComparison.internalPureTensor R Y _ _ U x y))) = _
  rw [restriction_pure, hpS]
  change _ = ((Mod.restrictionTensor (coefficientMap a X) M N).hom.hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U))
    (((Functor.LaxMonoidal.μ (lowerStar R f) _ _).hom.hom.app U)
      (((((comapLowerStarIso a f).hom.app M) ⊗ₘ
        ((comapLowerStarIso a f).hom.app N)).hom.hom.app U)
          (ModuleRingedComparison.internalPureTensor R Y _ _ U x y)))
  rw [ht, hi, hi]
  change _ = ((Mod.restrictionTensor (coefficientMap a X) M N).hom.hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U))
    (((Functor.LaxMonoidal.μ (lowerStar R f) _ _).hom.hom.app U)
      (ModuleRingedComparison.internalPureTensor R Y _ _ U x y))
  rw [hpR, restriction_pure]

private theorem adjMonoidal_of_rightLax
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal] [m : G.LaxMonoidal]
    (h : m = adj.rightAdjointLaxMonoidal) : adj.IsMonoidal := by
  rw [h]
  infer_instance

private theorem adjMonoidal_of_leftOplax
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [m : F.OplaxMonoidal] [G.LaxMonoidal]
    (h : adj.leftAdjointOplaxMonoidal = m) : adj.IsMonoidal := by
  rw [← h]
  infer_instance

attribute [local semireducible] CategoryTheory.Mod.monoidalCategory in
private theorem scalarPull_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := internalScalarMonoidal a X
    letI := internalScalarMonoidal a Y
    letI := monoidal_upperStar R f
    letI := monoidal_upperStar S f
    NatTrans.IsMonoidal (pullIso a f).symm.hom := by
  letI := internalScalarMonoidal a X
  letI := internalScalarMonoidal a Y
  letI := monoidal_upperStar R f
  letI := monoidal_upperStar S f
  letI : (upperStar R f).OplaxMonoidal := (monoidal_upperStar R f).toOplaxMonoidal
  letI : (upperStar S f).OplaxMonoidal := (monoidal_upperStar S f).toOplaxMonoidal
  letI := Mod.restrictionLaxMonoidal (coefficientMap a X)
  letI := Mod.restrictionLaxMonoidal (coefficientMap a Y)
  haveI hx : (Mod.extendRestrictAdjunction (coefficientMap a X)).IsMonoidal := by
    exact adjMonoidal_of_rightLax _ (scalarRightLax_eq a X).symm
  haveI hy : (Mod.extendRestrictAdjunction (coefficientMap a Y)).IsMonoidal := by
    exact adjMonoidal_of_rightLax _ (scalarRightLax_eq a Y).symm
  haveI hr : (upperStarLowerStarAdjunction R f).IsMonoidal := by
    exact adjMonoidal_of_leftOplax _
      (ModuleRingedComparison.internalPullOplax_eq_canonical R f)
  haveI hs : (upperStarLowerStarAdjunction S f).IsMonoidal := by
    exact adjMonoidal_of_leftOplax _
      (ModuleRingedComparison.internalPullOplax_eq_canonical S f)
  haveI hc := comapPush_monoidal a f
  haveI hp : NatTrans.IsMonoidal (pullIso a f).hom := by
    exact isMonoidal_conjugateEquiv_symm
      ((Mod.extendRestrictAdjunction (coefficientMap a Y)).comp
        (upperStarLowerStarAdjunction S f))
      ((upperStarLowerStarAdjunction R f).comp
        (Mod.extendRestrictAdjunction (coefficientMap a X)))
      (comapLowerStarIso a f).hom
  exact inferInstanceAs (NatTrans.IsMonoidal (pullIso a f).inv)

variable [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

/-- Scalar adjunction and tensor realization, and the tensor equation for the canonical
coefficient ringed-square pullback comparison, on all unbounded objects.
Source: Stacks 07A4, 07A6 and 0D6D; blueprint rational proper base change, proof (3)
(blueprint: lem-sfb-coefficient-scalar-tensor-realization).

Proof: the canonical scalar oplax structure is normalized on balanced generators, so
its adjoint restriction lax structure is the prescribed one. Check the ordinary
restriction/direct-image comparison on generalized pure tensors, then apply monoidal
conjugation to the scalar and geometric adjunctions. This proves ordinary monoidality
of the actual pullIso comparison. The separate coefficientScalarSectionRealization
lemma supplies the normalized section clauses at X and Y; the separate
coefficientScalarDerivedTensorSquare lemma lifts this proved ordinary monoidality to
the displayed derived tensor equation. Combine the three clauses. Nothing uses
boundedness, constructibility or properness. -/
theorem coefficientScalarTensorRealization
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    CoefficientScalarSectionRealization a X.left ∧
    CoefficientScalarSectionRealization a Y.left ∧
    ∀ A B : DerivedCategory (ModuleRingedComparison.internalModules R Y.left),
      (moduleObjectDerivedPullback S f.left).map
          (((internalScalarTensorComparison a Y.left).app A).app B) ≫
        coefficientGeometricTensorComparison S f.left
          ((internalScalarExtension a Y.left).obj A)
          ((internalScalarExtension a Y.left).obj B) ≫
        ((derivedTensor S X.left).map ((coefficientScalarPathIso a f.left).hom.app A)).app
          ((moduleObjectDerivedPullback S f.left).obj
            ((internalScalarExtension a Y.left).obj B)) ≫
        ((derivedTensor S X.left).obj
          ((internalScalarExtension a X.left).obj
            ((moduleObjectDerivedPullback R f.left).obj A))).map
              ((coefficientScalarPathIso a f.left).hom.app B) =
      (coefficientScalarPathIso a f.left).hom.app (((derivedTensor R Y.left).obj A).obj B) ≫
        (internalScalarExtension a X.left).map
          (coefficientGeometricTensorComparison R f.left A B) ≫
        ((internalScalarTensorComparison a X.left).app
          ((moduleObjectDerivedPullback R f.left).obj A)).app
            ((moduleObjectDerivedPullback R f.left).obj B) := by
  refine ⟨coefficientScalarSectionRealization a X.left,
    coefficientScalarSectionRealization a Y.left, ?_⟩
  exact coefficientScalarDerivedTensorSquare a f.left (scalarPull_monoidal a f.left)

end AlgebraicGeometry.ProEtale.CondensedRing
