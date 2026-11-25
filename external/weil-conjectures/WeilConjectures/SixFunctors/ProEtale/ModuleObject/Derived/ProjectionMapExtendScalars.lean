/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCompNatIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-!
# The projection map under a flat change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings such that every coefficient change
`a_X : Λ_X ⟶ Λ'_X` is flat, write `T = L(Ext_a) = Λ' ⊗ᴸ_Λ -` for the derived extensions of
scalars, and let `f : X ⟶ Y` be a morphism of schemes. The extensions of scalars are strong
monoidal (`Functor.leftDerivedTensorComparison`), and the derived (Pull) isomorphism
`Lf^* ⋙ T ≅ T ⋙ Lf^*` (`ProEtale.CondensedRing.derivedPullIso`) is compatible with these tensor
comparisons and those of the derived pullbacks
(`ProEtale.CondensedRing.comparisonCompatible_derivedPullIso`): it is induced by the underived
(Pull) isomorphism, which is monoidal. Its mate along the adjunctions `Lf^* ⊣ Rf_*` is the (Push)
comparison `T Rf_* ⟶ Rf_* T` (`ProEtale.CondensedRing.derivedPushHom`). Hence `T` carries the
projection map `Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ Lf^* M)` with coefficients `Λ` to the projection map
with coefficients `Λ'` at `(T K, T M)`, up to (Push) at `K` and at `K ⊗ᴸ Lf^* M`
(`CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`). In particular the
projection formula with coefficients `Λ'` holds at `(T K, T M)` as soon as it holds with
coefficients `Λ` at `(K, M)` and (Push) is invertible at `K` and at `K ⊗ᴸ Lf^* M`
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_extendScalars`).

This is the formal part of blueprint `proposition-proper-direct-image-constructible-complexes` (3),
deducing the projection formula with coefficients `E` and `ℚ̄_ℓ` from the one with coefficients
`𝒪_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-- Reverse a tensor comparison square after identifying its isomorphism and comparison maps. -/
private theorem comparisonCompatible_symm_of_tensorComparison
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    {F : D ⥤ C} {F' : D' ⥤ C'} {N : D ⥤ D'} {M : C ⥤ C'}
    (α : F ⋙ M ≅ N ⋙ F')
    (t : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (t' : (Functor.postcompose₂.obj F').obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj (curriedTensor C'))
    (m : (Functor.postcompose₂.obj M).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ C').obj M).obj M).obj (curriedTensor C'))
    (n : (Functor.postcompose₂.obj N).obj (curriedTensor D) ≅
      (((Functor.whiskeringLeft₂ D').obj N).obj N).obj (curriedTensor D'))
    {β : F ⋙ M ≅ N ⋙ F'}
    {s : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C)}
    {s' : (Functor.postcompose₂.obj F').obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj (curriedTensor C')}
    (hα : α = β) (ht : t = s) (ht' : t' = s')
    (h : ∀ X Y, F'.map ((n.hom.app X).app Y) ≫ (s'.app (N.obj X)).app (N.obj Y) =
      β.inv.app (X ⊗ Y) ≫ M.map ((s.app X).app Y) ≫
        (m.hom.app (F.obj X)).app (F.obj Y) ≫ (β.hom.app X ⊗ₘ β.hom.app Y)) :
    Adjunction.ComparisonCompatible α.symm t t' m n := by
  subst β s s'
  intro X Y
  simp only [Iso.symm_inv, Iso.symm_hom, curriedTensor_obj_obj,
    curriedTensor_map_app, curriedTensor_obj_map, Functor.comp_obj]
  rw [reassoc_of% (h X Y), Iso.hom_inv_id_app_assoc, ← MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]

/-- Transport projection invertibility using an identified representative of the mate. -/
private theorem isIso_projectionMap_of_mate_eq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
    {N_D : D ⥤ D'} {N_C : C ⥤ C'} {α : N_D ⋙ F' ≅ F ⋙ N_C}
    {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
    {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
    {φ : (Functor.postcompose₂.obj F).obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T_C}
    {φ' : (Functor.postcompose₂.obj F').obj T_D' ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj T_C'}
    {m_C : (Functor.postcompose₂.obj N_C).obj T_C ≅
      (((Functor.whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C'}
    {m_D : (Functor.postcompose₂.obj N_D).obj T_D ≅
      (((Functor.whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D'}
    (H : Adjunction.ComparisonCompatible α φ φ' m_C m_D)
    {β : G ⋙ N_D ⟶ N_C ⋙ G'} (hβ : mateEquiv adj adj' α.hom = β) (K : C) (M : D)
    [hπ : IsIso (((adj.rightAdjointProjectionMap φ).app K).app M)]
    [IsIso (β.app K)] [IsIso (β.app ((T_C.obj K).obj (F.obj M)))] :
    IsIso (((adj'.rightAdjointProjectionMap φ').app (N_C.obj K)).app (N_D.obj M)) := by
  subst β
  exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv adj adj' H K M

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The tensor comparison `T(K ⊗ᴸ M) ≅ T K ⊗ᴸ T M` of the derived extension of scalars
`T = L(Ext_{a_X})`, as an isomorphism of bifunctors: the tensor comparison
`Functor.leftDerivedTensorComparison` of the strong monoidal functor `Ext_{a_X}`
(`Mod.extendScalarsMonoidal`). -/
noncomputable def derivedExtendScalarsTensorIso (X : Scheme.{u}) :
    (Functor.postcompose₂.obj (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).obj
        (curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)))) ≅
      (((Functor.whiskeringLeft₂ _).obj
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).obj
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).obj
          (curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj Λ' X)))) :=
  letI := Mod.extendScalarsMonoidal (coefficientMap a X)
  asIso (Mod.extendScalars (coefficientMap a X)).leftDerivedTensorComparison

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived (Pull) isomorphism `Lf^* ⋙ T ≅ T ⋙ Lf^*` is compatible with the tensor
comparisons of the derived pullbacks (`leftDerivedUpperStarTensor`) and of the derived extensions
of scalars (`derivedExtendScalarsTensorIso`): it is the isomorphism of composites of left derived
functors induced by the underived (Pull) isomorphism
(`derivedPullIso_eq_leftDerivedFunctorCompNatIso`), which is monoidal
(`isMonoidal_pullIso_hom`), so this is
`Functor.map_leftDerivedTensorComparison_comp_eq_of_iso`. -/
theorem comparisonCompatible_derivedPullIso :
    Adjunction.ComparisonCompatible (derivedPullIso a f).symm
      (leftDerivedUpperStarTensor Λ f) (leftDerivedUpperStarTensor Λ' f)
      (derivedExtendScalarsTensorIso a X) (derivedExtendScalarsTensorIso a Y) := by
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  let := Mod.extendScalarsMonoidal (coefficientMap a Y)
  have := isMonoidal_pullIso_hom a f
  refine comparisonCompatible_symm_of_tensorComparison (derivedPullIso a f) _ _ _ _
    (derivedPullIso_eq_leftDerivedFunctorCompNatIso a f)
    (leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f)
    (leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ' f) ?_
  exact Functor.map_leftDerivedTensorComparison_comp_eq_of_iso
    (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ (f)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X)) (pullIso a f)

/-- **The projection formula under a flat change of coefficients**: if the projection map
`Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ Lf^* M)` with coefficients `Λ` is an isomorphism at `(K, M)` and the
(Push) comparison `T Rf_* ⟶ Rf_* T` is an isomorphism at `K` and at `K ⊗ᴸ Lf^* M`, then the
projection map with coefficients `Λ'` is an isomorphism at `(T K, T M)`. -/
theorem isIso_projectionMap_app_app_extendScalars
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    [IsIso (((projectionMap Λ f).app K).app M)]
    [IsIso ((derivedPushHom a f).app K)]
    [IsIso ((derivedPushHom a f).app
      (((curriedTensor _).obj K).obj (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M)))] :
    IsIso (((projectionMap Λ' f).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)).app
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M)) := by
  exact isIso_projectionMap_of_mate_eq
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ' f)
    (comparisonCompatible_derivedPullIso a f) (derivedPushHom_eq_mateEquiv a f).symm K M
    (hπ := (inferInstance : IsIso (((projectionMap Λ f).app K).app M)))

end AlgebraicGeometry.ProEtale.CondensedRing
