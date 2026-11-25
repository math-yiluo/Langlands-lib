/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilObject.Sheaf.StalkUnit
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax

/-! # Monoidality of the canonical point-pullback trivialization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace TestMapMod
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [HasCoequalizers E] [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

@[reassoc]
private theorem mapMod_delta (F : C ⥤ D) [F.Braided]
    [PreservesColimitsOfShape WalkingParallelPair F]
    {R : C} [MonObj R] [IsCommMonObj R] (M N : Mod C R) :
    F.map (Mod.tensorObjπ M N) ≫
        (Functor.OplaxMonoidal.δ (F.mapMod R) M N).hom =
      Functor.OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) := by
  have h := Functor.tensorπ_mapModTensorIso_hom_hom F M N
  have hδ : (Functor.OplaxMonoidal.δ (F.mapMod R) M N).hom =
      (F.mapModTensorIso M N).inv.hom := rfl
  rw [hδ, ← cancel_epi (Functor.LaxMonoidal.μ F M.X N.X), ← Category.assoc, ← h,
    Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom', Category.comp_id,
    Functor.Monoidal.μ_δ_assoc]

@[reassoc]
private theorem comap_delta {R S : C} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (M N : Mod C S) :
    Mod.tensorObjπ M N ≫ (Functor.OplaxMonoidal.δ (Mod.comap φ) M N).hom =
      Mod.tensorObjπ ((Mod.comap φ).obj M) ((Mod.comap φ).obj N) := by
  have h := Mod.tensorπ_comapTensorIso_hom_hom φ M N
  have hδ : (Functor.OplaxMonoidal.δ (Mod.comap φ) M N).hom =
      (Mod.comapTensorIso φ M N).inv.hom := rfl
  rw [hδ, ← h, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom',
    Category.comp_id]

set_option synthInstance.maxHeartbeats 100000 in
-- Relative tensor functor instances require this local elaboration budget.
private theorem mapModComp_monoidal (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Braided] [G.Braided] [H.Braided]
    [F.PreservesEpimorphisms] [G.PreservesEpimorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F]
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesColimitsOfShape WalkingParallelPair H]
    (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ] [IsIso τ]
    (R : C) [MonObj R] [IsCommMonObj R]
    [IsIso (Functor.compAlgHom F G τ R)] :
    NatTrans.IsMonoidal (Functor.mapModCompIso F G τ R).hom := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro M N
  apply Mod.hom_ext
  apply (cancel_epi (G.map (F.map (Mod.tensorObjπ M N)))).mp
  dsimp only [Functor.OplaxMonoidal.comp_δ, Functor.comp_obj,
    Mod.comp_hom', Functor.mapModCompIso_hom_app_hom, Mod.comap_map_hom,
    Functor.mapMod_map_hom]
  simp only [Functor.mapModCompIso_hom_app_hom, Mod.comap_map_hom, Category.assoc]
  erw [τ.naturality_assoc]
  change τ.app (M.X ⊗ N.X) ≫ H.map (Mod.tensorObjπ M N) ≫ _ ≫ _ = _
  erw [mapMod_delta_assoc, comap_delta]
  rw [← G.map_comp_assoc]
  erw [mapMod_delta]
  rw [G.map_comp, Category.assoc]
  erw [mapMod_delta_assoc]
  rw [Mod.tensorObjπ_tensorHom_hom]
  simp only [Functor.mapModCompIso_hom_app_hom]
  have ht : Functor.OplaxMonoidal.δ (F ⋙ G) M.X N.X ≫
        (τ.app M.X ⊗ₘ τ.app N.X) =
      τ.app (M.X ⊗ N.X) ≫ Functor.OplaxMonoidal.δ H M.X N.X := by
    apply (cancel_epi (Functor.LaxMonoidal.μ (F ⋙ G) M.X N.X)).mp
    simp only [Functor.Monoidal.μ_δ_assoc]
    rw [← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]
  simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc, Functor.mapMod] using
    congrArg (fun f ↦ f ≫ Mod.tensorObjπ
      ((Mod.comap (Functor.compAlgHom F G τ R)).obj ((H.mapMod R).obj M))
      ((Mod.comap (Functor.compAlgHom F G τ R)).obj ((H.mapMod R).obj N))) ht.symm

set_option synthInstance.maxHeartbeats 100000 in
-- Tensor instances for both restrictions need this local elaboration budget.
private theorem comap_unit_monoidal [MonoidalClosed C] [HasEqualizers C]
    {R S : C} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    NatTrans.IsMonoidal (show Mod.comap φ ⋙ Mod.comap (asIso φ).inv ⟶ 𝟭 (Mod C S)
      from (Mod.comapEquivalenceOfIsIso φ).unitIso.inv) := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro M N
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Functor.OplaxMonoidal.id_δ,
    Mod.comapEquivalenceOfIsIso_unitIso_inv_app_hom,
    Functor.OplaxMonoidal.comp_δ, Mod.comap_map_hom]
  apply (cancel_epi (Mod.tensorObjπ M N)).mp
  simp only [Category.assoc, Mod.id_hom', Category.comp_id]
  erw [comap_delta_assoc, comap_delta_assoc, Mod.tensorObjπ_tensorHom_hom]
  rw [Mod.comapEquivalenceOfIsIso_unitIso_inv_app_hom,
    Mod.comapEquivalenceOfIsIso_unitIso_inv_app_hom]
  change Mod.tensorObjπ M N ≫ 𝟙 _ =
    (𝟙 M.X ⊗ₘ 𝟙 N.X) ≫ Mod.tensorObjπ M N
  simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]

private theorem extend_comap_monoidal [MonoidalClosed C] [HasEqualizers C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    NatTrans.IsMonoidal (Mod.extendScalarsIsoComapInv φ).hom := by
  have : NatTrans.IsMonoidal (Mod.extendScalarsIsoComapInv φ).symm.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport (Mod.extendScalarsIsoComapInv φ).symm
  exact inferInstanceAs (NatTrans.IsMonoidal (Mod.extendScalarsIsoComapInv φ).symm.inv)

set_option synthInstance.maxHeartbeats 100000 in
-- Composition monoidal instances require this local elaboration budget.
private theorem mapModCompExtend_monoidal [MonoidalClosed E] [HasEqualizers E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Braided] [G.Braided] [H.Braided]
    [F.PreservesEpimorphisms] [G.PreservesEpimorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F]
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesColimitsOfShape WalkingParallelPair H]
    (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ] [IsIso τ]
    (R : C) [MonObj R] [IsCommMonObj R]
    [IsIso (Functor.compAlgHom F G τ R)] :
    NatTrans.IsMonoidal (Functor.mapModCompExtendScalarsIso F G τ R).hom := by
  have := mapModComp_monoidal F G H τ R
  have := extend_comap_monoidal (Functor.compAlgHom F G τ R)
  have := comap_unit_monoidal (Functor.compAlgHom F G τ R)
  dsimp only [Functor.mapModCompExtendScalarsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

end TestMapMod

namespace AlgebraicGeometry.ProEtale.CondensedRing
universe u
open AlgebraicGeometry
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

-- Elaborating sheaf pullback monoidal structures requires this local budget.
private theorem pointComp_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.IsMonoidal (upperStarFromPointModComp Λ f).hom := by
  have : (upperStarFromPoint Y).PreservesEpimorphisms := by
    have : PreservesColimits (upperStarFromPoint Y) :=
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
          (toSpecZ Y))).leftAdjoint_preservesColimits
    infer_instance
  have : ((f)^*[Ab.{u + 1}]).PreservesEpimorphisms := by
    have : PreservesColimits ((f)^*[Ab.{u + 1}]) :=
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).leftAdjoint_preservesColimits
    infer_instance
  rw [show upperStarFromPointModComp Λ f = upperStarFromPointModCompComposite Λ f from rfl]
  exact TestMapMod.mapModCompExtend_monoidal (upperStarFromPoint Y) ((f)^*[Ab.{u + 1}])
    (upperStarFromPoint X) (upperStarFromPointComp f).hom Λ

private theorem cancel_equivalence_monoidal {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] (P : A ⥤ B) [P.Monoidal] [P.IsEquivalence]
    (Q : B ⥤ B) [Q.Monoidal] (c : P ⋙ Q ≅ P) [NatTrans.IsMonoidal c.hom] :
    NatTrans.IsMonoidal
      ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight P.asEquivalence.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ c ≪≫
        P.asEquivalence.counitIso).hom := by
  let : P.asEquivalence.functor.Monoidal := inferInstanceAs P.Monoidal
  let := P.asEquivalence.inverseMonoidal
  have : P.asEquivalence.IsMonoidal := inferInstance
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

/-- The canonical trivialization of point pullback preserves tensor products.
Source: the canonical point equivalence and coefficient comparison
`upperStarFromPointModComp`; latest blueprint,
realified-kernel proof Steps 1--2
(blueprint: lem-fd-point-pullback-trivialization-monoidal).

Proof: write P for pullback from condensed modules and Q for pullback along σ.
The coefficient sheaf comparison P ⋙ Q ≅ P is strong monoidal: its underlying
sheaf comparison is the pullback compositor, and extending scalars along its
coefficient-ring component makes its tensorator the relative tensor comparison.
To verify this, precompose both tensor maps with the extension-of-scalars unit
and the balanced tensor-product projection. The two maps then become the same
underlying pullback tensor map, by the monoidality of the sheaf compositor.
The unit identity is `upperStarFromPointModComp_hom_app_unit`.
Since P is a monoidal equivalence, equip its chosen inverse with the transported
monoidal structure. Its counit and the associators and unitors are monoidal.
The defining composite Q ≅ P⁻¹ ⋙ P ⋙ Q ≅ P⁻¹ ⋙ P ≅ id is therefore monoidal.
This argument includes the zero coefficient ring and every endomorphism σ. -/
theorem point_pullback_trivialization_monoidal {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) :
    NatTrans.IsMonoidal (upperStarIsoIdOfIsSepClosed Λ σ).hom := by
  have := pointComp_monoidal Λ σ
  exact cancel_equivalence_monoidal (upperStarFromPointMod Λ (Spec (.of Ω)))
    (upperStar Λ σ) (upperStarFromPointModComp Λ σ)

end AlgebraicGeometry.ProEtale.CondensedRing
