/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.DualFinite
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# Lisse flat sheaves are dualizable

Let `Λ` be a finite commutative ring and `F` a finite locally constant (lisse) sheaf of
`Λ`-modules on the small étale site of a scheme `X` which is flat. Then `F` is dualizable, with
left dual its internal dual `F^∨ = [F, Λ_X]`
(`AlgebraicGeometry.Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf`).

By the criterion `CategoryTheory.MonoidalClosed.exactPairingOfIsIso` it suffices that the
comparison map `[F, Λ] ⊗ F ⟶ [F, F]` is an isomorphism. This is checked after pullback to the
members of a trivialising étale cover, pullback along an étale morphism being monoidal and
commuting with internal homs (`AlgebraicGeometry.Etale.isIso_ihomComparison_upperStar`). There
`F` is the constant sheaf at its stalk `M`, a finitely generated flat, hence finite projective,
`Λ`-module; `M` is dualizable in `ModuleCat Λ`, and so is the constant sheaf at `M`, the
constant sheaf functor being monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

/-- If a lisse flat sheaf of modules over a finite ring on a nonempty scheme is the constant sheaf
at `M`, then `M` is dualizable: it is the stalk, hence finitely generated and flat, hence finite
projective. -/
lemma isDualizable_of_constantSheaf_iso [Nonempty X] {M : ModuleCat.{u + 1} Λ}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (eM : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ F)
    [hFl : IsFiniteLocallyConstantSheaf F] (hF : ObjectProperty.flat F) : IsDualizable M := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let t := X.algClosurePoint (Classical.arbitrary X)
  have hfin : Module.Finite Λ M := by
    have := hFl.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber _ t
    rw [ConcreteCategory.isFinitelyGenerated_iff_of_iso
      ((pointSmallEtale t).sheafFiber.mapIso eM.symm ≪≫
        (pointSmallEtale t).sheafFiberConstantSheafIso M),
      ModuleCat.isFinitelyGenerated_iff] at this
    exact this
  have hflat : Module.Flat Λ M := by
    let Φ := (pointSmallEtale t).ulift.{u + 1}
    have := Φ.flat_sheafFiber_obj hF
    rw [← ModuleCat.flat_iff_flat]
    exact ObjectProperty.prop_of_iso _
      (Φ.sheafFiber.mapIso eM.symm ≪≫ Φ.sheafFiberConstantSheafIso M) this
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
  have : Module.Projective Λ M := Module.Flat.projective_of_finitePresentation
  exact ModuleCat.isDualizable_of_projective M

/-- A lisse flat sheaf of modules over a finite ring is dualizable, provided it is constant. -/
lemma isDualizable_of_isConstant_of_flat (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] [F.IsConstant X.smallEtaleTopology]
    (hF : ObjectProperty.flat F) : IsDualizable F := by
  by_cases hX : IsEmpty X
  · exact IsDualizable.of_iso
      (IsZero.iso (Etale.isZero_sheaf_of_isEmpty _) (Etale.isZero_sheaf_of_isEmpty _))
      isDualizable_unit
  rw [not_isEmpty_iff] at hX
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨M, ⟨eM⟩⟩ := F.mem_essImage_of_isConstant
  obtain ⟨_⟩ := isDualizable_of_constantSheaf_iso eM hF
  exact IsDualizable.of_iso eM
    ⟨{ rightDual := _
       exact := ExactPairing.map (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) M Mᘁ }⟩

/-- **A lisse flat sheaf is dualizable**: for a finite ring `Λ` and a finite locally constant
flat sheaf `F` of `Λ`-modules on `X_ét`, the comparison map `[F, Λ] ⊗ F ⟶ [F, F]` is an
isomorphism. -/
theorem isIso_ihomUnitTensorToIhom_of_isFiniteLocallyConstantSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hF : ObjectProperty.flat F) :
    IsIso (ihomUnitTensorToIhom F F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  refine isIso_of_isIso_localizationRestriction (ModuleCat.{u + 1} Λ) _ 𝒰.f
    (Set.eq_univ_of_forall fun x ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  let G := (𝒰.f i)^*[ModuleCat.{u + 1} Λ]
  let r := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) (𝒰.f i) inferInstance
  suffices IsIso (G.map (ihomUnitTensorToIhom F F)) by
    have h := r.hom.naturality (ihomUnitTensorToIhom F F)
    rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h
    rw [← h]
    infer_instance
  have : (G.obj F).IsConstant (𝒰.X i).smallEtaleTopology :=
    (isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) F).1 (h𝒰 i)
  have : IsFiniteLocallyConstantSheaf (G.obj F) := IsFiniteLocallyConstantSheaf.upperStar _ F
  obtain ⟨_⟩ := isDualizable_of_isConstant_of_flat (G.obj F)
    (Functor.PreservesFlat.flat_obj (F := G) hF)
  obtain ⟨_⟩ := Nonempty.intro (BraidedCategory.exactPairing_swap (G.obj F) (G.obj F)ᘁ)
  have := isIso_ihomUnitTensorToIhom (G.obj F)ᘁ (G.obj F) (G.obj F)
  have := isIso_ihomComparison_upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i) F
  exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison G F F

/-- **A lisse flat sheaf is dualizable**: for a finite ring `Λ`, a finite locally constant flat
sheaf `F` of `Λ`-modules on `X_ét` has the left dual `[F, Λ_X]`, the evaluation being the
evaluation of the internal hom. -/
@[instance_reducible]
noncomputable def exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hF : ObjectProperty.flat F) :
    ExactPairing ((ihom F).obj (𝟙_ _)) F :=
  have := isIso_ihomUnitTensorToIhom_of_isFiniteLocallyConstantSheaf F hF
  exactPairingOfIsIso F

/-- **The internal dual of a lisse flat sheaf is lisse**: for a finite ring `Λ` and a finite
locally constant flat sheaf `F` of `Λ`-modules on `X_ét`, the dual `[F, Λ_X]` is finite locally
constant. On a trivialising étale cover, where `F` is the constant sheaf at a finite projective
module `M`, the pullback of `[F, Λ_X]` is `[M_W, Λ_W]`, the constant sheaf at the dual of `M`;
its stalks are dualizable modules, hence finitely generated
(`ModuleCat.finite_of_exactPairing`). -/
theorem isFiniteLocallyConstantSheaf_ihom_unit_of_flat
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hF : ObjectProperty.flat F) :
    IsFiniteLocallyConstantSheaf ((ihom F).obj (𝟙_ _)) where
  toIsLocallyConstantSheaf := by
    have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    rw [isConstant_over_iff_upperStar]
    let G := (𝒰.f i)^*[ModuleCat.{u + 1} Λ]
    change Sheaf.IsConstant (𝒰.X i).smallEtaleTopology (G.obj ((ihom F).obj (𝟙_ _)))
    have : (G.obj F).IsConstant (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) F).1 (h𝒰 i)
    have : IsFiniteLocallyConstantSheaf (G.obj F) := IsFiniteLocallyConstantSheaf.upperStar _ F
    by_cases hW : IsEmpty (𝒰.X i)
    · exact Sheaf.isConstant_of_iso _ (X := 𝟙_ (ModuleCat.{u + 1} Λ))
        (IsZero.iso (Etale.isZero_sheaf_of_isEmpty _) (Etale.isZero_sheaf_of_isEmpty _))
    rw [not_isEmpty_iff] at hW
    obtain ⟨M, ⟨eM⟩⟩ := (G.obj F).mem_essImage_of_isConstant
    obtain ⟨_⟩ := isDualizable_of_constantSheaf_iso eM
      (Functor.PreservesFlat.flat_obj (F := G) hF)
    let _ : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    let _ := ExactPairing.map (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      Mᘁ M
    have := isIso_ihomComparison_upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i) F
    exact Sheaf.isConstant_of_iso _ (X := Mᘁ)
      (asIso ((Functor.LaxMonoidal.ihomComparison G F).app (𝟙_ _)) ≪≫
        (ihom (G.obj F)).mapIso (Functor.Monoidal.εIso G).symm ≪≫
        ihomIsoOfIsoLeft eM.symm _ ≪≫ ihomObjUnitIso _ _)
  toIsFiniteSheaf := by
    let _ := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf F hF
    refine ⟨fun Ω _ _ s ↦ ?_⟩
    let Φ := (pointSmallEtale s).ulift.{u + 1}
    let _ := ExactPairing.map Φ.sheafFiber ((ihom F).obj (𝟙_ _)) F
    have := ModuleCat.finite_of_exactPairing (Φ.sheafFiber.obj ((ihom F).obj (𝟙_ _)))
      (Φ.sheafFiber.obj F)
    exact (((ModuleCat.isFinitelyGenerated_iff _).2 this).of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app _))

end Etale

end AlgebraicGeometry
