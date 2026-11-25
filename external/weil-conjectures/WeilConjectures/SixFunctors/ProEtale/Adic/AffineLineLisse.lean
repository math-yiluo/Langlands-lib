/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarUnit
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.AffineLineConstant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance

/-!
# Homotopy invariance for lisse `ℓ`-adic sheaves

Let `k` be an algebraically closed field in which `ℓ` is invertible, `X` a `k`-scheme locally of
finite type and `π : Y ⟶ X` isomorphic over `X` to the affine line `𝔸¹_X ⟶ X`. For a lisse
`ℓ`-adic sheaf `L` on `X`, the unit `L ⟶ Rπ_* π^* L` of the derived adjunction `π^* ⊣ Rπ_*` of
`ℓ`-adic sheaves is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_adicUnit_app_singleFunctor_of_isAdicLisseSheaf`).

The invertibility of a unit only depends on the left adjoint
(`CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app_obj`), so the claim may be checked in
the condensed model of `ℓ`-adic complexes and for the affine line `𝔸¹_X` itself. There the unit
is pro-étale local (`ProEtale.CondensedRing.isIso_affineLineUnit_app_of_cover`): on an affine open
`U` of `X`, the unit is invertible at the constant sheaf `ℚ̄_ℓ`
(`ProEtale.CondensedRing.isIso_affineLineUnit_app_tensorUnit_padicAlgCl`), hence at the module
objects which are pro-étale locally finite direct sums of copies of `ℚ̄_ℓ`, as the lisse sheaves
are (`ProEtale.CondensedRing.isIso_affineLineUnit_app_singleFunctor_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {l : ℕ} [Fact l.Prime]

/-- **A lisse `ℓ`-adic sheaf in the condensed model**: for a lisse `ℓ`-adic sheaf `L`, the
corresponding module object over `ℚ̄_ℓ` is pro-étale locally a finite direct sum of copies of the
unit. -/
lemma IsAdicLisseSheaf.exists_cover_upperStar_condensedMod_iso {X : Scheme.{u}}
    {L : AdicSheaf l X} (hL : IsAdicLisseSheaf L) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i, ∃ n : ℕ,
      Nonempty ((𝒰.f i)^*⟦Profinite.padicAlgClRingObj l⟧.obj
        ((adicSheafEquivCondensedMod l X).functor.obj L) ≅ ⨁ fun _ : Fin n ↦ 𝟙_ _) := by
  obtain ⟨R, hR, hRL⟩ := hL
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X := ⟨⟨ι, V, f⟩, hR⟩
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  refine ⟨C.restrictIndexOfSmall.{u}, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hRL (f (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i))
    (.mk _)
  refine ⟨n, ⟨((adicUpperStarCompCondensedModIso l _).app L).symm ≪≫
    (adicSheafEquivCondensedMod l _).functor.mapIso e ≪≫
    (adicSheafEquivCondensedMod l _).functor.mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ adicSheafEquivCondensedModTensorUnitIso l _⟩⟩

namespace CondensedRing

/-- **Homotopy invariance for lisse sheaves in the condensed model.** Let `X` be locally of finite
type over an algebraically closed field `k` in which `ℓ` is invertible, and `L` a lisse `ℓ`-adic
sheaf on `X`. The unit of the affine line `𝔸¹_X ⟶ X` is invertible at the module object over
`ℚ̄_ℓ` corresponding to `L`, placed in degree `0`. -/
theorem isIso_affineLineUnit_app_singleFunctor_of_isAdicLisseSheaf {k : Type u} [Field k]
    [IsAlgClosed k] (hl : IsUnit (l : k)) {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] {L : AdicSheaf l X} (hL : IsAdicLisseSheaf L) :
    IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((adicSheafEquivCondensedMod l X).functor.obj L))) := by
  refine isIso_affineLineUnit_app_of_openCover _ X.affineCover _ fun a ↦ ?_
  let j := X.affineCover.f a
  have : IsSeparated (j ≫ aX) := inferInstance
  have : QuasiCompact (j ≫ aX) := inferInstance
  have := isIso_affineLineUnit_app_tensorUnit_padicAlgCl l (j ≫ aX) hl
  obtain ⟨𝒰, h𝒰⟩ := IsAdicLisseSheaf.exists_cover_upperStar_condensedMod_iso (hL.upperStar j)
  have := isIso_affineLineUnit_app_singleFunctor_of_cover _
    ((adicSheafEquivCondensedMod l _).functor.obj ((j)^*ᵃ[l].obj L)) 𝒰 h𝒰
  let e : (L((j)^*⟦Profinite.padicAlgClRingObj l⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafEquivCondensedMod l X).functor.obj L)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l _).functor.obj ((j)^*ᵃ[l].obj L)) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
      ((j)^*⟦Profinite.padicAlgClRingObj l⟧.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso ((adicUpperStarCompCondensedModIso l j).app L).symm
  exact (NatTrans.isIso_app_iff_of_iso _ e).2 this

end CondensedRing

/-- **Homotopy invariance for lisse `ℓ`-adic sheaves.** Let `X` be locally of finite type over
an algebraically closed field `k` in which `ℓ` is invertible, `π : Y ⟶ X` isomorphic over `X` to
the affine line `𝔸¹_X ⟶ X`, and `L` a lisse `ℓ`-adic sheaf on `X`. Then the unit
`L ⟶ Rπ_* π^* L` of the derived adjunction `π^* ⊣ Rπ_*` of `ℓ`-adic sheaves is an isomorphism. -/
theorem isIso_adicUnit_app_singleFunctor_of_isAdicLisseSheaf {k : Type u} [Field k]
    [IsAlgClosed k] (hl : IsUnit (l : k)) {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] (π : Y ⟶ X) (e : Y ≅ 𝔸(ULift.{u} (Fin 1); X))
    (he : e.hom ≫ (𝔸(ULift.{u} (Fin 1); X) ↘ X) = π) {L : AdicSheaf l X}
    (hL : IsAdicLisseSheaf L) :
    IsIso ((adicUpperStarLowerStarAdjunction l π).mapDerivedCategoryRightDerivedAdjunction.unit.app
      ((DerivedCategory.singleFunctor _ 0).obj L)) := by
  let Λ := Profinite.padicAlgClRingObj l
  let p := 𝔸(ULift.{u} (Fin 1); X) ↘ X
  -- the condensed unit of the affine line, at the module object of `L`
  have hp := CondensedRing.isIso_affineLineUnit_app_singleFunctor_of_isAdicLisseSheaf hl aX hL
  -- the condensed unit of `π`: `Lπ^* ⋙ Le⁻¹^* ≅ Lp^*`, with `Le⁻¹^*` an equivalence
  have := CondensedRing.isEquivalence_upperStar_of_isUniversalHomeomorphism Λ e.inv
  have : (L((e.inv)^*⟦Λ⟧)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  have : IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ p).unit.app
      ((𝟭 _).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l X).functor.obj L)))) := hp
  have hπ : IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ π).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafEquivCondensedMod l X).functor.obj L))) :=
    Adjunction.isIso_unit_app_of_isIso_unit_app_obj _
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ p) (𝟭 _) (L((e.inv)^*⟦Λ⟧))
      ((CondensedRing.leftDerivedUpperStarComp Λ e.inv π).symm ≪≫
        eqToIso (by rw [← he, Iso.inv_hom_id_assoc]) ≪≫
        (Functor.leftUnitor _).symm) _
  -- from the condensed model to `ℓ`-adic sheaves
  have : IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ π).unit.app
      ((adicSheafDerivedEquivCondensedMod l X).functor.obj
        ((DerivedCategory.singleFunctor _ 0).obj L))) :=
    (NatTrans.isIso_app_iff_of_iso _
      ((singleFunctorCompAdicSheafDerivedEquivCondensedModIso l X 0).app L)).2 hπ
  exact Adjunction.isIso_unit_app_of_isIso_unit_app_obj _
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ π)
    (adicSheafDerivedEquivCondensedMod l X).functor (adicSheafDerivedEquivCondensedMod l Y).functor
    (adicUpperStarMapDerivedCategoryCompIso l X π ≪≫ Functor.isoWhiskerLeft _
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ π).symm) _

end AlgebraicGeometry.ProEtale
