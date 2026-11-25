/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import all WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# The unit of `t^* ⊣ Rt_*` at complexes with constant cohomology over a strictly henselian ring

Let `R` be a strictly henselian local ring, `Y = Spec R` with closed point
`s₀ : Spec κ ⟶ Y` and `t : Spec Ω ⟶ Y` a morphism from the spectrum of a separably closed field.
For a bounded below complex `G` of étale sheaves of `Λ`-modules on `Y` all of whose cohomology
sheaves are constant, the pullback to the closed point of the unit `G ⟶ Rt_* t^* G` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_app_of_isConstant_homology`).
This is the case of a single constant sheaf
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing`)
extended by dévissage along the truncation triangles
(`DerivedCategory.Plus.isIso_app_of_forall_homology`); both `s₀^*` and `s₀^* Rt_* t^*` are left
`t`-exact.

Moreover every bounded below complex on `Spec Ω` is the pullback of such a complex on `Y`
(`AlgebraicGeometry.Etale.exists_isConstant_homology_iso_upperStar_obj`): sheaves on the
separably closed point are constant (`constantSheafEquivalenceOfIsSepClosed`), and pullbacks of
constant sheaves are constant (`AlgebraicGeometry.Etale.constantSheafCompUpperStarIso`). The
property of having constant cohomology sheaves is stable under pullback
(`AlgebraicGeometry.Etale.isConstant_homology_upperStar_obj`).

In the language of nearby cycles: for a strictly henselian trait `Y` with geometric generic point
`t`, the nearby cycles `s₀^* Rt_*` of the constant complex `t^* G` are `s₀^* G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The étale pullback `D+(f^*)` does not lower the cohomological degree: it commutes with the
cohomology sheaves. -/
lemma Etale.isGE_mapDerivedCategoryPlus_upperStar_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] : (D+((f)^*[ModuleCat.{u + 1} Λ]).obj K).IsGE n := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro i hi
  refine IsZero.of_iso ?_
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso i |>.app _).symm
  exact Functor.map_isZero (f)^*[ModuleCat.{u + 1} Λ]
    (DerivedCategory.Plus.isZero_homology_of_isGE K n i hi)

/-- The cohomology sheaves of a pullback of a complex with constant cohomology sheaves are
constant. -/
lemma Etale.isConstant_homology_upperStar_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : ∀ q, Sheaf.IsConstant Y.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj G)) (q : ℤ) :
    Sheaf.IsConstant X.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (D+((f)^*[ModuleCat.{u + 1} Λ]).obj G)) := by
  obtain ⟨M, ⟨e⟩⟩ := (hG q).mem_essImage
  exact Sheaf.isConstant_of_iso _
    (((((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).app G).symm ≪≫
      ((f)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫
      (Etale.constantSheafCompUpperStarIso Λ f).app M)

/-- **The unit at complexes with constant cohomology over a strictly henselian local ring.** Let
`R` be a strictly henselian local ring with closed point `s₀ : Spec κ ⟶ Spec R` and
`t : Spec Ω ⟶ Spec R` a morphism from the spectrum of a separably closed field. For every bounded
below complex `G` of étale sheaves of `Λ`-modules on `Spec R` whose cohomology sheaves are
constant, the pullback along `s₀` of the unit `G ⟶ Rt_* t^* G` is an isomorphism. -/
theorem Etale.isIso_upperStar_map_unit_app_of_isConstant_homology
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
    (G : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : ∀ q, Sheaf.IsConstant (Spec (.of R)).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj G)) :
    IsIso (D+((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app G)) := by
  rw [Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  have := derivedUnit_commShift (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t)
  let P : ObjectProperty (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun F ↦ Sheaf.IsConstant _ F
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    have : Sheaf.IsConstant _ _ := h
    Sheaf.isConstant_congr _ e⟩
  refine DerivedCategory.Plus.isIso_app_of_forall_homology
    (Functor.whiskerRight (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).derivedPlus.unit
      D+((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ])) P
    (fun F hF ↦ ?_) (fun K n _ q hq ↦ ?_) (fun K n _ q hq ↦ ?_) G hG
  · obtain ⟨M, ⟨e⟩⟩ := hF.mem_essImage
    have h := Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing Λ R t M
    rw [Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at h
    rw [← NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e)]
    exact h
  · have := Etale.isGE_mapDerivedCategoryPlus_upperStar_obj Λ
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) K n
    exact DerivedCategory.Plus.isZero_homology_of_isGE
      (D+((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ]).obj K)
      n q hq
  · have := Etale.isGE_mapDerivedCategoryPlus_upperStar_obj Λ t K n
    refine IsZero.of_iso ?_ (((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[
      ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q |>.app _).symm
    exact Functor.map_isZero ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[
      ModuleCat.{u + 1} Λ]) (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((t)_*[ModuleCat.{u + 1} Λ]) (D+((t)^*[ModuleCat.{u + 1} Λ]).obj K) n hq)

/-- **Complexes on a separably closed point are pulled back from complexes with constant
cohomology**: for any morphism `t : Spec Ω ⟶ Y` from the spectrum of a separably closed field,
every bounded below complex `L` of étale sheaves of `Λ`-modules on `Spec Ω` is isomorphic to
`t^* G` for a bounded below complex `G` on `Y` whose cohomology sheaves are constant (namely the
constant complex on the global sections of `L`). -/
theorem Etale.exists_isConstant_homology_iso_upperStar_obj {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (L : DerivedCategory.Plus (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ q, Sheaf.IsConstant Y.smallEtaleTopology
        ((DerivedCategory.Plus.homologyFunctor _ q).obj G)) ∧
      Nonempty (D+((t)^*[ModuleCat.{u + 1} Λ]).obj G ≅ L) := by
  let E := constantSheafEquivalenceOfIsSepClosed Λ (k := Ω)
  have : E.inverse.Additive := additive_sheafSections_obj Λ _
  have : E.functor.Additive := additive_constantSheaf Λ _
  have : PreservesFiniteColimits (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteColimits (Functor.const _) (presheafToSheaf _ _)
  have : PreservesFiniteLimits (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)
  have : PreservesFiniteColimits
      (constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteColimits (Functor.const _) (presheafToSheaf _ _)
  have : PreservesFiniteLimits
      (constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)
  refine ⟨D+(constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (D+(E.inverse).obj L), fun q ↦ Sheaf.isConstant_of_iso _
      (((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).mapDerivedCategoryPlusHomologyFunctorIso q).app _).symm, ⟨?_⟩⟩
  exact ((Functor.mapDerivedCategoryPlusCompIso _ _).app _).symm ≪≫
    (Functor.mapDerivedCategoryPlusNatIso (Etale.constantSheafCompUpperStarIso Λ t)).app _ ≪≫
    ((Functor.mapDerivedCategoryPlusCompIso E.inverse E.functor).app L).symm ≪≫
    (Functor.mapDerivedCategoryPlusNatIso E.counitIso).app L ≪≫
    (Functor.mapDerivedCategoryPlusIdIso _).app L

end AlgebraicGeometry
