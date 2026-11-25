/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomFilteredColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyColimitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionsWithSupportHomology

/-!
# Continuity of `Hom` out of a closed pushforward

Let `Λ` be a commutative condensed ring with `Λ_X` flat, `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`. If `Hom(s, -[q])` commutes with filtered colimits of module
objects over `Λ_Z` and `s` is bounded above, then so does `Hom(Ri_* s, -[q])` over `Λ_X`
(`homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion`, blueprint
`lemma-continuity-ext-out-constructible-complex--1`, closed-support step via
`lemma-sections-support-closed-subscheme`).

Indeed `Hom(i_* s, B[q]) = Hom(s, (Ri^! B)[q])`
(`ProEtale.CondensedRing.derivedLowerStarClosedUpperShriekAdjunction`),
`Ri^! B = i^* RΓ_Z B` is concentrated in degrees `≥ 0`, and its cohomology commutes with filtered
colimits: `RΓ_Z B` sits in the natural triangle `RΓ_Z B ⟶ B ⟶ Rj_* j^* B ⟶`, whose last two terms
have this property
(`corollary-continuity-cohomology`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

/-- The cohomology sheaves of `RΓ_Z (B[0])` commute with `u + 1`-small filtered colimits of
module objects `B`. -/
lemma nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_sectionsWithSupport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {B : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (c : Cocone B) (hc : IsColimit c) (n : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.homologyFunctor _ n).mapCocone
      ((DerivedCategory.singleFunctor _ 0 ⋙
        (sectionsWithSupport Λ j).rightDerivedFunctor).mapCocone c))) := by
  have hS := shortExactOnInjectives_sectionsWithSupportShortComplex Λ j
  have : (sectionsWithSupportShortComplex Λ j).X₁.Additive :=
    inferInstanceAs (sectionsWithSupport Λ j).Additive
  have : (sectionsWithSupportShortComplex Λ j).X₂.Additive :=
    inferInstanceAs (𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))).Additive
  have : (sectionsWithSupportShortComplex Λ j).X₃.Additive :=
    inferInstanceAs ((j)^*⟦Λ⟧ ⋙ (j)_*⟦Λ⟧).Additive
  let T := DerivedCategory.Plus.singleFunctor _ 0 ⋙ ShortComplex.rightDerivedTriangle hS
  have e₁ : T ⋙ Triangle.π₁ ≅ DerivedCategory.singleFunctor _ 0 ⋙
      (sectionsWithSupport Λ j).rightDerivedFunctor :=
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
      simp [T, ShortComplex.rightDerivedTriangle]; rfl) :
      T ⋙ Triangle.π₁ ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙ DerivedCategory.Plus.ι) ⋙
        (sectionsWithSupport Λ j).rightDerivedFunctor) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0) _
  have e₂ : T ⋙ Triangle.π₂ ≅ DerivedCategory.singleFunctor _ 0 ⋙
      (𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))).rightDerivedFunctor :=
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
      simp [T, ShortComplex.rightDerivedTriangle]; rfl) :
      T ⋙ Triangle.π₂ ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙ DerivedCategory.Plus.ι) ⋙
        (𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))).rightDerivedFunctor) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0) _
  have e₃ : T ⋙ Triangle.π₃ ≅ DerivedCategory.singleFunctor _ 0 ⋙
      ((j)^*⟦Λ⟧ ⋙ (j)_*⟦Λ⟧).rightDerivedFunctor :=
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
      simp [T, ShortComplex.rightDerivedTriangle]; rfl) :
      T ⋙ Triangle.π₃ ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙ DerivedCategory.Plus.ι) ⋙
        ((j)^*⟦Λ⟧ ⋙ (j)_*⟦Λ⟧).rightDerivedFunctor) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0) _
  have h := DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₁ T
    (fun M ↦ ShortComplex.rightDerivedTriangle_obj_distinguished hS _) c
    (fun m ↦ (nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_id Λ c hc m).map
      fun h ↦ (IsColimit.mapCoconeEquiv (Functor.isoWhiskerRight e₂ _).symm h))
    (fun m ↦ (nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_upperStarLowerStar
      Λ j c hc m).map
      fun h ↦ (IsColimit.mapCoconeEquiv (Functor.isoWhiskerRight e₃ _).symm h)) n
  exact h.map fun h ↦ IsColimit.mapCoconeEquiv (Functor.isoWhiskerRight e₁ _) h

omit [IsClosedImmersion i] in
/-- The cohomology sheaves of `Ri^!₀ (B[0])` commute with `u + 1`-small filtered colimits of
module objects `B`. -/
lemma nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_closedUpperShriek
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {B : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (c : Cocone B) (hc : IsColimit c) (n : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.homologyFunctor _ n).mapCocone
      ((DerivedCategory.singleFunctor _ 0 ⋙
        (closedUpperShriek Λ i j).rightDerivedFunctor).mapCocone c))) := by
  unfold closedUpperShriek
  obtain ⟨h⟩ := nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_sectionsWithSupport
    Λ j c hc n
  have e : DerivedCategory.singleFunctor _ 0 ⋙
      (sectionsWithSupport Λ j ⋙ (i)^*⟦Λ⟧).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ n ≅
      (DerivedCategory.singleFunctor _ 0 ⋙ (sectionsWithSupport Λ j).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ n) ⋙ (i)^*⟦Λ⟧ :=
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (sectionsWithSupport Λ j) (i)^*⟦Λ⟧) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((i)^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (i)^*⟦Λ⟧ :=
    (upperStarLowerStarAdjunction Λ i).leftAdjoint_preservesColimits
  have h' : IsColimit ((i)^*⟦Λ⟧.mapCocone ((DerivedCategory.homologyFunctor _ n).mapCocone
      ((DerivedCategory.singleFunctor _ 0 ⋙
        (sectionsWithSupport Λ j).rightDerivedFunctor).mapCocone c))) :=
    isColimitOfPreserves (i)^*⟦Λ⟧ h
  exact ⟨IsColimit.mapCoconeEquiv e.symm h'⟩

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1`, closed-support step: for a closed
immersion `i` with quasi-compact open complement and `Λ_X` flat, `Ri_*` preserves the bounded above
objects whose morphisms commute with filtered colimits of module objects. -/
theorem homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {s : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))}
    (hs : DerivedCategory.HomCommutesWithFilteredColimits.{u + 1} s) (b : ℤ) [s.IsLE b] :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1} ((R((i)_*⟦Λ⟧)).obj s) := by
  have := preservesFiniteColimits_lowerStar_of_isCompl Λ i j hij
  refine DerivedCategory.HomCommutesWithFilteredColimits.of_iso
    (((i)_*⟦Λ⟧).rightDerivedFunctorIsoMapDerivedCategory.app s).symm ?_
  exact DerivedCategory.HomCommutesWithFilteredColimits.of_adjunction
    (derivedLowerStarClosedUpperShriekAdjunction Λ i j hij) 0
    (fun B ↦ Functor.isGE_rightDerivedFunctor_obj_singleFunctor _ B)
    (fun _ _ _ _ c hc n ↦
      nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_closedUpperShriek
        Λ i j c hc n) hs b

end AlgebraicGeometry.ProEtale.CondensedRing
