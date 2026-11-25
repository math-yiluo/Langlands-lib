/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.SupportsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-!
# The triangle of sections with support on module objects, and filtered colimits

Let `Λ` be a commutative condensed ring such that `Λ_X = condensedRingObj Λ X` is flat, and
`j : U ⟶ X` a quasi-compact open immersion. On module objects over `Λ_X`, the short complex of
functors `Γ_Z ⟶ 𝟭 ⟶ j_* j^*` (`ProEtale.CondensedRing.sectionsWithSupportShortComplex`) is short
exact on injective objects: the restriction `I ⟶ j_* j^* I` of an injective module object is an
epimorphism (`ProEtale.CondensedRing.epi_upperStarLowerStarAdjunction_unit_app_of_injective`), so
its right derived functors form a natural distinguished triangle
`RΓ_Z K ⟶ K ⟶ Rj_* j^* K ⟶`.

The cohomology sheaves of the last two terms, evaluated on module objects placed in degree `0`,
commute with `u + 1`-small filtered colimits: for `j_* j^*` because the higher direct images of
abelian pro-étale sheaves along a quasi-compact quasi-separated morphism do
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`, blueprint
`corollary-continuity-cohomology--2`), and the underlying abelian sheaves of the derived
pushforward of module objects are the derived pushforward of the underlying abelian sheaves
(`ProEtale.CondensedRing.rightDerivedLowerStarCompMapDerivedCategoryForgetIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- The short complex of functors `Γ_Z ⟶ 𝟭 ⟶ j_* j^*` on module objects over `Λ_X`. -/
noncomputable def sectionsWithSupportShortComplex :
    ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ShortComplex.mk (sectionsWithSupportι Λ j) (upperStarLowerStarAdjunction Λ j).unit
    (by ext N : 2; exact sectionsWithSupportι_app_comp_unit_app Λ j N)

variable [IsOpenImmersion j] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

/-- For a flat `Λ_X`, the restriction `I ⟶ j_* j^* I` of an injective module object along an open
immersion is an epimorphism: on underlying abelian sheaves it is the restriction of an injective
abelian sheaf
(`AlgebraicGeometry.ProEtale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`). -/
lemma epi_upperStarLowerStarAdjunction_unit_app_of_injective
    (I : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) [Injective I] :
    Epi ((upperStarLowerStarAdjunction Λ j).unit.app I) := by
  let F := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : Injective (F.obj I) := F.injective_obj_of_injective ‹_›
  have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective Ab.{u + 1} j (F.obj I)
  have : Epi (F.map ((upperStarLowerStarAdjunction Λ j).unit.app I)) := by
    rw [forget_map_upperStarLowerStarAdjunction_unit_app']
    infer_instance
  exact F.epi_of_epi_map this

/-- `0 ⟶ Γ_Z I ⟶ I ⟶ j_* j^* I ⟶ 0` is short exact for injective `I`. -/
lemma shortExactOnInjectives_sectionsWithSupportShortComplex :
    (sectionsWithSupportShortComplex Λ j).ShortExactOnInjectives := fun I _ ↦
  have := epi_upperStarLowerStarAdjunction_unit_app_of_injective Λ j I
  .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (inferInstanceAs (Mono (kernel.ι _))) this

variable [QuasiCompact j]

/-- The cohomology sheaves of `Rj_* j^* (B[0])` commute with `u + 1`-small filtered colimits of
module objects `B`. -/
lemma nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_upperStarLowerStar
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {B : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (c : Cocone B) (hc : IsColimit c) (n : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.homologyFunctor _ n).mapCocone
      ((DerivedCategory.singleFunctor _ 0 ⋙
        ((j)^*⟦Λ⟧ ⋙ (j)_*⟦Λ⟧).rightDerivedFunctor).mapCocone c))) := by
  let F := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let G := (j)^*⟦Λ⟧ ⋙ (j)_*⟦Λ⟧
  let Ψ := DerivedCategory.singleFunctor _ 0 ⋙ G.rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ n
  obtain hn | ⟨k, rfl⟩ : n < 0 ∨ ∃ k : ℕ, n = k :=
    (lt_or_ge n 0).imp_right fun hn ↦ ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
  · have hz (N) : IsZero (Ψ.obj N) :=
      have := G.isGE_rightDerivedFunctor_obj_singleFunctor N
      DerivedCategory.isZero_of_isGE _ 0 n hn
    exact ⟨IsColimit.ofIsZero _ (Functor.isZero _ fun _ ↦ hz _) (hz _)⟩
  have :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).preservesKInjectiveComplexes
  let α : G ⋙ F ≅ F ⋙ (j)^*[Ab.{u + 1}] ⋙ (j)_*[Ab.{u + 1}] :=
    Functor.isoWhiskerLeft (j)^*⟦Λ⟧ (lowerStarForgetIso Λ j).symm ≪≫
      Functor.isoWhiskerRight (upperStarForgetIso Λ j).symm (j)_*[Ab.{u + 1}]
  let e : Ψ ⋙ F ≅ F ⋙ (j)^*[Ab.{u + 1}] ⋙ ((j)_*[Ab.{u + 1}]).rightDerived k :=
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ G.rightDerivedFunctor)
        (F.mapDerivedCategoryHomologyFunctorIso k) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
        (Functor.isoWhiskerRight (G.rightDerivedFunctorCompMapDerivedCategoryIso F).symm _ ≪≫
          Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso α) _ ≪≫
          Functor.isoWhiskerRight (F.mapDerivedCategoryCompRightDerivedFunctorIso _) _ ≪≫
          Functor.isoWhiskerLeft F.mapDerivedCategory (Functor.isoWhiskerRight
            (((j)^*[Ab.{u + 1}]).mapDerivedCategoryCompRightDerivedFunctorIso _) _)) ≪≫
      Functor.isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0)
        (((j)^*[Ab.{u + 1}]).mapDerivedCategory ⋙ ((j)_*[Ab.{u + 1}]).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ k) ≪≫
      Functor.isoWhiskerLeft F
        (Functor.isoWhiskerRight (((j)^*[Ab.{u + 1}]).mapDerivedCategorySingleFunctor 0)
            (((j)_*[Ab.{u + 1}]).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ k) ≪≫
          Functor.isoWhiskerLeft (j)^*[Ab.{u + 1}]
            (((j)_*[Ab.{u + 1}]).singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso k))
  have := preservesColimitsOfShape_rightDerived_lowerStar j I k
  have : PreservesColimitsOfShape I (Ψ ⋙ F) := preservesColimitsOfShape_of_natIso e.symm
  have : ReflectsColimitsOfShape I F := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have := preservesColimitsOfShape_of_reflects_of_preserves (J := I) Ψ F
  exact ⟨isColimitOfPreserves Ψ hc⟩

omit [IsCommMonObj Λ] [IsOpenImmersion j]
  [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))] [QuasiCompact j] in
/-- The cohomology sheaves of `R𝟭 (B[0])` commute with filtered colimits of module objects `B`. -/
lemma nonempty_isColimit_homologyFunctor_mapCocone_rightDerivedFunctor_id
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {B : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (c : Cocone B) (hc : IsColimit c) (n : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.homologyFunctor _ n).mapCocone
      ((DerivedCategory.singleFunctor _ 0 ⋙
        (𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))).rightDerivedFunctor).mapCocone c))) := by
  let M := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let Ψ := DerivedCategory.singleFunctor M 0 ⋙ (𝟭 M).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor M n
  let e : Ψ ≅ DerivedCategory.singleFunctor M 0 ⋙ DerivedCategory.homologyFunctor M n :=
    Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (𝟭 M).rightDerivedFunctorIsoMapDerivedCategory _) ≪≫
      Functor.isoWhiskerRight ((𝟭 M).mapDerivedCategorySingleFunctor 0) _
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hz (N : M) : IsZero (Ψ.obj N) :=
      (DerivedCategory.isZero_of_isGE _ 0 n hn).of_iso (e.app N)
    exact ⟨IsColimit.ofIsZero _ (Functor.isZero _ fun _ ↦ hz _) (hz _)⟩
  · have := preservesColimitsOfShape_of_natIso
      (e ≪≫ DerivedCategory.singleFunctorCompHomologyFunctorIso M 0).symm (J := I)
    exact ⟨isColimitOfPreserves Ψ hc⟩
  · have hz (N : M) : IsZero (Ψ.obj N) :=
      (DerivedCategory.isZero_of_isLE _ 0 n hn).of_iso (e.app N)
    exact ⟨IsColimit.ofIsZero _ (Functor.isZero _ fun _ ↦ hz _) (hz _)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
