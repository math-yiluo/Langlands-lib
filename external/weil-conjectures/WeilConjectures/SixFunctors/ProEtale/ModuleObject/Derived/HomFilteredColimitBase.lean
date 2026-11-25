/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.HomFilteredColimitExt
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-!
# Basic objects of `D(X_proét, Λ)` whose morphisms commute with filtered colimits

Let `Λ` be a commutative condensed ring and `X` a scheme, with coefficient ring
`Λ_X = condensedRingObj Λ X`. We show that the following objects `s` of the derived category of
`Λ_X`-modules satisfy `DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}`, i.e. for every
`u + 1`-small filtered colimit `B = colim Bᵢ` of `Λ_X`-modules and every `n`, the map
`colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is bijective (blueprint
`lemma-continuity-ext-out-constructible-complex--1`, `corollary-continuity-cohomology`):

* the unit `ℤ` of abelian pro-étale sheaves in degree `0`, for `X` qcqs
  (`AlgebraicGeometry.ProEtale.homCommutesWithFilteredColimits_singleFunctor_unit`): the
  morphisms `ℤ[0] ⟶ B[-q]` are the pro-étale cohomology groups `Hᵠ(X, B)`, which commute with
  filtered colimits (`AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_of_isFiltered_small`);
* the regular module `Λ_X` in degree `0`, for `X` qcqs and `Λ_X` flat
  (`CondensedRing.homCommutesWithFilteredColimits_singleFunctor_regular`):
  `Λ_X = Λ_X ⊗ ℤ` is the free module on the unit, and the free-forgetful adjunction consists of
  exact functors when `Λ_X` is flat, the forgetful functor preserving filtered colimits;
* the extension by zero `j_! s` along an open immersion `j` of an object `s` with this property
  (`CondensedRing.homCommutesWithFilteredColimits_openImmersionLowerShriek`),
  `j_!` and `j^*` being exact and `j^*` a left adjoint;
* a dualizable module `L` in degree `0` as soon as the regular module is
  (`AlgebraicGeometry.ProEtale.homCommutesWithFilteredColimits_singleFunctor_of_isDualizable`),
  via the adjunction `- ⊗ L ⊣ - ⊗ Lᘁ` of exact functors which are both left and right adjoints;
* hence every locally free `Λ_X`-module in degree `0`, for `X` qcqs and `Λ_X` flat
  (`CondensedRing.homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj DerivedCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **The unit `ℤ` of abelian pro-étale sheaves on a qcqs scheme, in degree `0`, has morphisms
commuting with filtered colimits.** The morphisms `ℤ[0] ⟶ B[-q]` are the pro-étale cohomology
groups `Hᵠ(X, B) = Extᵠ(ℤ, B)`, which commute with `u + 1`-small filtered colimits on a qcqs
scheme, and the morphisms `ℤ[0] ⟶ B[n]` vanish for `n > 0`. -/
theorem homCommutesWithFilteredColimits_singleFunctor_unit (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    HomCommutesWithFilteredColimits.{u + 1}
      ((singleFunctor (Sheaf (ProEt.topology X) Ab.{u + 1}) 0).obj
        (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}))) :=
  HomCommutesWithFilteredColimits.singleFunctor_obj_of_ext _
    fun _ _ _ _ _ hc k ↦ ProEt.H_map_isColimit_of_isFiltered_small X hc k

/-- **Dualizable modules in degree `0` have morphisms commuting with filtered colimits**, as soon
as the regular module has. For a dual `Lᘁ` of `L`, the functors `- ⊗ L ⊣ - ⊗ Lᘁ` are adjoint and
both exact (each of them is a left and a right adjoint, up to the braiding), the right adjoint
preserves filtered colimits, and `- ⊗ L` sends `R` to `R ⊗ L ≅ L`. -/
theorem homCommutesWithFilteredColimits_singleFunctor_of_isDualizable {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {L : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R} (hL : IsDualizable L)
    (hR : HomCommutesWithFilteredColimits.{u + 1}
      ((singleFunctor (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) 0).obj (Mod.regular R))) :
    HomCommutesWithFilteredColimits.{u + 1}
      ((singleFunctor (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) 0).obj L) := by
  obtain ⟨_⟩ := hL
  let : BraidedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
    @Mod.braidedCategory _ _ _ _ _ _ (sheafSymmetricCategory X) R _ (by assumption)
  let adj := tensorRightAdjunction L Lᘁ
  have := adj.left_adjoint_additive
  have := adj.right_adjoint_additive
  have := adj.isLeftAdjoint
  have := adj.isRightAdjoint
  have := (tensorLeftAdjunction L Lᘁ).isLeftAdjoint
  have := (tensorLeftAdjunction L Lᘁ).isRightAdjoint
  have := preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L)
  have := preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Lᘁ)
  exact (hR.mapDerivedCategory adj fun _ _ _ ↦
      preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Lᘁ)).of_iso
    (((tensorRight L).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (singleFunctor _ 0).mapIso (λ_ L))

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The regular module `A` is the free module `A ⊗ 𝟙` on the unit. -/
private noncomputable def regularIsoFreeUnit {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) [MonObj A] : Mod.regular A ≅ (Mod.free A).obj (𝟙_ C) :=
  Mod.isoMk (ρ_ A).symm (by
    refine (rightUnitor_inv_naturality μ[A]).trans ?_
    rw [rightUnitor_tensor_inv, Category.assoc]
    rfl)

omit [IsCommMonObj Λ] in
/-- **The regular module `Λ_X` in degree `0` has morphisms commuting with filtered colimits**,
for `X` qcqs and `Λ_X` flat. The regular module is the free module `Λ_X ⊗ ℤ` on the unit, the
free-forgetful adjunction consists of exact functors when `Λ_X` is flat, and the forgetful
functor preserves filtered colimits; so this follows from the case of the unit `ℤ`
(`AlgebraicGeometry.ProEtale.homCommutesWithFilteredColimits_singleFunctor_unit`). -/
theorem homCommutesWithFilteredColimits_singleFunctor_regular (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))] :
    HomCommutesWithFilteredColimits.{u + 1}
      ((singleFunctor (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0).obj
        (Mod.regular (condensedRingObj Λ X))) :=
  ((homCommutesWithFilteredColimits_singleFunctor_unit X).mapDerivedCategory
      (Mod.freeForgetAdjunction (condensedRingObj Λ X)) fun _ _ _ ↦ inferInstance).of_iso
    (((Mod.free _).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
      (singleFunctor _ 0).mapIso (regularIsoFreeUnit (condensedRingObj Λ X)).symm)

/-- **Extension by zero along an open immersion preserves objects whose morphisms commute with
filtered colimits.** For an open immersion `j : U ⟶ X`, both `j_!` and `j^*` are exact on module
objects, and `j^*` preserves colimits, being left adjoint to `j_*`. -/
theorem homCommutesWithFilteredColimits_openImmersionLowerShriek {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {s : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))}
    (hs : HomCommutesWithFilteredColimits.{u + 1} s) :
    HomCommutesWithFilteredColimits.{u + 1} (D((j)_!open⟦Λ⟧).obj s) :=
  hs.mapDerivedCategory (openImmersionLowerShriekUpperStarAdjunction Λ j)
    fun _ _ _ ↦ inferInstance

/-- **Locally free modules in degree `0` have morphisms commuting with filtered colimits**, for
`X` qcqs and `Λ_X` flat: a locally free module is dualizable
(`AlgebraicGeometry.ProEtale.IsLocallyFree.isDualizable`), and the regular module has this
property. -/
theorem homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]
    {L : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hL : IsLocallyFree (condensedRingObj Λ X) L) :
    HomCommutesWithFilteredColimits.{u + 1}
      ((singleFunctor (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0).obj
        L) :=
  homCommutesWithFilteredColimits_singleFunctor_of_isDualizable hL.isDualizable
    (homCommutesWithFilteredColimits_singleFunctor_regular Λ X)

end CondensedRing

end AlgebraicGeometry.ProEtale
