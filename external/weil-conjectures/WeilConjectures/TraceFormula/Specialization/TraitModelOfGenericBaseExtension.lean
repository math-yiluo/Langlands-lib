/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.TraceFormula.Specialization.TraitProduct
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase

/-!

# Extending the coefficients of a trait model over the generic base to its total space

Let `M` be a trait model of `X₁` over the generic base
(`NearbyCyclesModel.IsTraitModelOfGenericBase`):
its generic fibre `𝒳_η` is an open of `X₁ ×_F η`, and the identification `ε` of its geometric
generic fibre factors through `𝒳_η ⟶ X₁`. For a bounded constructible complex `A` on `X₁`, the
extension by zero along the open immersion `𝒳_η ⟶ 𝒳` of the pullback of `A` to `𝒳_η` is a
bounded constructible complex `B` on the total space with `j^* B ≅ ε^* A`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_extension_total`). This is the form of the
coefficients required by the generic-slicing identification
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- **Extension by zero of coefficients pulled back to an open**: let `v : U ⟶ T` be an open
immersion into a noetherian scheme, and `j = s ≫ v`, `ε = s ≫ e` two morphisms factoring through
`s : G ⟶ U`. For a bounded constructible complex `A` on `X`, the extension by zero
`B = v_! Le^* A` is bounded constructible on `T` with `Lj^* B ≅ Lε^* A`, as `Lv^* v_! ≅ 𝟭`. -/
theorem exists_boundedConstructible_leftDerivedUpperStar_obj_iso_of_isOpenImmersion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {G U T X : Scheme.{u}} (v : U ⟶ T) [IsOpenImmersion v] [TopologicalSpace.NoetherianSpace T]
    (s : G ⟶ U) (e : U ⟶ X) {j : G ⟶ T} {ε : G ⟶ X} (hj : s ≫ v = j) (hε : s ≫ e = ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A) :
    ∃ B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)),
      boundedConstructible (condensedRingObj Λ T) B ∧
        Nonempty (L((j)^*⟦Λ⟧).obj B ≅ L((ε)^*⟦Λ⟧).obj A) := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (openImmersionLowerShriekUpperStarAdjunction Λ v)
  refine ⟨_, boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ v _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ e A hA), ⟨?_⟩⟩
  exact (leftDerivedUpperStarCompOfEq Λ hj).app _ ≪≫
    (L((s)^*⟦Λ⟧)).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ v).app _ ≪≫
        (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).unit.app _)).symm) ≪≫
    ((leftDerivedUpperStarCompOfEq Λ hε).app A).symm

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The coefficients extend to the total space**: for a trait model `M` of `X₁` over the
generic base and a bounded constructible complex `A` on `X₁`, there is a bounded constructible
complex `B` on the total space `𝒳` with `j^* B ≅ ε^* A`: the extension by zero, along the open
immersion `𝒳_η ⟶ 𝒳` of the generic fibre, of the pullback of `A` along `𝒳_η ⟶ X₁`. -/
theorem IsTraitModelOfGenericBase.exists_extension_total
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj Λ X₁.left))}
    (hA : boundedConstructible (condensedRingObj Λ X₁.left) A) :
    ∃ B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
        (condensedRingObj Λ M.total)),
      boundedConstructible (condensedRingObj Λ M.total) B ∧
        Nonempty (L((M.j)^*⟦Λ⟧).obj B ≅ L((M.ε)^*⟦Λ⟧).obj A) := by
  obtain ⟨w, -, -, hw⟩ := h.exists_openImmersion_genericFibre
  have := h.isTraitModelOver.isTraitModel.isNoetherian_total
  exact exists_boundedConstructible_leftDerivedUpperStar_obj_iso_of_isOpenImmersion Λ
    (pullback.fst q (traitGenericSpec k'))
    (genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w) (w ≫ pullback.fst _ _)
    (genericFibreInclusion_fst M q g h.isTraitModelOver.isPullback_j.w) hw hA

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
