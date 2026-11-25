/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCycles
public import WeilConjectures.TraceFormula.Specialization.SupportCompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.DeformationModelNormalCone
public import WeilConjectures.AlgebraicGeometry.NormalBundle

/-!

# Specialization kills complexes supported away from the point

For a closed immersion `g : Z ⟶ X` and an ideal sheaf `I` of `X` with `g⁻¹ I = 𝒪_Z`, the special
fibre of the deformation of `Z` along `g⁻¹ I` is empty, so by proper base change for nearby
cycles `Ψ_X(Rg_* M) ≅ Rg'_* Ψ_Z(M) = 0`. In particular the specialization `Sp_{X,x}` to the
normal cone of a rational point `x` kills `Rg_* M` if `x` is not in the image of `g`
(step (E) of Varshavsky's argument).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme AffineZariskiSite

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {X Z : Over (Spec (.of k))}

/-- On an empty scheme, every complex of module objects over `ℚ̲̄_ℓ` is zero. -/
lemma isZero_derivedCategory_padicAlgCl_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))) : IsZero K := by
  have hA (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) : IsZero M :=
    isZero_of_isZero_X _ (IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) _
      (Functor.isZero _ fun T ↦
        have : IsEmpty T.unop.left := ⟨fun t ↦ IsEmpty.false (α := Y) (T.unop.hom.base t)⟩
        (ProEt.isTerminalSectionsOfIsEmpty M.X T.unop).isZero))
  refine IsZero.of_iso (Functor.map_isZero DerivedCategory.Q ?_)
    (DerivedCategory.Q.objObjPreimageIso K).symm
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun n ↦ (hA _).eq_of_src _ _

/-- The deformation along the unit ideal has empty special fibre: it maps to `V(⊤) = ∅`. -/
lemma isEmpty_deformationSpecialFibre_top :
    IsEmpty (deformationSpecialFibre Z (⊤ : Z.left.IdealSheafData) k').left := by
  have : IsEmpty (⊤ : Z.left.IdealSheafData).quotientSpec := by
    rw [← Scheme.Hom.ker_eq_top_iff_isEmpty
      (relativeGluingData (⊤ : Z.left.IdealSheafData).coequifibered_toQuotientAlgebra).toBase,
      IdealSheafData.ker_quotientSpec_toBase]
  exact ⟨fun p ↦ IsEmpty.false ((deformationSpecialFibreToNormalCone Z ⊤ k' ≫
    IdealSheafData.normalConeToQuotientSpec _).base p)⟩

/-- A rational point `x` outside the image of `g` pulls back to the unit ideal: `g⁻¹(ker x) = ⊤`. -/
lemma comap_ker_eq_top_of_disjoint [IsSeparated X.hom] (x : RationalPoint X) (g : Z ⟶ X)
    (hx : Disjoint (Set.range g.left.base) (Set.range x.left.base)) :
    x.left.ker.comap g.left = ⊤ := by
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  rw [← IdealSheafData.support_eq_bot_iff, IdealSheafData.support_comap]
  refine TopologicalSpace.Closeds.ext (Set.eq_empty_of_forall_notMem fun z hz ↦ ?_)
  have hz' : g.left.base z ∈ (x.left.ker.support : Set X.left) := hz
  rw [Scheme.Hom.support_ker, x.left.isClosedEmbedding.isClosed_range.closure_eq] at hz'
  exact Set.disjoint_left.mp hx ⟨z, rfl⟩ hz'

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- **Nearby cycles of the deformation kill complexes supported away from `I`**: for a closed
immersion `g : Z ⟶ X` with `g⁻¹ I = 𝒪_Z`, `Ψ_X(Rg_* M) ≅ Rg'_* Ψ_Z(M) = 0`, by proper base change
for nearby cycles, the special fibre of the deformation of `Z` along `g⁻¹ I` being empty. -/
theorem isZero_deformationNearbyCycles_obj_lowerStar_obj [Fact (ringChar k' ≠ ℓ)]
    (I : X.left.IdealSheafData) (g : Z ⟶ X)
    [IsClosedImmersion g.left] (hI : I.comap g.left = ⊤)
    (hM : (deformationModel X I k').PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
      ((boundedConstructibleLowerStar ℓ g).obj M)) := by
  have hJ := IdealSheafData.map_siteIdeal_le_of_comap_le g.left (le_refl (I.comap g.left))
  have : IsEmpty (deformationSpecialFibre Z (I.comap g.left) k').left := by
    rw [hI]; exact isEmpty_deformationSpecialFibre_top k'
  have : IsClosedImmersion (deformationModelHom g hJ k').total :=
    have := IdealSheafData.isClosedImmersion_deformationSpaceMap g.left I _ hJ rfl
    MorphismProperty.of_isPullback (isPullback_deformationTotalMap g hJ k').flip this
  have hε : IsPullback (deformationModel Z (I.comap g.left) k').ε
      (deformationModelHom g hJ k').generic g.left (deformationModel X I k').ε := by
    refine IsPullback.of_bot ?_ (deformationModelHom g hJ k').comm_ε.symm
      (isPullback_deformationModel_ε k' (X := X) I)
    rw [Over.w]
    change IsPullback _ (deformationGenericMap g hJ k' ≫ pullback.snd _ _) _ _
    rw [show deformationGenericMap g hJ k' ≫ pullback.snd _ _ = pullback.snd _ _ from
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)]
    exact isPullback_deformationModel_ε k' (X := Z) _
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := (deformationModelHom g hJ k').isIso_pushforwardExchange_app_of_isProper X.hom
    (isTraitModel_deformationModel Z _ k').exists_over
    (isTraitModel_deformationModel X I k').exists_over
    (isPullback_deformationSpecialFibreMap k' g hJ) hε M.property
  have h3 : IsZero
      (R(((deformationSpecialFibreMap g hJ k').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (((deformationModel Z (I.comap g.left) k').nearbyCycles _).obj M.obj)) :=
    Functor.map_isZero _ (isZero_derivedCategory_padicAlgCl_of_isEmpty _)
  have e1 := (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hM).app
    ((boundedConstructibleLowerStar ℓ g).obj M)
  have e2 := ((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).mapIso
    ((boundedConstructibleLowerStarCompatibility ℓ g).app M)
  have e3 := asIso (((deformationModelHom g hJ k').pushforwardExchange
      (Profinite.padicAlgClRingObj ℓ)).app M.obj)
  have h : IsZero ((boundedConstructible _).ι.obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
        ((boundedConstructibleLowerStar ℓ g).obj M))) := h3.of_iso (e1 ≪≫ e2 ≪≫ e3)
  exact IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ h

/-- **Specialization kills complexes supported away from the point** (step (E) of Varshavsky's
argument): for a closed immersion `g : Z ⟶ X` whose image avoids the rational point `x`,
`Sp_{X,x}(Rg_* M) = 0`. -/
theorem isZero_specialization_obj_lowerStar_obj [IsSepClosed k'] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] (x : RationalPoint X) (g : Z ⟶ X) [IsClosedImmersion g.left]
    (hx : Disjoint (Set.range g.left.base) (Set.range x.left.base))
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((specialization k' x).obj ((boundedConstructibleLowerStar ℓ g).obj M)) :=
  isZero_deformationNearbyCycles_obj_lowerStar_obj k' _ g (comap_ker_eq_top_of_disjoint x g hx) _ M

end AlgebraicGeometry.ProEtale.CondensedRing
