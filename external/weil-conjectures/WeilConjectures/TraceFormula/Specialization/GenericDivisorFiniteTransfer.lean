/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisse

/-!

# Vanishing of the restricted specialization near a point along a finite morphism

Let `f : X' ⟶ X` be a finite morphism of separated `k`-schemes of finite type, `Z = V(I) ⊆ X` a
closed subscheme, `Z' = f⁻¹ Z` and `f_Z : Z' ⟶ Z` the restriction of `f`. The coefficients are the
condensed ring `T̲` of a finite discrete commutative ring `T`.

For a complex `K` on `X'` of étale origin, the restricted specialization `Le^* Ψ_X(Rf_* K)` vanishes
near a point `ζ` of `Z` as soon as `Le'^* Ψ_{X'}(K)` vanishes near every point `ζ'` of `Z'` over
`ζ` (`ProEtale.CondensedRing.nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite`). Indeed,
by the proper exchange of nearby cycles with finite coefficients and proper base change along the
cartesian square of zero sections,
`Le^* Ψ_X(Rf_* K) ≅ Rf_{0*} Le'^* Ψ_{X'}(K)` for the finite map `f_0 : Z' ⊗ k' ⟶ Z ⊗ k'`
(`ProEtale.CondensedRing.isZero_restrictedZeroSectionNearbyCycles_rightDerivedLowerStar_of_isProper`
);
the fibre of `f_Z` over `ζ` is finite, and since `f_Z` is closed, some open neighbourhood `U` of
`ζ` has inverse image covered by the neighbourhoods of the points of the fibre on which
`Le'^* Ψ_{X'}(K)` vanishes.

## Main results

- `ProEtale.CondensedRing.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj`:
  nearby cycles preserve complexes of étale origin.
- `ProEtale.CondensedRing.isZero_leftDerivedUpperStar_ι_rightDerivedLowerStar_obj_of_isProper`:
  for `g` proper, `Rg_* M` vanishes over an open `W` if `M` vanishes over `g⁻¹ W`.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite`: the transfer
  of the vanishing near a point along a finite morphism.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite_of_notMem_range`:
  the vanishing near a point outside the image of a finite morphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-- Let `g : A → B` be a closed map and `O ⊆ A` an open set containing the fibre of `g` over `b`.
Then `b` has an open neighbourhood whose inverse image is contained in `O`. -/
lemma IsClosedMap.exists_isOpen_mem_preimage_subset {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {g : A → B} (hg : IsClosedMap g) {O : Set A} (hO : IsOpen O) {b : B}
    (hb : g ⁻¹' {b} ⊆ O) : ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ g ⁻¹' V ⊆ O := by
  refine ⟨(g '' Oᶜ)ᶜ, (hg _ hO.isClosed_compl).isOpen_compl, fun ⟨a, ha, hab⟩ ↦ ha (hb hab), ?_⟩
  intro a ha
  by_contra hna
  exact ha ⟨a, hna, rfl⟩

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Nearby cycles preserve complexes of étale origin**: for a model `M` whose inclusion `j` of
the geometric generic fibre is quasi-compact and quasi-separated, `Ψ_M = Li^* Rj_* Lε^*` maps
complexes with finite coefficients bounded below of étale origin to such complexes. -/
lemma plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj {X X' : Scheme.{u}}
    (M : NearbyCyclesModel X X') [QuasiCompact M.j] [QuasiSeparated M.j]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'
      ((finiteCoefficientDerivedEquivalence X' T).functor.obj
        ((M.nearbyCycles (Profinite.continuousMapRingObj T)).obj K)) :=
  plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.i
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T M.j
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.ε hK))

/-- **Direct images along proper maps and restriction to opens**: for `g : S' ⟶ S` proper, an
open `W ⊆ S` and a complex `M` on `S'` of étale origin vanishing over `g⁻¹ W`, the direct image
`Rg_* M` vanishes over `W`. By proper base change along the open immersion `W ⟶ S`,
`(Rg_* M)|_W ≅ R(g|_W)_* (M|_{g⁻¹ W})`. -/
lemma isZero_leftDerivedUpperStar_ι_rightDerivedLowerStar_obj_of_isProper {S S' : Scheme.{u}}
    (g : S' ⟶ S) [IsProper g] (W : S.Opens)
    {M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S') Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) S'))}
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) S'
      ((finiteCoefficientDerivedEquivalence S' T).functor.obj M))
    (h : IsZero (L(((g ⁻¹ᵁ W).ι)^*⟦Profinite.continuousMapRingObj T⟧).obj M)) :
    IsZero (L((W.ι)^*⟦Profinite.continuousMapRingObj T⟧).obj
      (R((g)_*⟦Profinite.continuousMapRingObj T⟧).obj M)) := by
  have := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T
    (isPullback_morphismRestrict g W).flip M hM
  exact ((R((g ∣_ W)_*⟦Profinite.continuousMapRingObj T⟧)).map_isZero h).of_iso
    (asIso ((baseChangeMap (Profinite.continuousMapRingObj T)
      (isPullback_morphismRestrict g W).flip.toCommSq).app M))

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-- The restriction of a finite morphism to the centres is finite. -/
lemma isFinite_centreMap [IsFinite f.left] : IsFinite (centreMap f I).left :=
  MorphismProperty.of_isPullback (isPullback_centreMap f I).flip ‹_›

/-- The map of zero sections induced by a finite morphism is finite. -/
lemma isFinite_centreSpecialFibreMap [IsFinite f.left] :
    IsFinite (centreSpecialFibreMap f I k').left :=
  MorphismProperty.of_isPullback (isPullback_centreSpecialFibreMap k' f I).flip
    (isFinite_centreMap f I)

attribute [local instance] isFinite_centreMap isFinite_centreSpecialFibreMap

/-- **Transfer of the vanishing of the restricted specialization along a proper morphism**: let
`f : X' ⟶ X` be proper and `K` a complex on `X'` of étale origin. If `Le'^* Ψ_{X'}(K)` vanishes
over the inverse image in `Z' ⊗ k'` of `f_Z⁻¹ U`, for an open `U` of the centre `Z`, then
`Le^* Ψ_X(Rf_* K)` vanishes over the inverse image of `U` in `Z ⊗ k'`. By the proper exchange of
nearby cycles and proper base change along the cartesian square of zero sections,
`Le^* Ψ_X(Rf_* K) ≅ Rf_{0*} Le'^* Ψ_{X'}(K)`, for the proper map `f_0 : Z' ⊗ k' ⟶ Z ⊗ k'`. -/
theorem isZero_restrictedZeroSectionNearbyCycles_rightDerivedLowerStar_of_isProper
    [IsProper f.left] (U : (centre X I).left.Opens)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X'.left)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'.left
      ((finiteCoefficientDerivedEquivalence X'.left T).functor.obj K))
    (h : IsZero ((restrictedZeroSectionNearbyCycles X' (I.comap f.left) k'
      (Profinite.continuousMapRingObj T) ((constantSpecialFibreProj k' (centre X' (I.comap f.left)))
        ⁻¹ᵁ (centreMap f I).left ⁻¹ᵁ U)).obj K)) :
    IsZero ((restrictedZeroSectionNearbyCycles X I k' (Profinite.continuousMapRingObj T)
      ((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U)).obj
        (R((f.left)_*⟦Profinite.continuousMapRingObj T⟧).obj K)) := by
  have : IsProper (comapDeformationModelHom f I k').total :=
    isProper_deformationTotalMap k' f (siteIdeal_map_appLE_le_comap f I) rfl
  have : IsProper (comapSpecialFibreMap f I k').left :=
    MorphismProperty.of_isPullback
      (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
      ‹IsProper (comapDeformationModelHom f I k').total›
  have : IsProper (centreSpecialFibreMap f I k').left :=
    MorphismProperty.of_isPullback (isPullback_zeroSectionSpecialFibreMap f I k') ‹_›
  have : QuasiCompact (deformationModel X' (I.comap f.left) k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : QuasiSeparated (deformationModel X' (I.comap f.left) k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have hΨ := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_nearbyCycles_obj T
    (deformationModel X' (I.comap f.left) k') hK
  have h₁ :=
    (comapDeformationModelHom f I k').isIso_pushforwardExchange_app_of_isProper_finiteCoefficient
      T (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
      (isPullback_deformationModel_ε_deformationGenericMap k' f (siteIdeal_map_appLE_le_comap f I))
      K hK
  have h₂ := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T
    (isPullback_zeroSectionSpecialFibreMap f I k') _ hΨ
  have hW : (centreSpecialFibreMap f I k').left ⁻¹ᵁ
      (constantSpecialFibreProj k' (centre X I) ⁻¹ᵁ U) ≤
      constantSpecialFibreProj k' (centre X' (I.comap f.left)) ⁻¹ᵁ
        (centreMap f I).left ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, centreSpecialFibreMap_constantSpecialFibreProj,
      Scheme.Hom.comp_preimage]
  rw [restrictedZeroSectionNearbyCycles_obj] at h ⊢
  have h₃ := isZero_leftDerivedUpperStar_ι_rightDerivedLowerStar_obj_of_isProper T
    (centreSpecialFibreMap f I k').left ((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U)
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
      (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left hΨ)
    (isZero_leftDerivedUpperStar_ι_obj_of_le _ hW h)
  exact h₃.of_iso ((L(((constantSpecialFibreProj k' (centre X I) ⁻¹ᵁ U).ι)^*⟦
    Profinite.continuousMapRingObj T⟧)).mapIso
      ((L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.continuousMapRingObj T⟧)).mapIso
        (asIso (((comapDeformationModelHom f I k').pushforwardExchange
          (Profinite.continuousMapRingObj T)).app K)) ≪≫
        asIso ((baseChangeMap (Profinite.continuousMapRingObj T)
          (isPullback_zeroSectionSpecialFibreMap f I k').toCommSq).app _)))

/-- **Vanishing near a point along a finite morphism**: let `f : X' ⟶ X` be finite, `ζ` a point
of the centre `Z` and `K` a complex on `X'` of étale origin such that `Le'^* Ψ_{X'}(K)` vanishes
near every point `ζ'` of `Z' = f⁻¹ Z` over `ζ`. Then `Le^* Ψ_X(Rf_* K)` vanishes near `ζ`. The
fibre of `f_Z` over `ζ` is finite, and `f_Z` is closed, so some open neighbourhood `U` of `ζ` has
inverse image covered by the given neighbourhoods of the points of the fibre; conclude by
`isZero_restrictedZeroSectionNearbyCycles_rightDerivedLowerStar_of_isProper`. -/
theorem nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsFinite f.left]
    (ζ : (centre X I).left)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X'.left)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'.left
      ((finiteCoefficientDerivedEquivalence X'.left T).functor.obj K))
    (h : ∀ ζ' : (centre X' (I.comap f.left)).left, (centreMap f I).left ζ' = ζ →
      nearbyCyclesVanishNear X' (I.comap f.left) k' (Profinite.continuousMapRingObj T) ζ' K) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj T) ζ
      (R((f.left)_*⟦Profinite.continuousMapRingObj T⟧).obj K) := by
  have := ((centreMap f I).left.finite_preimage_singleton ζ).to_subtype
  choose U hU hUK using fun ζ' : (centreMap f I).left ⁻¹' {ζ} ↦ h ζ'.1 ζ'.2
  obtain ⟨V, hV, hζV, hVU⟩ := (centreMap f I).left.isClosedMap.exists_isOpen_mem_preimage_subset
    (isOpen_iUnion fun a ↦ (U a).isOpen) fun z hz ↦ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hU _⟩
  refine ⟨⟨V, hV⟩, hζV,
    isZero_restrictedZeroSectionNearbyCycles_rightDerivedLowerStar_of_isProper T f I k' _ K hK ?_⟩
  rw [restrictedZeroSectionNearbyCycles_obj]
  refine isZero_leftDerivedUpperStar_ι_obj_of_cover _ _
    (fun a ↦ (constantSpecialFibreProj k' (centre X' (I.comap f.left))) ⁻¹ᵁ
      ((centreMap f I).left ⁻¹ᵁ ⟨V, hV⟩ ⊓ U a)) (fun a ↦ Hom.preimage_mono _ inf_le_left)
    (fun x hx ↦ ?_) fun a ↦ ?_
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (hVU hx)
    exact ⟨a, hx, ha⟩
  · have := hUK a
    rw [restrictedZeroSectionNearbyCycles_obj] at this
    exact isZero_leftDerivedUpperStar_ι_obj_of_le _ (Hom.preimage_mono _ inf_le_right) this

/-- **Vanishing near a point outside the image of a finite morphism**: if `ζ` is not in the image
of `f_Z : Z' ⟶ Z` and `f` is finite, then `Le^* Ψ_X(Rf_* K)` vanishes near `ζ` for every complex
`K` on `X'` of étale origin. -/
theorem nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite_of_notMem_range
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsFinite f.left]
    (ζ : (centre X I).left) (hζ : ζ ∉ Set.range (centreMap f I).left)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X'.left)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'.left
      ((finiteCoefficientDerivedEquivalence X'.left T).functor.obj K)) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj T) ζ
      (R((f.left)_*⟦Profinite.continuousMapRingObj T⟧).obj K) :=
  nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite T f I k' ζ K hK
    fun ζ' hζ' ↦ (hζ ⟨ζ', hζ'⟩).elim

end AlgebraicGeometry.ProEtale.CondensedRing
