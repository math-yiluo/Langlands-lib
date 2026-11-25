/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.Specialization.DefectExchangeSquares
public import WeilConjectures.TraceFormula.Specialization.DeformationModelFactor
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchange
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# Exchanges for the defect of the specialization

Let `f : X' ⟶ X` be a morphism of separated `k`-schemes of finite type, `Z = V(I) ⊆ X` a closed
subscheme and `Z' = f⁻¹ Z = V(f^* I)` its schematic inverse image, with the restriction
`f_Z : Z' ⟶ Z` (`ProEtale.CondensedRing.centreMap`). The deformation of `f_Z` maps the special fibre
`N_⊥ Z' ≅ Z' ⊗ k'` of the constant family of `Z'` to that of `Z`
(`ProEtale.CondensedRing.centreSpecialFibreMap`).

This file states the exchange properties of the defect `C_{X,Z}` of
`ProEtale.CondensedRing.specializationDefect`, which are the nodes of the blueprint subsection
`lemma-base-change-cone-x-z`, as compatibilities required from that subsection:

* `ProEtale.CondensedRing.nonempty_specializationDefect_lowerStar_iso`,
  `ProEtale.CondensedRing.nonempty_specializationDefect_upperStar_iso`: proper and smooth exchange
  (blueprint `lemma-base-change-cone-x-z`);
* `ProEtale.CondensedRing.isZero_specializationDefect_lowerStar_centreι`,
  `ProEtale.CondensedRing.nonempty_specializationDefect_lowerShriek_upperStar_iso`: the defect
  kills complexes supported on the centre, and is unchanged by `L ↦ j_! j^* L`
  (blueprint `lemma-base-change-cone-x-z`).

The coefficients are `ℚ̄_ℓ`, and the complexes are bounded constructible.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]



/-- **Smooth exchange for the defect** (blueprint `lemma-base-change-cone-x-z`, smooth case; a
node of the subsection `lemma-base-change-cone-x-z`): for `f : X' ⟶ X` smooth and `L` bounded
constructible on `X`, `C_{X',Z'}(Lf^* L) ≅ Lf_Z^* C_{X,Z}(L)`. The pullback exchanges of the
deformations `f̃` and `f̃_Z` of `f` and `f_Z` are invertible by the smooth exchange of nearby cycles
(`isIso_pullbackExchange_deformationModel_app_of_smooth`), and they carry `Lf_Z^* ε_{X,Z}(L)` to
`ε_{X',Z'}(Lf^* L)` (`nonempty_specializationDefect_upperStar_iso_of_isIso`). -/
theorem nonempty_specializationDefect_upperStar_iso [Smooth f.left]
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X' (I.comap f.left) k' (Profinite.padicAlgClRingObj ℓ)
        (L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj) ≅
      L(((centreSpecialFibreMap f I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) := by
  have : Smooth (comapDeformationModelHom f I k').total :=
    smooth_deformationTotalMap k' f (siteIdeal_map_appLE_le_comap f I) rfl
  have : Smooth (centreDeformationModelHom f I k').total :=
    smooth_deformationTotalMap k' (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I)
      (IdealSheafData.comap_bot _).symm
  have hf := isIso_pullbackExchange_deformationModel_app_of_smooth k'
    (comapDeformationModelHom f I k') (isPullback_deformationGenericMap _ _ k') L.property
  have hg := isIso_pullbackExchange_deformationModel_app_of_smooth k'
    (centreDeformationModelHom f I k') (isPullback_deformationGenericMap _ _ k')
    (boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I) L)
  have h₁ := nonempty_specializationDefect_upperStar_iso_of_isIso f I k'
    (Profinite.padicAlgClRingObj ℓ) L.obj
  revert h₁ hf hg
  normalize_precoherent
  intro hf hg h₁
  exact h₁ hf hg

/-- **Proper exchange for the defect** (blueprint `lemma-base-change-cone-x-z`, proper case; a
node of the subsection `lemma-base-change-cone-x-z`): for `f : X' ⟶ X` proper and `L'` bounded
constructible on `X'`, `C_{X,Z}(Rf_* L') ≅ Rf_{Z*} C_{X',Z'}(L')`. The pushforward exchanges of the
proper deformations `f̃` and `f̃_Z` are invertible (proper exchange of nearby cycles), and so are
the base change morphisms of the cartesian squares `i' ≫ f = f_Z ≫ i` and `e' ≫ f_s = g_s ≫ e`
(proper base change); they carry `ε_{X,Z}(Rf_* L')` to `Rf_{Z*} ε_{X',Z'}(L')`
(`nonempty_specializationDefect_lowerStar_iso_of_isIso`). -/
theorem nonempty_specializationDefect_lowerStar_iso [IsProper f.left]
    (L' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
        (R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L'.obj) ≅
      R(((centreSpecialFibreMap f I k').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (specializationDefect X' (I.comap f.left) k' (Profinite.padicAlgClRingObj ℓ) L'.obj)) := by
  have : IsProper (comapDeformationModelHom f I k').total :=
    isProper_deformationTotalMap k' f (siteIdeal_map_appLE_le_comap f I) rfl
  have : IsProper (centreDeformationModelHom f I k').total :=
    isProper_deformationTotalMap k' (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I)
      (IdealSheafData.comap_bot _).symm
  have : IsProper (comapSpecialFibreMap f I k').left :=
    MorphismProperty.of_isPullback
      (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
      ‹IsProper (comapDeformationModelHom f I k').total›
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType (centre X I).hom
  have := isNoetherian_of_locallyOfFiniteType (deformationSpecialFibre X I k').hom
  have := isNoetherian_of_locallyOfFiniteType
    (deformationSpecialFibre (centre X I) ⊥ k').hom
  have h₁ := (comapDeformationModelHom f I k').isIso_pushforwardExchange_app_of_isProper X.hom
    (isTraitModel_deformationModel _ _ k').exists_over
    (isTraitModel_deformationModel _ _ k').exists_over
    (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
    (isPullback_deformationModel_ε_deformationGenericMap k' f (siteIdeal_map_appLE_le_comap f I))
    L'.property
  have h₂ := (centreDeformationModelHom f I k').isIso_pushforwardExchange_app_of_isProper
    (centre X I).hom
    (isTraitModel_deformationModel _ _ k').exists_over
    (isTraitModel_deformationModel _ _ k').exists_over
    (isPullback_deformationSpecialFibreMap_toTotal (centreMap f I)
      (siteIdeal_map_appLE_le_bot_centreMap f I) k').flip
    (isPullback_deformationModel_ε_deformationGenericMap k' (centreMap f I)
      (siteIdeal_map_appLE_le_bot_centreMap f I))
    (boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X' (I.comap f.left)) L')
  have h₃ := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ X.hom
    (centre X I).hom
    (⟨centreι_comp_eq_centreMap_comp f I⟩ : CommSq (centreι X' (I.comap f.left)).left
      (centreMap f I).left f.left (centreι X I).left)
    (isPullback_centreMap f I).flip L'.obj L'.property
  have h₄ := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ
    (deformationSpecialFibre X I k').hom (deformationSpecialFibre (centre X I) ⊥ k').hom
    (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
      CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
        (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
        (zeroSectionSpecialFibreMap X I k').left)
    (isPullback_zeroSectionSpecialFibreMap f I k')
    (((deformationModel X' (I.comap f.left) k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
      L'.obj)
    ((deformationModel X' (I.comap f.left) k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X' (I.comap f.left) k')
      (deformationModel_exists_comp_ε X' (I.comap f.left) k') L'.obj L'.property)
  have h := nonempty_specializationDefect_lowerStar_iso_of_isIso f I k'
    (Profinite.padicAlgClRingObj ℓ) L'.obj
  revert h₁ h₂ h₃ h₄ h
  normalize_precoherent
  intro h₁ h₂ h₃ h₄ h
  exact h h₁ h₂ h₃ h₄

variable (X) in
/-- **The defect kills complexes supported on the centre** (blueprint
`lemma-base-change-cone-x-z`, first and second assertions; a node of the subsection
`lemma-base-change-cone-x-z`): `C_{X,Z}(i_* M) = 0` for `M` bounded constructible on `Z`. By
the proper exchange for the closed immersion `i`, `C_{X,Z}(i_* M) ≅ Ri_{Z*} C_{Z, i^* Z}(M)`, and
`i^* Z = Z` is the zero ideal of `Z`, whose defect vanishes. -/
theorem isZero_specializationDefect_lowerStar_centreι
    (M : Dᵇc((centre X I).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
      (R(((centreι X I).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M.obj)) := by
  have e := (nonempty_specializationDefect_lowerStar_iso (centreι X I) I k' M).some
  refine (Functor.map_isZero _ ?_).of_iso e
  exact isZero_specializationDefect_of_eq_bot k' (Profinite.padicAlgClRingObj ℓ) (centre X I)
    (I.comap (centreι X I).left) (IdealSheafData.comap_subschemeι I) M.obj

variable (X) in
/-- **The defect is unchanged by extension by zero from the complement** (blueprint
`lemma-base-change-cone-x-z`, last assertion; a node of the subsection
`lemma-base-change-cone-x-z`): for the open immersion `j : U ⟶ X` of the complement of the
centre, `C_{X,Z}(j_! j^* L) ≅ C_{X,Z}(L)`. Apply `nonempty_specializationDefect_iso_of_distTriang`
to the open–closed triangle `j_! j^* L ⟶ L ⟶ i_* i^* L`: `Li^* j_! = 0`, and the defect of
`i_* i^* L` vanishes. Here the isomorphism is only asserted to exist. -/
theorem nonempty_specializationDefect_lowerShriek_upperStar_iso {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
    [IsOpenImmersion j.left]
    (hj : IsCompl (Set.range j.left.base) (Set.range (centreι X I).left.base))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L)).obj ≅
      specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed j (centreι X I) hj L
  have h₁ := NearbyCyclesModel.isZero_nearbyCycles_obj (Profinite.padicAlgClRingObj ℓ)
    (deformationModel (centre X I) ⊥ k')
    (((boundedConstructible _).ι.map_isZero
      (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j (centreι X I)
        hj.disjoint ((boundedConstructibleUpperStar _ ℓ j).obj L))).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ (centreι X I)).symm.app _))
  have h₃ := (isZero_specializationDefect_iff X I k' (Profinite.padicAlgClRingObj ℓ) _).1
    (isZero_specializationDefect_lowerStar_centreι X I k'
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (centreι X I)).obj L))
  exact nonempty_specializationDefect_iso_of_distTriang I k' _ hδ h₁ h₃

end AlgebraicGeometry.ProEtale.CondensedRing
