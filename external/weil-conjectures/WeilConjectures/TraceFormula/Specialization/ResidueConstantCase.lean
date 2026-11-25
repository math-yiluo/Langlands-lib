/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorConstantCase
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantThickOrigin

/-!

# The constant case of generic vanishing along a divisor, with finite coefficients

Let `X` be normal, `Z = V(h)` a principal divisor with complement `j : X ∖ Z ⟶ X`, `ζ` a generic
point of `Z`, and suppose that some smooth `f₀ : W₀ ⟶ 𝔸¹_k` on a neighbourhood `W₀` of `ζ` pulls
the coordinate back to a uniformizer of the discrete valuation ring `𝒪_{X,ζ}`. For the residue
field `𝔽_E` of a finite extension `E` of `ℚ_ℓ`, the restricted specialization `Le^* Ψ_X(j_! 𝔽_E)`
vanishes near `ζ`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer`).
This is blueprint `lemma-vanishing-generic-points-principal-divisor` with coefficients `𝔽_E`.

The proof is that of the `ℚ̄_ℓ` case (`GenericDivisorConstantCase.lean`), with coefficients in a
finite ring `T` killed by `ℓ`:
* on a neighbourhood `W` of `ζ`, `Z ∩ W = f⁻¹ V(x^m)` for a smooth `f : W ⟶ 𝔸¹_k`
  (`ProEtale.CondensedRing.exists_smooth_comap_polyAffineThickOrigin_of_uniformizer`), so that
  `C_{W, Z ∩ W}(T̲) = 0` by the smooth exchange and the thick origin with finite coefficients;
* by the open exchange (`ProEtale.CondensedRing.isIso_deformationModelHom_pullbackExchange`),
  `C_{X,Z}(T̲)` then vanishes near `ζ`
  (`ProEtale.CondensedRing.isZero_restrict_specializationDefect_image_of_isOpenImmersion`);
* by the proper exchange and proper base change with finite coefficients, the defect kills
  complexes `Ri_* M` of étale origin supported on the centre, hence is unchanged by
  `L ↦ j_! j^* L`
  (`ProEtale.CondensedRing.nonempty_specializationDefect_lowerShriek_iso_finiteCoefficient`);
* since `Li^* j_! = 0`, the defect of `j_! T̲` is `Le^* Ψ_X(j_! T̲)[1]`.

## Main results

- `ProEtale.CondensedRing.nonempty_specializationDefect_lowerStar_iso_finiteCoefficient`: the
  proper exchange for the defect with finite coefficients.
- `ProEtale.CondensedRing.nonempty_specializationDefect_lowerShriek_iso_finiteCoefficient`: the
  closed vanishing of the defect with finite coefficients.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_of_uniformizer_finiteCoefficient`:
  the constant case for a finite coefficient ring killed by `ℓ`.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer`:
  the constant case with coefficients `𝔽_E`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Locality of the vanishing of the defect, for arbitrary coefficients -/

section Locality

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X V : Over (Spec (.of k))} (I : X.left.IdealSheafData)

/-- **The open exchange for the defect** (arbitrary coefficients): for an open immersion
`g : V ⟶ X`, `C_{V, Z ∩ V}(Lg^* L) ≅ Lg_Z^* C_{X,Z}(L)`, the pullback exchanges of the deformations
of `g` and of `g_Z` being invertible (`isIso_deformationModelHom_pullbackExchange`). -/
theorem nonempty_specializationDefect_upperStar_iso_of_isOpenImmersion (g : V ⟶ X)
    [IsOpenImmersion g.left]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    Nonempty (specializationDefect V (I.comap g.left) k' Λ (L((g.left)^*⟦Λ⟧).obj L) ≅
      L(((centreSpecialFibreMap g I k').left)^*⟦Λ⟧).obj (specializationDefect X I k' Λ L)) := by
  have := isIso_deformationModelHom_pullbackExchange g (siteIdeal_map_appLE_le_comap g I) k' Λ rfl
  have := isIso_deformationModelHom_pullbackExchange (centreMap g I)
    (siteIdeal_map_appLE_le_bot_centreMap g I) k' Λ (IdealSheafData.comap_bot _).symm
  exact nonempty_specializationDefect_upperStar_iso_of_isIso g I k' Λ L inferInstance
    inferInstance

/-- Let `g : V ⟶ X` be an open immersion and `U' ⊆ Z ∩ V` open (arbitrary coefficients). If the
restriction of the defect `C_{V, Z ∩ V}(Lg^* L)` to the inverse image of `U'` vanishes, so does the
restriction of `C_{X,Z}(L)` to the inverse image of the image of `U'` in `Z`. -/
theorem isZero_restrict_specializationDefect_image_of_isOpenImmersion (g : V ⟶ X)
    [IsOpenImmersion g.left]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (U' : (centre V (I.comap g.left)).left.Opens)
    (hL : IsZero ((L((((constantSpecialFibreProj k' (centre V (I.comap g.left))) ⁻¹ᵁ
      U').ι)^*⟦Λ⟧)).obj (specializationDefect V (I.comap g.left) k' Λ
        (L((g.left)^*⟦Λ⟧).obj L)))) :
    IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ
      ((centreMap g I).left ''ᵁ U')).ι)^*⟦Λ⟧)).obj (specializationDefect X I k' Λ L)) := by
  obtain ⟨e⟩ := nonempty_specializationDefect_upperStar_iso_of_isOpenImmersion k' Λ I g L
  exact isZero_leftDerivedUpperStar_ι_obj_of_le Λ
    (centreSpecialFibreMap_image_preimage k' I g U').ge
    (isZero_leftDerivedUpperStar_image_ι_obj Λ _ _
      (hL.of_iso ((L(((constantSpecialFibreProj k' (centre V (I.comap g.left)) ⁻¹ᵁ
        U').ι)^*⟦Λ⟧)).mapIso e.symm)))

end Locality

/-! ### Proper exchange and closed vanishing with finite coefficients -/

section Finite

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- Nearby cycles with finite coefficients preserve complexes of étale origin. -/
lemma plusEtaleOrigin_nearbyCycles_obj {A A' : Scheme.{u}} (M : NearbyCyclesModel A A')
    [QuasiCompact M.j] [QuasiSeparated M.j]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) A))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) A
      ((finiteCoefficientDerivedEquivalence A T).functor.obj K)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) A'
      ((finiteCoefficientDerivedEquivalence A' T).functor.obj
        ((M.nearbyCycles (Profinite.continuousMapRingObj.{u} T)).obj K)) :=
  plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.i
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T M.j
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.ε hK))

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] {X X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]

/-- **Proper exchange for the defect, with finite coefficients** (blueprint
`lemma-base-change-cone-x-z`, proper case): for `f : X' ⟶ X` proper and a complex `L'` of étale
origin on `X'`, `C_{X,Z}(Rf_* L') ≅ Rf_{Z*} C_{X',Z'}(L')`. The pushforward exchanges of the
deformations of `f` and `f_Z` are invertible by the proper exchange of nearby cycles with finite
coefficients, and the base change morphisms of the squares of the centres and of the zero sections
by proper base change with finite coefficients. -/
theorem nonempty_specializationDefect_lowerStar_iso_finiteCoefficient (f : X' ⟶ X)
    [IsProper f.left] (I : X.left.IdealSheafData)
    (L' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X'.left)))
    (hL' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'.left
      ((finiteCoefficientDerivedEquivalence X'.left T).functor.obj L')) :
    Nonempty (specializationDefect X I k' (Profinite.continuousMapRingObj.{u} T)
        (R((f.left)_*⟦Profinite.continuousMapRingObj.{u} T⟧).obj L') ≅
      R(((centreSpecialFibreMap f I k').left)_*⟦Profinite.continuousMapRingObj.{u} T⟧).obj
        (specializationDefect X' (I.comap f.left) k' (Profinite.continuousMapRingObj.{u} T)
          L')) := by
  have : IsProper (comapDeformationModelHom f I k').total :=
    isProper_deformationTotalMap k' f (siteIdeal_map_appLE_le_comap f I) rfl
  have : IsProper (centreDeformationModelHom f I k').total :=
    isProper_deformationTotalMap k' (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I)
      (IdealSheafData.comap_bot _).symm
  have : IsProper (comapSpecialFibreMap f I k').left :=
    MorphismProperty.of_isPullback
      (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
      ‹IsProper (comapDeformationModelHom f I k').total›
  obtain ⟨_, _⟩ := quasiCompact_deformationModel_j k' X' (I.comap f.left)
  obtain ⟨_, _⟩ := quasiCompact_deformationModel_j k' (centre X' (I.comap f.left)) ⊥
  have hM := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
    (centreι X' (I.comap f.left)).left hL'
  have h₁ := NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T
    (comapDeformationModelHom f I k')
    (isPullback_deformationSpecialFibreMap_toTotal f (siteIdeal_map_appLE_le_comap f I) k').flip
    (isPullback_deformationModel_ε_deformationGenericMap k' f (siteIdeal_map_appLE_le_comap f I))
    L' hL'
  have h₂ := NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T
    (centreDeformationModelHom f I k')
    (isPullback_deformationSpecialFibreMap_toTotal (centreMap f I)
      (siteIdeal_map_appLE_le_bot_centreMap f I) k').flip
    (isPullback_deformationModel_ε_deformationGenericMap k' (centreMap f I)
      (siteIdeal_map_appLE_le_bot_centreMap f I)) _ hM
  have sqc : IsPullback (centreι X' (I.comap f.left)).left (centreMap f I).left f.left
      (centreι X I).left := by
    rw [centreι_left, centreι_left]
    exact (isPullback_centreMap f I).flip
  have h₃ := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T sqc L' hL'
  have h₄ := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T
    (isPullback_zeroSectionSpecialFibreMap f I k') _
    (plusEtaleOrigin_nearbyCycles_obj T (deformationModel X' (I.comap f.left) k') hL')
  exact nonempty_specializationDefect_lowerStar_iso_of_isIso f I k'
    (Profinite.continuousMapRingObj.{u} T) L' (by exact_mod_proofs h₁) (by exact_mod_proofs h₂)
    (by exact_mod_proofs h₃) (by exact_mod_proofs h₄)

variable (X) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- **The defect kills complexes of étale origin supported on the centre, with finite
coefficients** (blueprint `lemma-base-change-cone-x-z`): `C_{X,Z}(Ri_* M) = 0` for `M` of
étale origin on `Z`, by the proper exchange for the closed immersion `i` and the vanishing of the
defect of the zero ideal. -/
theorem isZero_specializationDefect_lowerStar_centreι_finiteCoefficient
    (I : X.left.IdealSheafData)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (centre X I).left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) (centre X I).left)))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) (centre X I).left
      ((finiteCoefficientDerivedEquivalence (centre X I).left T).functor.obj M)) :
    IsZero (specializationDefect X I k' (Profinite.continuousMapRingObj.{u} T)
      (R(((centreι X I).left)_*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M)) := by
  obtain ⟨e⟩ := nonempty_specializationDefect_lowerStar_iso_finiteCoefficient T k' (centreι X I) I
    M hM
  exact (Functor.map_isZero _ (isZero_specializationDefect_of_eq_bot k' _ (centre X I)
    (I.comap (centreι X I).left) (IdealSheafData.comap_subschemeι I) M)).of_iso e

/-- **The defect is unchanged by extension by zero from the complement, with finite
coefficients** (blueprint `lemma-base-change-cone-x-z`, last assertion): for the open
immersion `j : U ⟶ X` of the complement of the centre and `L` of étale origin,
`C_{X,Z}(j_! Lj^* L) ≅ C_{X,Z}(L)`. Apply `nonempty_specializationDefect_iso_of_distTriang` to the
open–closed triangle `j_! Lj^* L ⟶ L ⟶ Ri_* Li^* L`: `Li^* j_! = 0`, and the defect of
`Ri_* Li^* L` vanishes. -/
theorem nonempty_specializationDefect_lowerShriek_iso_finiteCoefficient
    (I : X.left.IdealSheafData) {U : Over (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left]
    (hj : IsCompl (Set.range j.left.base) (Set.range (centreι X I).left.base))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X.left)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X.left
      ((finiteCoefficientDerivedEquivalence X.left T).functor.obj L)) :
    Nonempty (specializationDefect X I k' (Profinite.continuousMapRingObj.{u} T)
        (D((j.left)_!open⟦Profinite.continuousMapRingObj.{u} T⟧).obj
          ((L((j.left)^*⟦Profinite.continuousMapRingObj.{u} T⟧)).obj L)) ≅
      specializationDefect X I k' (Profinite.continuousMapRingObj.{u} T) L) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed_derived (Profinite.continuousMapRingObj.{u} T)
    j.left (centreι X I).left hj.symm L
  have h₁ := NearbyCyclesModel.isZero_nearbyCycles_obj (Profinite.continuousMapRingObj.{u} T)
    (deformationModel (centre X I) ⊥ k')
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint _ j.left
      (centreι X I).left hj.disjoint ((L((j.left)^*⟦Profinite.continuousMapRingObj.{u} T⟧)).obj L))
  have h₃ := (isZero_specializationDefect_iff X I k' _ _).1
    (isZero_specializationDefect_lowerStar_centreι_finiteCoefficient T k' X I _
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
        (centreι X I).left hL))
  exact nonempty_specializationDefect_iso_of_distTriang I k' _ hδ h₁ h₃

end Finite

/-! ### A smooth chart pulling back a thick origin near a generic point of the divisor -/

section Chart

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]

/-- **A smooth uniformizer pulls back a thick origin**: let `X` be normal, `Z = V(h)` for a nonzero
global function `h`, `ζ` a generic point of `Z`, and `f₀ : W₀ ⟶ 𝔸¹_k` a smooth morphism on a
neighbourhood `W₀` of `ζ` such that `f₀^* x` is a uniformizer of the discrete valuation ring
`𝒪_{X,ζ}`. Then on a smaller neighbourhood `W` of `ζ`, with the restriction `f` of `f₀`,
`Z ∩ W = f⁻¹ V(x^m)` for some `m ≥ 1`: near `ζ`, `h = (unit) · (f₀^* x)^m`
(`Scheme.exists_span_eq_span_pow_of_irreducible_germ`). -/
theorem exists_smooth_comap_polyAffineThickOrigin_of_uniformizer (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (W₀ : X.left.Opens) (hζW₀ : I.subschemeι ζ ∈ W₀)
    (f₀ : overRestrict X W₀ ⟶ polyAffine k 1) [Smooth f₀.left]
    (hf₀ : Irreducible (X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) (I.subschemeι ζ)
      ⟨⟨I.subschemeι ζ, hζW₀⟩, trivial, rfl⟩ (f₀.left.appTop (polyAffineCoord k (Fin.last 0))))) :
    ∃ (W : X.left.Opens) (_ : I.subschemeι ζ ∈ W) (f : overRestrict X W ⟶ polyAffine k 1)
      (_ : Smooth f.left) (m : ℕ), 0 < m ∧
        I.comap (overRestrictι X W).left = (polyAffineThickOrigin k m).comap f.left := by
  have := hX.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := (hX.2 (I.subschemeι ζ)).1
  have := (hX.2 (I.subschemeι ζ)).2
  have : IsDiscreteValuationRing (X.left.presheaf.stalk (I.subschemeι ζ)) :=
    IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral X.left (U := ⊤) _ trivial)).2 hh)
      (maximalIdeal_stalk_mem_minimalPrimes (subschemeι_mem_zeroLocus hI ζ)
        (eq_of_specializes_subschemeι hI ζ hζ))
  have hxU₀ : I.subschemeι ζ ∈ W₀.ι ''ᵁ ⊤ := ⟨⟨I.subschemeι ζ, hζW₀⟩, trivial, rfl⟩
  have hgerm : X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) _ hxU₀
      (X.left.presheaf.map (homOfLE le_top : W₀.ι ''ᵁ ⊤ ⟶ ⊤).op h) =
      X.left.presheaf.germ ⊤ (I.subschemeι ζ) trivial h :=
    X.left.presheaf.germ_res_apply _ _ _ _
  obtain ⟨W, hζW, iW, m, hm, hspan⟩ := Scheme.exists_span_eq_span_pow_of_irreducible_germ hxU₀
    (X.left.presheaf.map (homOfLE le_top : W₀.ι ''ᵁ ⊤ ⟶ ⊤).op h)
    (f₀.left.appTop (polyAffineCoord k (Fin.last 0)))
    (by
      rw [hgerm]
      exact (map_ne_zero_iff _ (germ_injective_of_isIntegral X.left (U := ⊤) _ trivial)).2 hh)
    hf₀
    (by
      rw [hgerm, ← Scheme.mem_basicOpen]
      exact (X.left.mem_zeroLocus_iff _ _).1 (subschemeι_mem_zeroLocus hI ζ) h rfl)
  have hWW₀ : W ≤ W₀ := (leOfHom iW).trans (W₀.ι_image_le _)
  let r : overRestrict X W ⟶ overRestrict X W₀ := Over.homMk (X.left.homOfLE hWW₀) (by simp)
  have hr : r.left = X.left.homOfLE hWW₀ := rfl
  let f : overRestrict X W ⟶ polyAffine k 1 := r ≫ f₀
  have : Smooth f.left := by
    rw [Over.comp_left, hr]
    infer_instance
  refine ⟨W, hζW, f, this, m, hm, ?_⟩
  have hspan' := congrArg (Ideal.map (X.left.presheaf.map
    (homOfLE (W.ι_image_le ⊤) : W.ι ''ᵁ ⊤ ⟶ W).op).hom) hspan
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow]
    at hspan'
  rw [hI, IdealSheafData.comap_ofIdealTop, polyAffineThickOrigin, IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow]
  have e₁ : (overRestrictι X W).left.appTop h = X.left.presheaf.map
      (homOfLE (W.ι_image_le ⊤) : W.ι ''ᵁ ⊤ ⟶ W).op (X.left.presheaf.map iW.op
        (X.left.presheaf.map (homOfLE le_top : W₀.ι ''ᵁ ⊤ ⟶ ⊤).op h)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  have e₂ : f.left.appTop (polyAffineCoord k (Fin.last 0)) = X.left.presheaf.map
      (homOfLE (W.ι_image_le ⊤) : W.ι ''ᵁ ⊤ ⟶ W).op (X.left.presheaf.map iW.op
        (f₀.left.appTop (polyAffineCoord k (Fin.last 0)))) := by
    rw [Over.comp_left, hr, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.homOfLE_appTop, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp]
    rfl
  rw [e₁, e₂]
  exact congrArg _ hspan'

end Chart

/-! ### The constant case -/

section Main

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k]
  (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The defect of the constant complex vanishes near a point with a smooth chart pulling back a
thick origin, with finite coefficients**: let `ζ` be a point of `Z = V(I)` with an open
neighbourhood `W` in `X` and a smooth `f : W ⟶ 𝔸¹_k` such that `Z ∩ W = f⁻¹ V(x^m)`, `m ≥ 1`.
Then `C_{X,Z}(T̲)` vanishes near `ζ`, for a finite coefficient ring `T` killed by `ℓ ≠ char k'`:
`C_{W, Z ∩ W}(T̲) = 0` by the smooth exchange and the thick origin, and the open exchange along
`W ⟶ X` concludes. -/
theorem defectVanishesNear_unit_of_smooth_finiteCoefficient (hT : (ℓ : T) = 0)
    (I : X.left.IdealSheafData) (ζ : (centre X I).left) (W : X.left.Opens)
    (hζW : I.subschemeι ζ ∈ W) (f : overRestrict X W ⟶ polyAffine k 1) [Smooth f.left] {m : ℕ}
    (hm : 0 < m)
    (hI : I.comap (overRestrictι X W).left = (polyAffineThickOrigin k m).comap f.left) :
    defectVanishesNear X I k' (Profinite.continuousMapRingObj.{u} T) (𝟙_ _) ζ := by
  have h₀ := isZero_specializationDefect_unit_of_smooth_finiteCoefficient k' T f
    (polyAffineThickOrigin k m) hT
    (isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient T k' hT hm)
  rw [← hI] at h₀
  obtain ⟨e⟩ := nonempty_specializationDefect_iso (overRestrict X W)
    (I.comap (overRestrictι X W).left) k' (Profinite.continuousMapRingObj.{u} T)
    (leftDerivedUpperStarUnitIso _ (overRestrictι X W).left)
  have hζ : ζ ∈ Set.range (centreMap (overRestrictι X W) I).left := by
    rw [range_centreMap, Set.mem_preimage, range_overRestrictι]
    exact hζW
  obtain ⟨ζ', rfl⟩ := hζ
  exact ⟨(centreMap (overRestrictι X W) I).left ''ᵁ ⊤, ⟨ζ', trivial, rfl⟩,
    isZero_restrict_specializationDefect_image_of_isOpenImmersion k' _ I (overRestrictι X W) _ ⊤
      (Functor.map_isZero _ (h₀.of_iso e))⟩

/-- **The constant case near a point with a smooth chart pulling back a thick origin, with finite
coefficients**: under the hypotheses of `defectVanishesNear_unit_of_smooth_finiteCoefficient`,
`Le^* Ψ_X(j_! T̲)` vanishes near `ζ`, for the complement `j : X ∖ Z ⟶ X`. Indeed
`C_{X,Z}(j_! T̲) ≅ C_{X,Z}(j_! Lj^* T̲) ≅ C_{X,Z}(T̲)` vanishes near `ζ`
(`nonempty_specializationDefect_lowerShriek_iso_finiteCoefficient`), and since `Li^* j_! = 0`
this defect is `Le^* Ψ_X(j_! T̲)[1]`. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_of_smooth_finiteCoefficient
    (hT : (ℓ : T) = 0) (I : X.left.IdealSheafData) (ζ : (centre X I).left) (W : X.left.Opens)
    (hζW : I.subschemeι ζ ∈ W) (f : overRestrict X W ⟶ polyAffine k 1) [Smooth f.left] {m : ℕ}
    (hm : 0 < m)
    (hI : I.comap (overRestrictι X W).left = (polyAffineThickOrigin k m).comap f.left) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj.{u} T) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj.{u} T⟧)).obj (𝟙_ _)) := by
  obtain ⟨U, hζU, hU⟩ := defectVanishesNear_unit_of_smooth_finiteCoefficient T k' hT I ζ W hζW f hm
    hI
  obtain ⟨e₁⟩ := nonempty_specializationDefect_iso X I k' (Profinite.continuousMapRingObj.{u} T)
    ((D(((overRestrictι X I.support.compl).left)_!open⟦
      Profinite.continuousMapRingObj.{u} T⟧)).mapIso
      (leftDerivedUpperStarUnitIso _ (overRestrictι X I.support.compl).left).symm)
  obtain ⟨e₂⟩ := nonempty_specializationDefect_lowerShriek_iso_finiteCoefficient T k' X I
    (overRestrictι X I.support.compl) (isCompl_range_overRestrictι_centreι I) (𝟙_ _)
    (isEtaleOrigin_of_isConstructible T (boundedConstructible_tensorUnit _ _)).plusEtaleOrigin
  have hΨ := NearbyCyclesModel.isZero_nearbyCycles_obj (Profinite.continuousMapRingObj.{u} T)
    (deformationModel (centre X I) ⊥ k')
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint _
      (overRestrictι X I.support.compl).left (centreι X I).left
      (isCompl_range_overRestrictι_centreι I).disjoint (𝟙_ _))
  refine ⟨U, hζU, ?_⟩
  rw [restrictedZeroSectionNearbyCycles_obj]
  exact isZero_restrict_of_isZero_restrict_specializationDefect X I k' _ _ _ hΨ
    (hU.of_iso ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
      Profinite.continuousMapRingObj.{u} T⟧)).mapIso (e₁ ≪≫ e₂)))

/-- **The constant case of generic vanishing along a divisor, with finite coefficients**
(blueprint `lemma-vanishing-generic-points-principal-divisor`, for a finite coefficient ring `T`
killed by `ℓ ≠ char k'`): let `X` be normal, `Z = V(h)` for a nonzero global function `h`,
`j : X ∖ Z ⟶ X` the complement, `ζ` a generic point of `Z`, and `f₀ : W₀ ⟶ 𝔸¹_k` smooth on a
neighbourhood `W₀` of `ζ` such that `f₀^* x` is a uniformizer of `𝒪_{X,ζ}`. Then
`Le^* Ψ_X(j_! T̲)` vanishes near `ζ`. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_of_uniformizer_finiteCoefficient
    (hT : (ℓ : T) = 0) (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0)
    {I : X.left.IdealSheafData} (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (W₀ : X.left.Opens) (hζW₀ : I.subschemeι ζ ∈ W₀)
    (f₀ : overRestrict X W₀ ⟶ polyAffine k 1) [Smooth f₀.left]
    (hf₀ : Irreducible (X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) (I.subschemeι ζ)
      ⟨⟨I.subschemeι ζ, hζW₀⟩, trivial, rfl⟩ (f₀.left.appTop (polyAffineCoord k (Fin.last 0))))) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj.{u} T) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj.{u} T⟧)).obj (𝟙_ _)) := by
  obtain ⟨W, hζW, f, _, m, hm, hIW⟩ := exists_smooth_comap_polyAffineThickOrigin_of_uniformizer hX
    hh hI ζ hζ W₀ hζW₀ f₀ hf₀
  exact nearbyCyclesVanishNear_lowerShriek_unit_of_smooth_finiteCoefficient T k' hT I ζ W hζW f hm
    hIW

end Main

section Residue

open PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k]
  (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The constant case of generic vanishing along a divisor, with coefficients `𝔽_E`** (blueprint
`lemma-vanishing-generic-points-principal-divisor`): let `X` be normal, `Z = V(h)` for a nonzero
global function `h`, `j : X ∖ Z ⟶ X` the complement, `ζ` a generic point of `Z`, and
`f₀ : W₀ ⟶ 𝔸¹_k` smooth on a neighbourhood `W₀` of `ζ` such that `f₀^* x` is a uniformizer of the
discrete valuation ring `𝒪_{X,ζ}`. Then, for the residue field `𝔽_E` of a finite extension `E` of
`ℚ_ℓ`, the restricted specialization `Le^* Ψ_X(j_! 𝔽_E)` vanishes near `ζ`. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0)
    {I : X.left.IdealSheafData} (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (W₀ : X.left.Opens) (hζW₀ : I.subschemeι ζ ∈ W₀)
    (f₀ : overRestrict X W₀ ⟶ polyAffine k 1) [Smooth f₀.left]
    (hf₀ : Irreducible (X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) (I.subschemeι ζ)
      ⟨⟨I.subschemeι ζ, hζW₀⟩, trivial, rfl⟩ (f₀.left.appTop (polyAffineCoord k (Fin.last 0))))) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) :=
  nearbyCyclesVanishNear_lowerShriek_unit_of_uniformizer_finiteCoefficient
    (integersResidueField ℓ E.1) k' (PadicAlgCl.natCast_eq_zero_integersResidueField ℓ E.1) hX hh
    hI ζ hζ W₀ hζW₀ f₀ hf₀

end Residue

end AlgebraicGeometry.ProEtale.CondensedRing
