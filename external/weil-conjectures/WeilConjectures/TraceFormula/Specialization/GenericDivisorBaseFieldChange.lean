/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeFiniteCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.TraceFormula.Specialization.DeformationModelBaseFieldChange
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisse
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance

/-!

# Vanishing of the restricted specialization near a point descends along a change of base field

Let `k ⟶ K₀` be a field extension, `X` a separated `k`-scheme of finite type, `Z = V(I) ⊆ X`,
`X₀ = X ×_k K₀` with projection `π : X₀ ⟶ X` and `Z₀ = π⁻¹ Z = V(I₀)`. Let `k'` be a separably
closed extension of `k` and `K` a separably closed common extension of `K₀` and `k'`, purely
inseparable over `k'`. Then the deformation model of `(X₀, I₀)` over `Spec K⟦t⟧` is the base
change of the one of `(X, I)` over `Spec k'⟦t⟧` along the change of trait
(`ProEtale.CondensedRing.deformationModelBaseFieldHom`, `π` being flat), so by Deligne's
invariance of nearby cycles under change of trait (`NearbyCyclesModel.traitChangeInvariance`,
finite coefficients) the pullback exchange `Lπ_s^* Ψ_X(L) ⟶ Ψ_{X₀}(Lπ^* L)` is invertible for `L`
of étale origin (`ProEtale.CondensedRing.isIso_deformationModelBaseFieldHom_pullbackExchange_app`).

On the zero sections, `N_⊥ Z₀ = Z₀ ⊗_{K₀} K ⟶ N_⊥ Z = Z ⊗_k k'` is the base change of the
universal homeomorphism `Spec K ⟶ Spec k'`, along which derived pullback is an equivalence
(topological invariance). Hence the vanishing of `Le^* Ψ_X(L)` over an open of `N_⊥ Z` can be
checked after the change of base field.

## Main results

- `ProEtale.CondensedRing.isZero_restrictedZeroSectionNearbyCycles_of_overBaseChange`: if the
  restricted specialization of `Lπ^* L` vanishes over the inverse image of an open `U` of `Z`, so
  does the one of `L` over the inverse image of `U`.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_of_overBaseChange`: for `K₀/k` purely
  inseparable, the vanishing near a point `ζ₀` of `Z₀` for `Lπ^* L` implies the vanishing near its
  image `π_Z(ζ₀)` for `L`.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_of_overBaseChange_residueField`: the case of the
  coefficients `𝔽_E = 𝒪_E/ϖ`, `E ⊆ ℚ̄_ℓ` finite over `ℚ_ℓ`, with `ℓ` invertible in `k'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Derived pullbacks along universal homeomorphisms and composites -/

section Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Vanishing descends along a universal homeomorphism**: for a universal homeomorphism
`σ : A ⟶ B`, an open `W` of `B` and a complex `F` on `B`, if the restriction of `Lσ^* F` to
`σ⁻¹ W` vanishes, so does the restriction of `F` to `W`. Indeed `σ⁻¹ W ⟶ W` is a universal
homeomorphism, so the derived pullback along it is an equivalence. -/
lemma isZero_leftDerivedUpperStar_ι_obj_of_isUniversalHomeomorphism {A B : Scheme.{u}}
    (σ : A ⟶ B) [IsUniversalHomeomorphism σ] {W : B.Opens} {W₀ : A.Opens} (hW : W₀ = σ ⁻¹ᵁ W)
    {F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B))}
    (h : IsZero (L((W₀.ι)^*⟦Λ⟧).obj (L((σ)^*⟦Λ⟧).obj F))) :
    IsZero (L((W.ι)^*⟦Λ⟧).obj F) := by
  subst hW
  have : IsUniversalHomeomorphism (σ ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict σ W).flip ‹_›
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ (σ ∣_ W)
  have : ((σ ∣_ W)^*⟦Λ⟧).leftDerivedFunctor.IsEquivalence :=
    Functor.isEquivalence_of_iso (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  refine IsZero.of_full_of_faithful_of_isZero L(((σ ∣_ W))^*⟦Λ⟧) _ ?_
  have h₁ := isZero_leftDerivedUpperStar_obj_of_eq Λ (morphismRestrict_ι σ W).symm
    (h.of_iso ((leftDerivedUpperStarComp Λ _ _).app F))
  exact h₁.of_iso ((leftDerivedUpperStarComp Λ _ _).app F).symm

/-- The vanishing of `L w^* La^* Lb^* F` only depends on the composite `a ≫ b`. -/
lemma isZero_leftDerivedUpperStar_comp_obj_of_eq {A B C D E : Scheme.{u}} {a : A ⟶ B}
    {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (hw : a ≫ b = c ≫ d) (w : E ⟶ A)
    {F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D))}
    (h : IsZero (L((w)^*⟦Λ⟧).obj (L((a)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj F)))) :
    IsZero (L((w)^*⟦Λ⟧).obj (L((c)^*⟦Λ⟧).obj (L((d)^*⟦Λ⟧).obj F))) := by
  have h₁ := (h.of_iso ((leftDerivedUpperStarComp Λ w a).app _)).of_iso
    ((leftDerivedUpperStarComp Λ (w ≫ a) b).app F)
  rw [Category.assoc, hw, ← Category.assoc] at h₁
  exact (h₁.of_iso ((leftDerivedUpperStarComp Λ (w ≫ c) d).app F).symm).of_iso
    ((leftDerivedUpperStarComp Λ w c).app _).symm

end Abstract

/-! ### Invariance of nearby cycles along a change of base field -/

section General

variable {k K₀ : Type u} [Field k] [Field K₀] [Algebra k K₀] (k' K : Type u) [Field k'] [Field K]
  [Algebra k k'] [Algebra K₀ K] [Algebra k' K] [Algebra k K] [IsScalarTower k K₀ K]
  [IsScalarTower k k' K]
  {Y : Over (Spec (.of k))} {Y₀ : Over (Spec (.of K₀))} (h : Y₀.left ⟶ Y.left)
  (hh : h ≫ Y.hom = Y₀.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)))
  {J : Y.left.IdealSheafData} {J₀ : Y₀.left.IdealSheafData}
  (hJ : ∀ ⦃U' : Y₀.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ h ⁻¹ᵁ U.1), (J.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J₀.siteIdeal U')
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The residue field `k'` of `k'⟦t⟧`: a prime dividing the naturals vanishing in `k'` divides the
naturals vanishing in the residue field of `k'⟦t⟧`. -/
lemma dvd_of_natCast_residueField_powerSeries_eq_zero {p : ℕ}
    (hp : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (n : ℕ) (hn : (n : ResidueField (PowerSeries k')) = 0) :
    p ∣ n := by
  rw [← map_natCast (IsLocalRing.residue (PowerSeries k')), IsLocalRing.residue_eq_zero_iff,
    ← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker, map_natCast] at hn
  exact hp n hn

/-- **Invariance of nearby cycles under a change of base field** (finite coefficients `T`): if the
total space of the deformation model of `(Y₀, J₀)` over `Spec K⟦t⟧` is the base change of the one
of `(Y, J)` over `Spec k'⟦t⟧`, `k' ⊆ K` separably closed, then the pullback exchange of the
morphism of models `deformationModelBaseFieldHom` is invertible at every complex `L` on `Y` of
étale origin, for a prime `p` invertible in `T` dividing every natural number vanishing in `k'`.
This is Deligne's invariance of nearby cycles under change of strictly henselian trait
(`NearbyCyclesModel.traitChangeInvariance`). -/
theorem isIso_deformationModelBaseFieldHom_pullbackExchange_app [IsSepClosed k'] [IsSepClosed K]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (hT : IsPullback (deformationTotalBaseFieldMap k' K h hh hJ) (deformationTotalToTrait Y₀ J₀ K)
      (deformationTotalToTrait Y J k') (traitMap k' K))
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (hpT : IsUnit (p : T))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y.left)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y.left
      ((finiteCoefficientDerivedEquivalence Y.left T).functor.obj L)) :
    IsIso (((deformationModelBaseFieldHom k' K h hh hJ).pullbackExchange
      (Profinite.continuousMapRingObj T)).app L) := by
  have hK := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
    (deformationModel Y J k').ε hL
  have hNj : IsPullback (deformationModel Y J k').j
      (pullback.snd (deformationTotalToTrait Y J k') (traitGenericPoint k'))
      (deformationTotalToTrait Y J k')
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') (traitGenericField k')))) :=
    IsPullback.of_hasPullback _ _
  have hMj : IsPullback (deformationModel Y₀ J₀ K).j
      (pullback.snd (deformationTotalToTrait Y₀ J₀ K) (traitGenericPoint K))
      (deformationTotalToTrait Y₀ J₀ K)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) (traitGenericField K)))) :=
    IsPullback.of_hasPullback _ _
  have hMi : IsPullback (deformationModel Y₀ J₀ K).i (deformationSpecialFibre Y₀ J₀ K).hom
      (deformationTotalToTrait Y₀ J₀ K)
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) :=
    isPullback_deformationSpecialFibre Y₀ J₀ K
  have hφ : IsPullback (deformationModelBaseFieldHom k' K h hh hJ).total
      (deformationTotalToTrait Y₀ J₀ K) (deformationTotalToTrait Y J k')
      (Spec.map (CommRingCat.ofHom (PowerSeries.map (algebraMap k' K)))) := hT
  have hgen : (deformationModelBaseFieldHom k' K h hh hJ).generic ≫
      pullback.snd (deformationTotalToTrait Y J k') (traitGenericPoint k') =
      pullback.snd (deformationTotalToTrait Y₀ J₀ K) (traitGenericPoint K) ≫
        Spec.map (CommRingCat.ofHom (traitGenericFieldMap k' K)) :=
    deformationGenericBaseFieldMap_snd k' K h hh hJ
  exact isIso_pullbackExchange_app_of_isPullback_trait_finite T
    (PowerSeries.map_injective _ (algebraMap k' K).injective)
    (maximalIdeal_powerSeries_eq_map k' K) p
    (dvd_of_natCast_residueField_powerSeries_eq_zero k' hp) hpT
    (algebraMap_traitGenericField_injective k') (algebraMap_traitGenericField_injective K)
    (isAlgebraic_traitGenericField k') (isAlgebraic_traitGenericField K)
    (traitGenericFieldMap_comp_algebraMap k' K) PowerSeries.ker_coeff_eq_max_ideal
    (deformationModelBaseFieldHom k' K h hh hJ) (deformationTotalToTrait Y J k') _ hNj _ _ hMj _
    hMi hφ hgen L hK

/-- **Descent of the vanishing of the restricted specialization along a change of base field**
(general form). Let `h : Y₀ ⟶ Y` be the base change of `Y ⟶ Spec k` along `Spec K₀ ⟶ Spec k`
with `D_{J₀} Y₀ = Y₀ ×_Y D_J Y`, let `π_Z : Z₀ = V(J₀) ⟶ Z = V(J)` be the base change of `h` and
`U` an open of `Z`. If `K/k'` is purely inseparable (`k'`, `K` separably closed) and the restricted
specialization of `Lh^* L` vanishes over the inverse image of `π_Z⁻¹ U` in `N_⊥ Z₀`, then the
restricted specialization of `L` vanishes over the inverse image of `U` in `N_⊥ Z`. -/
theorem isZero_restrictedZeroSectionNearbyCycles_of_isPullback [IsSepClosed k'] [IsSepClosed K]
    [IsPurelyInseparable k' K] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    (hY : IsPullback h Y₀.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
    (hD : IsPullback (IdealSheafData.deformationSpaceMap h J J₀ hJ) J₀.deformationSpaceProj
      J.deformationSpaceProj h)
    (πZ : (centre Y₀ J₀).left ⟶ (centre Y J).left)
    (hZ : IsPullback πZ J₀.subschemeι J.subschemeι h)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (hpT : IsUnit (p : T))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y.left)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y.left
      ((finiteCoefficientDerivedEquivalence Y.left T).functor.obj L))
    (U : (centre Y J).left.Opens)
    (h₀ : IsZero ((restrictedZeroSectionNearbyCycles Y₀ J₀ K (Profinite.continuousMapRingObj T)
      ((constantSpecialFibreProj K (centre Y₀ J₀)) ⁻¹ᵁ (πZ ⁻¹ᵁ U))).obj
        (L((h)^*⟦Profinite.continuousMapRingObj T⟧).obj L))) :
    IsZero ((restrictedZeroSectionNearbyCycles Y J k' (Profinite.continuousMapRingObj T)
      ((constantSpecialFibreProj k' (centre Y J)) ⁻¹ᵁ U)).obj L) := by
  have hiso := isIso_deformationModelBaseFieldHom_pullbackExchange_app k' K h hY.w hJ T
    (isPullback_deformationTotalBaseFieldMap k' K h hY.w hJ
      (isPullback_deformationSpaceMap_affineLine h hJ hY hD)) p hp hpT L hL
  have hZY := hZ.paste_vert hY
  have hhZ := centre_hom_of_subschemeι h hY.w πZ hZ.w
  have hσ := isPullback_deformationSpecialBaseFieldMap k' K πZ hhZ
    (IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le)
    (isPullback_deformationTotalBaseFieldMap k' K πZ hhZ _
      (isPullback_deformationSpaceMap_affineLine πZ _ hZY
        (IdealSheafData.isPullback_deformationSpaceMap_bot πZ _)))
  have : IsUniversalHomeomorphism (deformationSpecialBaseFieldMap k' K πZ hhZ
      (IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le)) :=
    MorphismProperty.of_isPullback hσ.flip inferInstance
  have hW : constantSpecialFibreProj K (centre Y₀ J₀) ⁻¹ᵁ (πZ ⁻¹ᵁ U) =
      deformationSpecialBaseFieldMap k' K πZ hhZ
        (IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le) ⁻¹ᵁ
        (constantSpecialFibreProj k' (centre Y J) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      deformationSpecialBaseFieldMap_toBase]
  rw [restrictedZeroSectionNearbyCycles_obj] at h₀ ⊢
  refine isZero_leftDerivedUpperStar_ι_obj_of_isUniversalHomeomorphism _
    (deformationSpecialBaseFieldMap k' K πZ hhZ
      (IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le)) hW ?_
  refine isZero_leftDerivedUpperStar_comp_obj_of_eq _
    (zeroSection_deformationSpecialBaseFieldMap k' K h hY.w hJ πZ hZ.w) _ ?_
  exact h₀.of_iso ((L((((constantSpecialFibreProj K (centre Y₀ J₀)) ⁻¹ᵁ (πZ ⁻¹ᵁ U)).ι)^*⟦
    Profinite.continuousMapRingObj T⟧)).mapIso ((L(((zeroSectionSpecialFibreMap Y₀ J₀ K).left)^*⟦
      Profinite.continuousMapRingObj T⟧)).mapIso (asIso (((deformationModelBaseFieldHom k' K h hY.w
        hJ).pullbackExchange (Profinite.continuousMapRingObj T)).app L))))

/-- **Descent of the vanishing near a point along a purely inseparable change of base field**
(general form of `nearbyCyclesVanishNear_of_overBaseChange`): in the situation of
`isZero_restrictedZeroSectionNearbyCycles_of_isPullback` with `K₀/k` purely inseparable, so that
`π_Z` is a homeomorphism, if the restricted specialization of `Lh^* L` vanishes near a point `ζ₀`
of `Z₀`, then the restricted specialization of `L` vanishes near `π_Z(ζ₀)`. -/
theorem nearbyCyclesVanishNear_of_isPullback [IsPurelyInseparable k K₀] [IsSepClosed k']
    [IsSepClosed K] [IsPurelyInseparable k' K] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    (hY : IsPullback h Y₀.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
    (hD : IsPullback (IdealSheafData.deformationSpaceMap h J J₀ hJ) J₀.deformationSpaceProj
      J.deformationSpaceProj h)
    (πZ : (centre Y₀ J₀).left ⟶ (centre Y J).left)
    (hZ : IsPullback πZ J₀.subschemeι J.subschemeι h)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (hpT : IsUnit (p : T))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y.left)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y.left
      ((finiteCoefficientDerivedEquivalence Y.left T).functor.obj L))
    (ζ₀ : (centre Y₀ J₀).left)
    (h₀ : nearbyCyclesVanishNear Y₀ J₀ K (Profinite.continuousMapRingObj T) ζ₀
      (L((h)^*⟦Profinite.continuousMapRingObj T⟧).obj L)) :
    nearbyCyclesVanishNear Y J k' (Profinite.continuousMapRingObj T) (πZ ζ₀) L := by
  obtain ⟨U₀, hζU₀, hU₀⟩ := h₀
  have : IsUniversalHomeomorphism πZ := MorphismProperty.of_isPullback (hZ.paste_vert hY).flip
    inferInstance
  have hhom := Scheme.Hom.isHomeomorph πZ
  obtain ⟨U, hU⟩ : ∃ U : (centre Y J).left.Opens, (U : Set (centre Y J).left) =
      πZ '' SetLike.coe U₀ :=
    ⟨⟨_, hhom.isOpenMap _ U₀.2⟩, rfl⟩
  have hle : πZ ⁻¹ᵁ U ≤ U₀ := by
    intro x hx
    have hx' : _ ∈ (U : Set (centre Y J).left) := hx
    rw [hU] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    rwa [← hhom.injective hxy]
  have hζ : πZ ζ₀ ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact ⟨ζ₀, hζU₀, rfl⟩
  rw [restrictedZeroSectionNearbyCycles_obj] at hU₀
  refine ⟨U, hζ, isZero_restrictedZeroSectionNearbyCycles_of_isPullback k' K h hJ T hY hD πZ hZ p
    hp hpT L hL U ?_⟩
  rw [restrictedZeroSectionNearbyCycles_obj]
  exact isZero_leftDerivedUpperStar_ι_obj_of_le _ (Scheme.Hom.preimage_mono _ hle) hU₀

end General

/-! ### The base change `X ×_k K₀` -/

section OverBaseChange

variable {k K₀ : Type u} [Field k] [Field K₀] [Algebra k K₀] (k' K : Type u) [Field k'] [Field K]
  [Algebra k k'] [Algebra K₀ K] [Algebra k' K] [Algebra k K] [IsScalarTower k K₀ K]
  [IsScalarTower k k' K]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (I : X.left.IdealSheafData)

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The restriction `π_Z : Z₀ = π⁻¹ Z ⟶ Z` of the projection `π : X ×_k K₀ ⟶ X` is its base change
along `Z ⟶ X`. -/
lemma isPullback_subschemeMap_overBaseChange :
    IsPullback (IdealSheafData.subschemeMap _ _
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
        (I.le_map_comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))))
      (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))).subschemeι
      I.subschemeι (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))) := by
  have := (I.isPullback_comap
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))).flip
  rwa [IdealSheafData.comapIso_hom_snd] at this

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Descent of the vanishing of the restricted specialization along a change of base field.**
Let `X₀ = X ×_k K₀` with projection `π : X₀ ⟶ X`, `I₀ = π⁻¹ I`, `π_Z : Z₀ = V(I₀) ⟶ Z = V(I)`
the restriction of `π`, and `U` an open of `Z`. Let `k ⊆ k' ⊆ K` and `K₀ ⊆ K` with `k'`, `K`
separably closed and `K/k'` purely inseparable, and let `L` be a complex on `X` of étale origin
with finite coefficients `T` in which a prime `p` dividing the naturals vanishing in `k'` is
invertible. If the restricted specialization of `Lπ^* L` vanishes over the inverse image of
`π_Z⁻¹ U` in `N_⊥ Z₀`, then the restricted specialization of `L` vanishes over the inverse image of
`U` in `N_⊥ Z`. -/
theorem isZero_restrictedZeroSectionNearbyCycles_of_overBaseChange [IsSepClosed k']
    [IsSepClosed K] [IsPurelyInseparable k' K]
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (hpT : IsUnit (p : T))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X.left
      ((finiteCoefficientDerivedEquivalence X.left T).functor.obj L))
    (U : (centre X I).left.Opens)
    (h₀ : IsZero ((restrictedZeroSectionNearbyCycles
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X)
      (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))) K
      (Profinite.continuousMapRingObj T)
      ((constantSpecialFibreProj K (centre
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X)
        (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))))) ⁻¹ᵁ
        ((IdealSheafData.subschemeMap _ _
          (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
          (I.le_map_comap (pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))) ⁻¹ᵁ U))).obj
      (L(((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))^*⟦
        Profinite.continuousMapRingObj T⟧).obj L))) :
    IsZero ((restrictedZeroSectionNearbyCycles X I k' (Profinite.continuousMapRingObj T)
      ((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U)).obj L) := by
  have : Flat (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact isZero_restrictedZeroSectionNearbyCycles_of_isPullback k' K
    (Y₀ := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X)
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
    (IdealSheafData.map_siteIdeal_le_comap _ I) T (IsPullback.of_hasPullback _ _)
    (IdealSheafData.isPullback_deformationSpaceMap_of_flat _ I _ _ rfl) _
    (isPullback_subschemeMap_overBaseChange X I) p hp hpT L hL U h₀

/-- **Vanishing near a point descends along a purely inseparable change of base field.** Let
`X₀ = X ×_k K₀` for a purely inseparable extension `K₀/k`, with projection `π : X₀ ⟶ X`,
`I₀ = π⁻¹ I` and `π_Z : Z₀ = V(I₀) ⟶ Z = V(I)` (a homeomorphism). In the situation of
`isZero_restrictedZeroSectionNearbyCycles_of_overBaseChange`, if the restricted specialization of
`Lπ^* L` vanishes near a point `ζ₀` of `Z₀`, then the restricted specialization of `L` vanishes
near `π_Z(ζ₀)`. -/
theorem nearbyCyclesVanishNear_of_overBaseChange [IsPurelyInseparable k K₀] [IsSepClosed k']
    [IsSepClosed K] [IsPurelyInseparable k' K]
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : k') = 0 → p ∣ n) (hpT : IsUnit (p : T))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X.left
      ((finiteCoefficientDerivedEquivalence X.left T).functor.obj L))
    (ζ₀ : (centre ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X)
      (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))).left)
    (h : nearbyCyclesVanishNear ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k K₀)))).obj X)
      (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))) K
      (Profinite.continuousMapRingObj T) ζ₀
      (L(((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))^*⟦
        Profinite.continuousMapRingObj T⟧).obj L)) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj T)
      (IdealSheafData.subschemeMap _ _
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
        (I.le_map_comap (pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))) ζ₀) L := by
  have : Flat (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact nearbyCyclesVanishNear_of_isPullback k' K
    (Y₀ := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X)
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
    (IdealSheafData.map_siteIdeal_le_comap _ I) T (IsPullback.of_hasPullback _ _)
    (IdealSheafData.isPullback_deformationSpaceMap_of_flat _ I _ _ rfl) _
    (isPullback_subschemeMap_overBaseChange X I) p hp hpT L hL ζ₀ h

/-- **Vanishing near a point descends along a purely inseparable change of base field**, for the
coefficients `𝔽_E = 𝒪_E/ϖ` of a finite extension `E` of `ℚ_ℓ` in `ℚ̄_ℓ`, `ℓ` invertible in `k'`
(`nearbyCyclesVanishNear_of_overBaseChange`). -/
theorem nearbyCyclesVanishNear_of_overBaseChange_residueField [IsPurelyInseparable k K₀]
    [IsSepClosed k'] [IsSepClosed K] [IsPurelyInseparable k' K] {ℓ : ℕ} [Fact ℓ.Prime]
    [Fact (ringChar k' ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj
        (PadicAlgCl.integersResidueField ℓ E.1)) X.left)))
    (hL : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) X.left
      ((finiteCoefficientDerivedEquivalence X.left
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj L))
    (ζ₀ : (centre ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X)
      (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))).left)
    (h : nearbyCyclesVanishNear ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k K₀)))).obj X)
      (I.comap (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))) K
      (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)) ζ₀
      (L(((pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))^*⟦Profinite.continuousMapRingObj
          (PadicAlgCl.integersResidueField ℓ E.1)⟧).obj L)) :
    nearbyCyclesVanishNear X I k'
      (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1))
      (IdealSheafData.subschemeMap _ _
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))
        (I.le_map_comap (pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K₀))))) ζ₀) L := by
  refine (exists_prime_ne_dvd_of_natCast_eq_zero k' ‹Fact (ringChar k' ≠ ℓ)›.out).elim
    fun p hp ↦ ?_
  have : Fact p.Prime := ⟨hp.1⟩
  exact nearbyCyclesVanishNear_of_overBaseChange k' K X I _ p hp.2.2
    (isUnit_natCast_integersResidueField E.1 hp.1 hp.2.1) L hL ζ₀ h

end OverBaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
