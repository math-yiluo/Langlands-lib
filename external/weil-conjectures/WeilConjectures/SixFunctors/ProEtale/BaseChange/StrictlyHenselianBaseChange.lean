/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonUnit

/-!
# Base change between strictly henselian local rings at the closed point

Let `ι : R₁ ⟶ R₂` be a local homomorphism of strictly henselian local rings,
`tᵢ : Spec Ωᵢ ⟶ Spec Rᵢ`
morphisms from spectra of separably closed fields and `c : Spec Ω₂ ⟶ Spec Ω₁` with
`c ≫ t₁ = t₂ ≫ Spec ι`, and `b : R₂ ⟶ κ` a map to a field with kernel the maximal ideal. This
square is not cartesian, and its base change morphism `L(Spec ι)^* Rt₁_* ⟶ Rt₂_* Lc^*` is not
invertible; but it becomes invertible after pullback to the closed point `Spec b` of `Spec R₂`, at
every complex bounded below of étale origin
(`isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing`).
For strictly henselian traits with geometric generic points, this says that the nearby cycles of
the trait itself are invariant under change of trait, the step (B) of the proof of SGA 4½,
[Th. finitude], Prop. 3.7.

Every complex `L` bounded below of étale origin on `Spec Ω₁` is `Lt₁^* F` for `F = ν^* G` with `G`
a complex on `Spec R₁` with constant cohomology sheaves
(`AlgebraicGeometry.Etale.exists_isConstant_homology_iso_upperStar_obj`). At such an `L`, the base
change morphism composed with `L(Spec ι)^*` of the unit `F ⟶ Rt₁_* Lt₁^* F` is the unit at
`L(Spec ι)^* F` followed by an isomorphism (`CategoryTheory.unit_mateEquiv`). After pullback to the
closed point both units are invertible
(`ProEtale.isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology`): the second since
`L(Spec ι)^* F` is again `ν^*` of a complex with constant cohomology sheaves, the first since the
composite `Spec b ≫ Spec ι` is a closed point of `Spec R₁`, `ι` being local.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Base change between strictly henselian local rings at the closed point.** Let
`ι : R₁ ⟶ R₂` be a local homomorphism of strictly henselian local rings, `t₁ : Spec Ω₁ ⟶ Spec R₁`
and `t₂ : Spec Ω₂ ⟶ Spec R₂` morphisms from spectra of separably closed fields, and
`c : Spec Ω₂ ⟶ Spec Ω₁` with `c ≫ t₁ = t₂ ≫ Spec ι`. For `b : R₂ ⟶ κ` a map to a field with kernel
the maximal ideal, the pullback along `Spec b` of the base change morphism
`L(Spec ι)^* Rt₁_* L ⟶ Rt₂_* Lc^* L` is an isomorphism for every complex `L` bounded below of
étale origin. -/
theorem isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing
    {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
    [IsStrictlyHenselianLocalRing R₂] (ι : R₁ →+* R₂) [IsLocalHom ι]
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]
    {t₁ : Spec (.of Ω₁) ⟶ Spec (.of R₁)} {t₂ : Spec (.of Ω₂) ⟶ Spec (.of R₂)}
    {c : Spec (.of Ω₂) ⟶ Spec (.of Ω₁)} (sq : CommSq c t₂ t₁ (Spec.map (CommRingCat.ofHom ι)))
    {κ : Type u} [Field κ] (b : R₂ →+* κ) (hb : RingHom.ker b = IsLocalRing.maximalIdeal R₂)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology (Spec (.of Ω₁))) (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) _ L) :
    IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b))).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app L)) := by
  obtain ⟨L', hL', ⟨e⟩⟩ := hL
  obtain ⟨G, hG, ⟨e'⟩⟩ :=
    AlgebraicGeometry.Etale.exists_isConstant_homology_iso_upperStar_obj Λ t₁ ⟨L', hL'⟩
  -- `L ≅ Lt₁^* F` with `F = ν^* G`
  let F := (DerivedCategory.Plus.ι ⋙ D(ν^*(Spec (.of R₁))[ModuleCat.{u + 1} Λ])).obj G
  let eL : L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) t₁).obj F ≅ L :=
    ((leftDerivedUpperStarComparisonIso t₁ Λ).app G).symm ≪≫
      (DerivedCategory.Plus.ι ⋙ D(ν^*(Spec (.of Ω₁))[ModuleCat.{u + 1} Λ])).mapIso e' ≪≫ e
  let τ := Functor.whiskerRight (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq)
    L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b)))
  suffices h : IsIso (τ.app (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) t₁).obj F)) from
    (NatTrans.isIso_app_iff_of_iso τ eL).1 h
  -- the unit identity of the base change morphism
  have hunit := unit_mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₁)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₂)
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq).hom F
  have h₂ := congrArg
    (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b)))).map hunit
  simp only [Functor.map_comp] at h₂
  -- the unit of `S₁`, restricted to the closed point of `S₂`
  have hker : RingHom.ker (b.comp ι) = IsLocalRing.maximalIdeal R₁ := by
    rw [← RingHom.comap_ker, hb, IsLocalRing.maximalIdeal_comap]
  have hs : Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom (b.comp ι)) := (Spec.map_comp _ _).symm
  have i₁ : IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom b))).map (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (Spec.map (CommRingCat.ofHom ι))).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₁).unit.app F))) := by
    have h := isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology Λ R₁ t₁ (b.comp ι)
      hker G hG
    rw [← NatIso.isIso_map_iff (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hs)] at h
    exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _) _).1 h
  -- the unit of `S₂` at `L(Spec ι)^* F = ν^* (Spec ι)^* G`
  have i₂ : IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom b))).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₂).unit.app
          (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom ι))).obj F))) := by
    have h := isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology Λ R₂ t₂ b hb
      (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom ι))).obj G)
      (AlgebraicGeometry.Etale.isConstant_homology_upperStar_obj Λ _ G hG)
    exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₂).unit
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b))))
      ((leftDerivedUpperStarComparisonIso (Spec.map (CommRingCat.ofHom ι)) Λ).app G)).1 h
  have : IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom b))).map (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (Spec.map (CommRingCat.ofHom ι))).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₁).unit.app F)) ≫
      τ.app (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) t₁).obj F)) := by
    erw [h₂]
    refine IsIso.comp_isIso' ?_ ?_
    · exact i₂
    · exact Functor.map_isIso _ _
  have := i₁
  exact IsIso.of_isIso_comp_left (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom b))).map (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (Spec.map (CommRingCat.ofHom ι))).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t₁).unit.app F)))
    (τ.app (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) t₁).obj F))

end AlgebraicGeometry.ProEtale
