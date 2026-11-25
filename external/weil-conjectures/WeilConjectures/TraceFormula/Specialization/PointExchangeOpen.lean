/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchange

/-!
# The compact-support exchange of the structure map of a separated scheme

For separated `X` of finite type over `k` with rational point `x`, the exchange `ν_X` of blueprint
`prose-E-15` (3) is `ν_{X̄}(u_!) ∘ Ra'_{X̄!}(ν_u)` for `u : X ⟶ X̄` the open immersion
into the compactification of `X ⟶ Spec k`, `ν_u : u'_! Ψ_X ⟶ Ψ_{X̄} u_!` the mate of `α_u⁻¹`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The shape of `ν_X`: `LSa' ≅ Lu' ⋙ LSb'`, the mate of `α⁻¹`, `ν_Y`, `Lu ⋙ LSb ≅ LSa`. -/
noncomputable def openExchangeAux {A A' B B' P P' : Type*} [Category A] [Category A']
    [Category B] [Category B'] [Category P] [Category P'] {SpA : A ⥤ A'} {SpB : B ⥤ B'}
    {Ts : P ⥤ P'} {Lu : A ⥤ B} {Ru : B ⥤ A} {Lu' : A' ⥤ B'} {Ru' : B' ⥤ A'} {LSa : A ⥤ P}
    {LSb : B ⥤ P} {LSa' : A' ⥤ P'} {LSb' : B' ⥤ P'} (adj : Lu ⊣ Ru) (adj' : Lu' ⊣ Ru')
    (α : SpB ⋙ Ru' ⟶ Ru ⋙ SpA) (hα : IsIso α) (i' : LSa' ≅ Lu' ⋙ LSb') (i : LSa ≅ Lu ⋙ LSb)
    (νY : SpB ⋙ LSb' ⟶ LSb ⋙ Ts) : SpA ⋙ LSa' ⟶ LSa ⋙ Ts :=
  Functor.whiskerLeft SpA i'.hom ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ (inv α))) LSb' ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Lu νY ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight i.inv Ts

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (x : RationalPoint X) (u : X ⟶ Y)
  [IsOpenImmersion u.left]

/-- Along an open immersion `u`, the ideal of `x ≫ u` restricts to the ideal of `x`. -/
lemma ker_eq_comap_of_isOpenImmersion : x.left.ker = (x ≫ u).left.ker.comap u.left := by
  have : IsClosedImmersion (x ≫ u).left := isClosedImmersion_of_comp_eq_id Y.hom _ (Over.w (x ≫ u))
  have sq : IsPullback x.left (𝟙 _) u.left (x ≫ u).left := by
    simpa using (IsPullback.of_vert_isIso (fst := x.left) (snd := 𝟙 _) (f := 𝟙 _) (g := x.left)
      ⟨by simp⟩).paste_horiz (IsKernelPair.id_of_mono u.left)
  rw [← sq.isoPullback_hom_fst, Hom.ker_comp_of_isIso, IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The compatibility `u^* I ⊆ J` of the ideals of `x ≫ u` and `x`. -/
lemma ker_compatible_of_isOpenImmersion ⦃U' : X.left.AffineZariskiSite⦄
    ⦃U : Y.left.AffineZariskiSite⦄ (hU : U'.1 ≤ u.left ⁻¹ᵁ U.1) :
    ((x ≫ u).left.ker.siteIdeal U).map (u.left.appLE U.1 U'.1 hU).hom ≤
      x.left.ker.siteIdeal U' :=
  ker_eq_comap_of_isOpenImmersion x u ▸ IdealSheafData.map_siteIdeal_le_comap _ _ hU

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [IsProper Y.hom]
  (k' : Type u) [Field k'] [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The compact-support exchange `ν_X` along an open immersion into a proper `Y`** (blueprint
`prose-E-15` (3)): `ν_X = ν_Y(u_!) ∘ Ra'_{Y!}(ν_u)`, `ν_u` the mate of `α_u⁻¹`. -/
noncomputable def pointCompactSupportExchangeOfOpenImmersion :
    Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x :=
  have hJ := ker_compatible_of_isOpenImmersion x u
  have hM := (deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel X _ k') (deformationModel_exists_comp_ε X _ k')
  have hN := (deformationModel Y (x ≫ u).left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel Y _ k') (deformationModel_exists_comp_ε Y _ k')
  have : IsOpenImmersion (deformationModelHom u hJ k').total :=
    isOpenImmersion_deformationTotalMap u hJ k' (ker_eq_comap_of_isOpenImmersion x u)
  have : IsOpenImmersion (deformationSpecialFibreMap u hJ k').left :=
    MorphismProperty.of_isPullback (IsPullback.of_right (by
        rw [Over.w, deformationTotalMap_toTrait]
        exact (isPullback_deformationSpecialFibre X _ k').flip)
      (deformationSpecialFibreMap_toTotal u _ k')
      (isPullback_deformationSpecialFibre Y _ k').flip).flip this
  openExchangeAux (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ u)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ _)
    ((deformationModelHom u hJ k').boundedConstructiblePullbackExchange ℓ hM hN)
    ((deformationModelHom u hJ k').isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion
      ℓ hM hN (isPullback_deformationGenericMap u hJ k'))
    (lowerShriekCompOfEq ℓ (deformationSpecialFibreMap u hJ k') (toPoint _) (comp_toPoint _) ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ _) _)
    (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _)
    (pointCompactSupportExchange Y (x ≫ u) k')

/-- **The compact-support exchange `ν_X` of a separated `X`** (blueprint `prose-E-15`
(3)): `pointCompactSupportExchangeOfOpenImmersion` for the compactification `X ⊂ X̄` of `a_X`. -/
noncomputable def pointCompactSupportExchangeOfSeparated :
    Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x :=
  have := (compactificationOverField (toPoint X)).isProper
  have : IsProper (compactificationOverField (toPoint X)).overObj.hom :=
    inferInstanceAs (IsProper (_ ≫ 𝟙 _))
  pointCompactSupportExchangeOfOpenImmersion x (compactificationOverField (toPoint X)).overI k'

end AlgebraicGeometry.ProEtale.CondensedRing
