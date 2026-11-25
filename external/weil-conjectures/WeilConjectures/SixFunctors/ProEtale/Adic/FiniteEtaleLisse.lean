/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris

/-!
# The pushforward of a lisse `ℓ`-adic sheaf along a finite étale morphism is lisse

Let `g : Y ⟶ X` be finite étale and `F` a lisse `ℓ`-adic sheaf on `Y_proét`. Then `g_* F` is
lisse (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.lowerStar_of_finite_etale`). Being lisse is
local on `X`, and `g` is étale-locally on `X` a trivial cover
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`): there are an étale
`u : U ⟶ X` around any point and a finite set `S` with `Y ×_X U ≅ ∐_{s ∈ S} U`. By weakly étale
base change (`AlgebraicGeometry.ProEtale.isIso_adicBaseChangeMap_of_isPullback`), `u^* g_* F` is
the pushforward of the lisse sheaf `G = F|_{Y ×_X U}` along the codiagonal `∇ : ∐_S U ⟶ U`. On a
finite disjoint union the sheaf `G` is the product of the pushforwards of its restrictions
`ι_s^* G` to the summands
(`AlgebraicGeometry.ProEtale.isIso_pi_lift_adicUpperStarLowerStarAdjunction_unit`),
so `∇_* G ≅ ∏_s ι_s^* G` is a finite product of lisse sheaves.

## Main declarations

- `AlgebraicGeometry.ProEtale.adicLowerStarSigmaIso`: `p_* G ≅ ∏_s (p ∘ ι_s)_* ι_s^* G` for a
  morphism `p` out of a finite disjoint union.
- `AlgebraicGeometry.ProEtale.adicLisseSheaf`: lisse sheaves as an object property, closed under
  finite products (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.pi`).
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.lowerStar_of_finite_etale`: the pushforward of a
  lisse sheaf along a finite étale morphism is lisse.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Abelian.hasFiniteBiproducts

variable (l : ℕ) [Fact l.Prime]

/-- **A sheaf on a finite disjoint union is the product of its restrictions to the summands**:
for `ι_s : U_s ⟶ ∐_s U_s`, the units `G ⟶ ι_{s*} ι_s^* G` induce an isomorphism
`G ≅ ∏_s ι_{s*} ι_s^* G`. It is checked on the Zariski cover by the summands: the restriction
along `ι_t` of the `t`-th unit is invertible, `ι_{t*}` being fully faithful, and
`ι_t^* ι_{s*}` vanishes for `s ≠ t`, the summands being disjoint. -/
lemma isIso_pi_lift_adicUpperStarLowerStarAdjunction_unit {S : Type u} [Finite S]
    (U : S → Scheme.{u}) (G : AdicSheaf l (∐ U)) :
    IsIso (Pi.lift fun s ↦ (adicUpperStarLowerStarAdjunction l (Sigma.ι U s)).unit.app G) := by
  refine isIso_of_isIso_adicUpperStar l (Sigma.ι U) ?_ _ fun t ↦ ?_
  · refine Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun s ↦ inferInstance⟩)
    obtain ⟨s, y, rfl⟩ := (sigmaOpenCover U).exists_eq x
    exact ⟨s, y, rfl⟩
  rw [← isIso_comp_right_iff _ (PreservesProduct.iso (Sigma.ι U t)^*ᵃ[l] _).hom,
    PreservesProduct.iso_hom, map_lift_piComparison]
  refine isIso_pi_lift_of_isZero _ t ?_ fun s hst ↦ ?_
  · have h := (adicUpperStarLowerStarAdjunction l (Sigma.ι U t)).left_triangle_components G
    have : IsIso ((Sigma.ι U t)^*ᵃ[l].map
        ((adicUpperStarLowerStarAdjunction l (Sigma.ι U t)).unit.app G) ≫
        (adicUpperStarLowerStarAdjunction l (Sigma.ι U t)).counit.app _) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((adicUpperStarLowerStarAdjunction l (Sigma.ι U t)).counit.app _)
  · have hjk : Set.range (Sigma.ι U s).base ∩ Set.range (Sigma.ι U t).base = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ hst ?_
      exact congrArg Sigma.fst ((sigmaι_eq_iff U s t a b).mp (ha.trans hb.symm))
    exact AdicSheaf.isZero_of_isZero_X ((isZero_openImmersionRestriction_lowerStar _
      (Sigma.ι U s) (Sigma.ι U t) hjk _).of_iso
      ((upperStarIsoOpenImmersionRestriction _ (Sigma.ι U t)).app _))

/-- **Pushforward out of a finite disjoint union**: for `p : ∐_s U_s ⟶ W` and a sheaf `G` on
`∐_s U_s`, `p_* G ≅ ∏_s (ι_s ≫ p)_* ι_s^* G`. -/
noncomputable def adicLowerStarSigmaIso {S : Type u} [Finite S] {U : S → Scheme.{u}}
    {W : Scheme.{u}} (p : ∐ U ⟶ W) (G : AdicSheaf l (∐ U)) :
    (p)_*ᵃ[l].obj G ≅
      ∏ᶜ fun s ↦ (Sigma.ι U s ≫ p)_*ᵃ[l].obj ((Sigma.ι U s)^*ᵃ[l].obj G) :=
  haveI := (adicUpperStarLowerStarAdjunction l p).rightAdjoint_preservesLimits
  (p)_*ᵃ[l].mapIso (@asIso _ _ _ _ (Pi.lift fun s ↦
    (adicUpperStarLowerStarAdjunction l (Sigma.ι U s)).unit.app G)
    (isIso_pi_lift_adicUpperStarLowerStarAdjunction_unit l U G)) ≪≫
    PreservesProduct.iso (p)_*ᵃ[l] _ ≪≫ Pi.mapIso fun _ ↦ (adicLowerStarComp l _ p).app _

variable (X : Scheme.{u})

/-- Lisseness of `ℓ`-adic pro-étale sheaves, as an object property. -/
def adicLisseSheaf : ObjectProperty (AdicSheaf l X) :=
  fun F ↦ IsAdicLisseSheaf F

instance : (adicLisseSheaf l X).IsClosedUnderIsomorphisms where
  of_iso e hF := IsAdicLisseSheaf.of_iso e hF

instance : (adicLisseSheaf l X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, IsAdicLisseSheaf.of_isZero (isZero_zero _)⟩

/-- **Finite products of lisse sheaves are lisse**: the empty product is `0`, and a binary
product is a binary direct sum (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.biprod`). -/
instance : (adicLisseSheaf l X).IsClosedUnderFiniteProducts := by
  have : (adicLisseSheaf l X).IsClosedUnderBinaryProducts := by
    refine ⟨fun Y ⟨p⟩ ↦ ?_⟩
    exact IsAdicLisseSheaf.of_iso
      (biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair _)).symm ≪≫
        (p.isLimit.conePointUniqueUpToIso (limit.isLimit _)).symm)
      ((p.prop_diag_obj ⟨.left⟩).biprod (p.prop_diag_obj ⟨.right⟩))
  exact .mk'

variable {l X}

/-- A finite product of lisse sheaves is lisse. -/
theorem IsAdicLisseSheaf.pi {S : Type*} [Finite S] {F : S → AdicSheaf l X}
    (hF : ∀ s, IsAdicLisseSheaf (F s)) : IsAdicLisseSheaf (∏ᶜ F) :=
  (adicLisseSheaf l X).prop_product hF

/-- The pushforward of a lisse sheaf along the codiagonal `∇ : ∐_{s ∈ S} W ⟶ W` of a trivial
finite cover is lisse: it is the product of the restrictions to the summands
(`AlgebraicGeometry.ProEtale.adicLowerStarSigmaIso`). -/
theorem IsAdicLisseSheaf.lowerStar_sigmaDesc_id {S : Type u} [Finite S] {W : Scheme.{u}}
    {G : AdicSheaf l (∐ fun _ : S ↦ W)} (hG : IsAdicLisseSheaf G) :
    IsAdicLisseSheaf ((Sigma.desc fun _ : S ↦ 𝟙 W)_*ᵃ[l].obj G) := by
  refine IsAdicLisseSheaf.of_iso (adicLowerStarSigmaIso l _ G).symm
    (IsAdicLisseSheaf.pi fun s ↦ ?_)
  have e (M : AdicSheaf l W) :
      (Sigma.ι (fun _ : S ↦ W) s ≫ Sigma.desc fun _ ↦ 𝟙 W)_*ᵃ[l].obj M ≅ M :=
    (adicLowerStarCongr l (Sigma.ι_comp_desc (fun _ : S ↦ 𝟙 W) s)).app M ≪≫
      (adicLowerStarId l W).app M
  exact (hG.upperStar _).of_iso (e _).symm

/-- **The pushforward of a lisse sheaf along a finite étale morphism is lisse.** Étale locally
on `X`, `g` is a trivial cover `∐_{s ∈ S} U ⟶ U`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`), and by weakly étale
base change the restriction of `g_* F` is the pushforward of a lisse sheaf along the codiagonal
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.lowerStar_sigmaDesc_id`). This is the lissity part
of the blueprint lemmas `lemma-finite-generically-etale-map-line--2` and
`lemma-finite-quasi-finite-direct-images--3`. -/
theorem IsAdicLisseSheaf.lowerStar_of_finite_etale {Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g]
    [Etale g] {F : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) :
    IsAdicLisseSheaf ((g)_*ᵃ[l].obj F) := by
  let P : X.FiniteEtale := ⟨Scheme.Etale.mk g, inferInstanceAs (IsFinite g)⟩
  choose U u hu S hS fst hx hsq using Scheme.FiniteEtale.exists_etale_isPullback_sigma P
  refine IsAdicLisseSheaf.of_cover u ?_ fun x ↦ ?_
  · exact Scheme.etalePrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ⟨x, hx x⟩, hu⟩)
  have : Etale (fst x) := MorphismProperty.of_isPullback (hsq x).flip (hu x)
  have := isIso_adicBaseChangeMap_of_isPullback l (hsq x).flip
  exact (hF.upperStar (fst x)).lowerStar_sigmaDesc_id.of_iso
    (asIso ((adicBaseChangeMap l (hsq x).flip.toCommSq).app F)).symm

end AlgebraicGeometry.ProEtale
