/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Morphisms into lisse sheaves are detected on a generizing open

Let `k : W ⟶ Y` be weakly étale (for instance an open immersion) such that every point of `Y`
is a specialization of a point in the image of `k`; for `Y` irreducible this says that the
image of `k` contains the generic point. Then a morphism `φ : N ⟶ H` of `ℓ`-adic sheaves into a
lisse sheaf `H` vanishes as soon as its pullback `k^* φ` does
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero`).

For `H = ℚ̄_ℓ` this is continuity: a section of `ℚ̄_ℓ` over `U ⟶ Y` weakly étale is a continuous
function on `U`, its image under `φ` vanishes on the preimage of `W`, and every point of `U` is a
specialization of a point of that preimage, weakly étale morphisms being flat and so lifting
generizations; a continuous function to the Hausdorff space `ℚ̄_ℓ` is constant along
specializations. The lisse case reduces to this one on a trivialising cover.

On a smooth curve this is the fact that a lisse sheaf has no nonzero punctual subsheaf, used for
the curve perverse t-structure (blueprint `lemma-perverse-sheaves-curve`, Step 0).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y W : Scheme.{u}}

/-- A morphism `ψ : N ⟶ ℚ̄_ℓ` of pro-étale sheaves vanishes as soon as its pullback along a
weakly étale `k : W ⟶ Y` does, provided every point of `Y` specializes from the image of `k`: a
section of `ℚ̄_ℓ` is a continuous function, it vanishes on the preimage of `W`, and every point
specializes from a point of that preimage. -/
lemma eq_zero_of_upperStar_map_eq_zero_of_specializes (k : W ⟶ Y) [h : WeaklyEtale k]
    (hk : ∀ y : Y, ∃ w : W, k.base w ⤳ y)
    {N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)}
    (ψ : N ⟶ adicConstantSheaf l Y) (hψ : (k)^*[WeilCoefficients.{u} l].map ψ = 0) :
    ψ = 0 := by
  have hres : (localizationRestriction (WeilCoefficients.{u} l) k h).map ψ = 0 := by
    have := (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) k h).hom.naturality ψ
    rw [hψ, zero_comp] at this
    rw [← cancel_epi ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) k h).hom.app
      N), ← this, comp_zero]
  ext U : 3
  ext x
  induction U using Opposite.rec with | op U => ?_
  change ψ.hom.app (op U) x = 0
  set c := ψ.hom.app (op U) x with hc
  -- the restriction of `c` to `U ×_Y W` vanishes
  let b : W.ProEt := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).obj U
  let ε : (MorphismProperty.Over.map ⊤ h).obj b ⟶ U :=
    MorphismProperty.Over.homMk (pullback.fst U.hom k) pullback.condition trivial
  have h1 : ψ.hom.app (op ((MorphismProperty.Over.map ⊤ h).obj b)) = 0 :=
    congrArg (fun φ ↦ φ.hom.app (op b)) hres
  have h2 := congrArg (fun φ ↦ φ x) (ψ.hom.naturality ε.op)
  simp only [h1] at h2
  have hz : ∀ p, c.down.1 ((pullback.fst U.hom k).base p) = 0 := by
    intro p
    have := congrArg (fun y ↦ y.down.1 p) h2
    simp only [comp_zero] at this
    exact this.symm
  -- every point of `U` specializes from a point of `U ×_Y W`
  refine adicConstantSheaf_ext (l := l) fun y ↦ ?_
  have : WeaklyEtale U.hom := U.prop
  obtain ⟨w, hw⟩ := hk (U.hom.base y)
  obtain ⟨y', hy', hy'w⟩ := Flat.generalizingMap U.hom hw
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := k) y' w hy'w
  rw [← (hy'.map c.down.1.continuous).eq, ← hp1, hz p]
  rfl

/-- **Morphisms into a lisse sheaf are detected on a generizing open.** Let `k : W ⟶ Y` be
weakly étale such that every point of `Y` specializes from a point in the image of `k`, and let
`H` be a lisse `ℓ`-adic sheaf on `Y`. A morphism `φ : N ⟶ H` with `k^* φ = 0` vanishes: on a
trivialising cover `f_i : V_i ⟶ Y` its components are morphisms into `ℚ̄_ℓ` whose pullbacks to
`V_i ×_Y W` vanish, and `V_i ×_Y W ⟶ V_i` inherits the specialization property because the flat
`f_i` lifts generizations
(`AlgebraicGeometry.ProEtale.eq_zero_of_upperStar_map_eq_zero_of_specializes`). -/
theorem IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero (k : W ⟶ Y) [WeaklyEtale k]
    (hk : ∀ y : Y, ∃ w : W, k.base w ⤳ y) {N H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H)
    (φ : N ⟶ H) (hφ : (k)^*ᵃ[l].map φ = 0) : φ = 0 := by
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  refine ProEtale.eq_zero_of_adicUpperStar_map_eq_zero f hR φ fun i ↦ ?_
  rw [← cancel_mono (e i).some.hom, zero_comp]
  refine biproduct.hom_ext _ _ fun a ↦ ?_
  rw [zero_comp, Category.assoc]
  set ψ := (f i)^*ᵃ[l].map φ ≫ (e i).some.hom ≫
    biproduct.π (fun _ : Fin (n i) ↦ AdicSheaf.unit l (V i)) a
  -- the pullback of `ψ` to `W ×_Y V i` vanishes
  have hψ : (pullback.snd k (f i))^*ᵃ[l].map ψ = 0 := by
    have e1 := (adicUpperStarCompIso l (pullback.condition (f := k) (g := f i))).hom.naturality φ
    simp only [Functor.comp_map, hφ, Functor.map_zero, zero_comp] at e1
    have e2 : (pullback.snd k (f i))^*ᵃ[l].map ((f i)^*ᵃ[l].map φ) = 0 := by
      rw [← cancel_epi ((adicUpperStarCompIso l
        (pullback.condition (f := k) (g := f i))).hom.app N), comp_zero]
      exact e1.symm
    simp only [ψ, Functor.map_comp, e2, zero_comp]
  apply Mod.hom_ext
  refine eq_zero_of_upperStar_map_eq_zero_of_specializes (pullback.snd k (f i)) ?_ ψ.hom
    (congrArg Mod.Hom.hom hψ)
  intro v
  obtain ⟨w, hw⟩ := hk ((f i).base v)
  obtain ⟨v', hv', hv'w⟩ := Flat.generalizingMap (f i) hw
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := k) (g := f i) w v'
    hv'w.symm
  exact ⟨p, hp2 ▸ hv'⟩

end AlgebraicGeometry.ProEtale
