/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Coefficient dévissage for the exchange morphism

For a cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

the degree-`q` exchange maps `p⁻¹ Rᵠg_* F ⟶ Rᵠh_* e⁻¹ F`
(`AlgebraicGeometry.Etale.baseChangeHomologyMap`) form a morphism between the long exact
sequences attached to a short exact sequence of coefficient sheaves. By the five lemma, the
class of sheaves at which they are isomorphisms in every degree is stable under extensions.
Consequently, if they are isomorphisms at every sheaf killed by a prime, then also at every
sheaf killed by a positive integer (by induction on the number of prime factors), and, for
`g` quasi-compact and quasi-separated, at every torsion sheaf (as a filtered colimit of such
sheaves).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact`: the five-lemma
  transfer.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero`: the prime-factor
  induction.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`: the prime-torsion
  dévissage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
  {e : Y ⟶ T} {h : Y ⟶ X}

instance (p : X ⟶ S) (g : T ⟶ S) (q : ℤ) : (Etale.baseChangeSourceFunctor Λ p g q).Additive := by
  dsimp only [Etale.baseChangeSourceFunctor]
  infer_instance

instance (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ) : (Etale.baseChangeTargetFunctor Λ e h q).Additive := by
  dsimp only [Etale.baseChangeTargetFunctor]
  infer_instance

/-- The source `F ↦ p⁻¹ Rᵠg_* F` of the exchange map is exact in the middle on short exact
sequences: it is the composite of the triangulated functors `F ↦ F[0]` (on short exact
sequences), `Rg_*`, `p^*` with the homological functor `Hᵠ`. -/
theorem Etale.exact_baseChangeSourceFunctor_map_of_shortExact (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact) :
    (E.map (Etale.baseChangeSourceFunctor Λ p g q)).Exact :=
  hE.map_exact_of_isHomological ((((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⋙
      ((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus) ⋙
    DerivedCategory.Plus.homologyFunctor _ q) _ rfl

/-- The target `F ↦ Rᵠh_* e⁻¹ F` of the exchange map is exact in the middle on short exact
sequences: it is the composite of the triangulated functors `F ↦ F[0]` (on short exact
sequences), `e^*`, `Rh_*` with the homological functor `Hᵠ`. -/
theorem Etale.exact_baseChangeTargetFunctor_map_of_shortExact (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact) :
    (E.map (Etale.baseChangeTargetFunctor Λ e h q)).Exact :=
  hE.map_exact_of_isHomological ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
      ((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus) ⋙
    DerivedCategory.Plus.homologyFunctor _ q) _ rfl

/-- **Five-lemma transfer for the exchange morphism**: for a short exact sequence
`0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` of sheaves of `Λ`-modules, if the exchange maps are isomorphisms at `F₁`
and at `F₂` in every degree, then they are isomorphisms at `F` in every degree. The exchange
maps form a morphism between the two long exact sequences
(`AlgebraicGeometry.Etale.exists_connecting_baseChangeHomologyMap`), and in each degree the
five lemma applies to the five adjacent terms.
(blueprint: `theorem-proper-base-change-classical-pro`) -/
theorem Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact (sq : IsPullback e h g p)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact)
    (h₁ : ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E.X₁))
    (h₃ : ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E.X₃)) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q E.X₂) := by
  obtain ⟨δS, δT, wS₁, wS₂, wT₁, wT₂, -, hS₂, -, hT₂, hδ⟩ :=
    Etale.exists_connecting_baseChangeHomologyMap Λ sq hE (q - 1) q (sub_add_cancel q 1)
  obtain ⟨δS', δT', wS₁', wS₂', wT₁', wT₂', hS₁', -, -, -, hδ'⟩ :=
    Etale.exists_connecting_baseChangeHomologyMap Λ sq hE q (q + 1) rfl
  have hS := Etale.exact_baseChangeSourceFunctor_map_of_shortExact Λ p g q hE
  have hT := Etale.exact_baseChangeTargetFunctor_map_of_shortExact Λ e h q hE
  have hf := Etale.baseChangeHomologyMap_naturality Λ sq q E.f
  have hg := Etale.baseChangeHomologyMap_naturality Λ sq q E.g
  have : Mono (Etale.baseChangeHomologyMap Λ sq q E.X₂) :=
    Abelian.mono_of_epi_of_mono_of_mono'
      (ComposableArrows.homMk₃ (f := ComposableArrows.mk₃ δS
        ((Etale.baseChangeSourceFunctor Λ p g q).map E.f)
        ((Etale.baseChangeSourceFunctor Λ p g q).map E.g))
        (g := ComposableArrows.mk₃ δT
        ((Etale.baseChangeTargetFunctor Λ e h q).map E.f)
        ((Etale.baseChangeTargetFunctor Λ e h q).map E.g))
        (Etale.baseChangeHomologyMap Λ sq (q - 1) E.X₃)
        (Etale.baseChangeHomologyMap Λ sq q E.X₁)
        (Etale.baseChangeHomologyMap Λ sq q E.X₂)
        (Etale.baseChangeHomologyMap Λ sq q E.X₃) hδ hf.symm hg.symm)
      wS₂ hS.exact_toComposableArrows hT₂.exact_toComposableArrows
      (h₃ (q - 1)).epi_of_iso (h₁ q).mono_of_iso (h₃ q).mono_of_iso
  have : Epi (Etale.baseChangeHomologyMap Λ sq q E.X₂) :=
    Abelian.epi_of_epi_of_epi_of_mono'
      (ComposableArrows.homMk₃ (f := ComposableArrows.mk₃
        ((Etale.baseChangeSourceFunctor Λ p g q).map E.f)
        ((Etale.baseChangeSourceFunctor Λ p g q).map E.g) δS')
        (g := ComposableArrows.mk₃
        ((Etale.baseChangeTargetFunctor Λ e h q).map E.f)
        ((Etale.baseChangeTargetFunctor Λ e h q).map E.g) δT')
        (Etale.baseChangeHomologyMap Λ sq q E.X₁)
        (Etale.baseChangeHomologyMap Λ sq q E.X₂)
        (Etale.baseChangeHomologyMap Λ sq q E.X₃)
        (Etale.baseChangeHomologyMap Λ sq (q + 1) E.X₁) hf.symm hg.symm hδ')
      hS₁'.exact_toComposableArrows hT.exact_toComposableArrows wT₁'
      (h₁ q).epi_of_iso (h₃ q).epi_of_iso (h₁ (q + 1)).mono_of_iso
  exact isIso_of_mono_of_epi _

/-- **Prime-factor induction for the exchange morphism**: if the exchange maps are
isomorphisms in every degree at every sheaf killed by a prime, then they are isomorphisms in
every degree at every sheaf killed by a positive integer `n`. Induct on the number of prime
factors of `n` using `0 ⟶ F[ℓ] ⟶ F ⟶ ℓF ⟶ 0` for a prime `ℓ ∣ n`
(`CategoryTheory.ObjectProperty.prop_of_nsmul_id_eq_zero`) and the five-lemma transfer
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact`.
(blueprint: `theorem-proper-base-change-classical-pro`) -/
theorem Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero (sq : IsPullback e h g p)
    (hprime : ∀ r : ℕ, r.Prime → ∀ E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      r • 𝟙 E = 0 → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E))
    {n : ℕ} (hn : 0 < n) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : n • 𝟙 F = 0) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  ObjectProperty.prop_of_nsmul_id_eq_zero
    (fun F ↦ ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F))
    (fun _ hE h₁ h₃ ↦ Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact Λ sq hE h₁ h₃)
    hprime n hn F hF q

/-- **Prime-torsion dévissage for the exchange morphism**: let `g` be quasi-compact and
quasi-separated. If the exchange maps are isomorphisms in every degree at every sheaf killed by
a prime, then they are isomorphisms at every torsion sheaf `F`. By the prime-factor induction
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero` they are
isomorphisms at the sheaves `F[n]` killed by a positive integer; `F` is their filtered colimit
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf.exists_isColimit`), and the source and the target of
the exchange map commute with filtered colimits
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`).
(blueprint: `theorem-proper-base-change-classical-pro`) -/
theorem Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g]
    (hprime : ∀ r : ℕ, r.Prime → ∀ E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      r • 𝟙 E = 0 → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F] (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq ‹_›
  obtain ⟨J, _, _, D, c, hc, rfl, hD⟩ := Scheme.IsTorsionModuleSheaf.exists_isColimit Λ F
  have : EssentiallySmall.{u + 1} J := essentiallySmallSelf.{u + 1} J
  have := Etale.preservesColimitsOfShape_higherDirectImage Λ g q J
  have := Etale.preservesColimitsOfShape_higherDirectImage Λ h q J
  have : PreservesColimitsOfSize.{0, 0} ((p)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} ((e)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape J (Etale.baseChangeSourceFunctor Λ p g q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeSourceFunctorIso Λ p g q).symm
  have : PreservesColimitsOfShape J (Etale.baseChangeTargetFunctor Λ e h q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeTargetFunctorIso Λ e h q).symm
  have : IsIso (Functor.whiskerLeft D (Etale.baseChangeHomologyNatTrans Λ sq q)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    obtain ⟨n, hn, hnj⟩ := hD j
    exact Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero Λ sq hprime hn _ hnj q
  exact isIso_app_coconePt_of_preservesColimit D _ c hc

end AlgebraicGeometry
