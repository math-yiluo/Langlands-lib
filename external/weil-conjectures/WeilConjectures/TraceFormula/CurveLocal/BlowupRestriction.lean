/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.RingTheory.TangentCone
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction
public import WeilConjectures.TraceFormula.CurveLocal.BlowupRestrictionPrincipal
public import WeilConjectures.RingTheory.RegularLocalLocalization
public import WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization

/-!

# The blow-up restriction vanishing

This file states the geometric vanishing used by the curve route of the trace formula
(blueprint `lemma-vanishing-restrictions-after-blowing-up--1`, proved in its own subsection by
blowing up the closed point, see `remark-outline-local-computation`):

Let `T` be the strict localization of a smooth surface over an algebraically closed field `k` at a
closed point `t`, `H` a regular curve through `t` and `D`, `B` reduced closed curves through `t`
whose tangent cones satisfy `C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`. Let
`i : T ∖ (D ∪ H) ⟶ T ∖ D` and let `E` be a bounded complex on `T ∖ (D ∪ H)` with finite locally
constant cohomology and finite `ℓ`-group monodromy. Then the restriction
`RΓ(T ∖ D, i_! E) ⟶ RΓ(B ∖ t, (i_! E)|_{B ∖ t})` is zero in `D(Λ)`.

The tangent cone condition is expressed in the local ring `R` of `T` through the ideals of the two
curves (`IsLocalRing.TangentConesMeetAtOrigin`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ideal of global sections of a closed subscheme `d : D ⟶ Spec R` of an affine scheme. -/
noncomputable def specIdeal {R : CommRingCat.{u}} {D : Scheme.{u}} (d : D ⟶ Spec R) : Ideal R :=
  RingHom.ker ((Scheme.ΓSpecIso R).inv ≫ d.appTop).hom

/-- **Blow-up restriction vanishing** (blueprint `lemma-vanishing-restrictions-after-blowing-up--1`;
SGA 5, III B, §§2–4). Let `T = Spec R` be the strict localization of a smooth surface `S` over the
algebraically closed field `k` at a `k`-point `s`, `ℓ` a prime invertible in `k` and `Λ` a finite
commutative `ℓ`-primary ring. Let `H` be a regular curve through the closed point `t` (its ring is a
discrete valuation ring) and `D`, `B` reduced closed curves through `t` whose tangent cones satisfy
`C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`. Let `i : T ∖ (D ∪ H) ⟶ T ∖ D` and let `E` be a
bounded complex on `T ∖ (D ∪ H)` whose cohomology sheaves are trivialized by a finite étale Galois
cover with group a finite `ℓ`-group, with finite constant values (finite locally constant
cohomology with finite `ℓ`-group monodromy). Then the restriction
`RΓ(T ∖ D, i_! E) ⟶ RΓ(B ∖ t, (i_! E)|_{B ∖ t})` is zero in `D(Λ)`; here `B ∖ t = B ∩ (T ∖ D)`,
since the tangent cone condition forces `B ∩ D = {t}`.

This is the statement of the blueprint node of the subsection
`lemma-vanishing-restrictions-after-blowing-up--1`, whose own task proves it. -/
theorem sectionsRestriction_app_eq_zero_of_tangentConesMeetAtOrigin
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 aS]
    (s : Spec (.of k) ⟶ S) (hs : s ≫ aS = 𝟙 _) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    {D H B : Scheme.{u}} (dD : D ⟶ strictLocalization s) (dH : H ⟶ strictLocalization s)
    (dB : B ⟶ strictLocalization s) [IsClosedImmersion dD] [IsClosedImmersion dH]
    [IsClosedImmersion dB] [Nonempty D] [Nonempty H] [Nonempty B]
    (hH : ∃ _ : IsDomain Γ(H, ⊤), IsDiscreteValuationRing Γ(H, ⊤))
    (hD : IsReduced D ∧ ringKrullDim Γ(D, ⊤) = 1)
    (hB : IsReduced B ∧ ringKrullDim Γ(B, ⊤) = 1)
    (hDB : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s) (specIdeal dD)
      (specIdeal dB))
    (hDH : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s) (specIdeal dD)
      (specIdeal dH))
    (E : DerivedCategory (Sheaf (dD.openComplement ⊓ dH.openComplement).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hE : (∃ a b : ℤ, E.IsGE a ∧ E.IsLE b) ∧ ∀ n : ℤ,
      ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
        (c : Scheme.GaloisCover G (dD.openComplement ⊓ dH.openComplement).toScheme)
        (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
        Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
            ((DerivedCategory.homologyFunctor _ n).obj E) ≅
          (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    (sectionsRestriction (ModuleCat.{u + 1} Λ)
      (dB.resLE dD.openComplement (dB ⁻¹ᵁ dD.openComplement) le_rfl)
      (V := Scheme.Etale.mk (𝟙 _)) (W := Scheme.Etale.mk (𝟙 _))
      (dB.resLE dD.openComplement (dB ⁻¹ᵁ dD.openComplement) le_rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)).app
        (((strictLocalization s).homOfLE (inf_le_left :
          dD.openComplement ⊓ dH.openComplement ≤ dD.openComplement))_!open[ModuleCat.{u + 1} Λ]
          |>.mapDerivedCategory.obj E) = 0 := by
  have : SmoothOfRelativeDimension 2 (Over.mk aS).hom := ‹_›
  have hreg := isRegularLocalRing_strictHenselization_of_smooth (Over.mk aS) s hs
  have hdim := ringKrullDim_strictHenselization_of_smooth (Over.mk aS) s hs
  have : IsRegularRing (strictHenselization s) :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal (strictHenselization s))).2
  have := IsRegularLocalRing.uniqueFactorizationMonoid (strictHenselization s)
  -- the curves `D` and `B` are principal
  obtain ⟨hDred, hDdim⟩ := hD
  have hDsurj := dD.surjective_ΓSpecIso_inv_comp_appTop
  have hDdim' : ringKrullDim (strictHenselization s ⧸ specIdeal dD) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hDsurj)).trans hDdim
  obtain ⟨f, hfI⟩ : ∃ f, specIdeal dD = Ideal.span {f} :=
    Ideal.exists_eq_span_singleton_of_isRadical_of_ringKrullDim_quotient_eq_one
      hdim ((RingHom.ker_isRadical_iff_reduced_of_surjective hDsurj).2 inferInstance) hDdim'
  obtain ⟨hfm, hf0⟩ :=
    Ideal.mem_maximalIdeal_and_ne_zero_of_ringKrullDim_quotient_eq_one hdim (hfI ▸ hDdim')
  obtain ⟨hBred, hBdim⟩ := hB
  have hBsurj := dB.surjective_ΓSpecIso_inv_comp_appTop
  have hBdim' : ringKrullDim (strictHenselization s ⧸ specIdeal dB) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hBsurj)).trans hBdim
  obtain ⟨g, hgI⟩ : ∃ g, specIdeal dB = Ideal.span {g} :=
    Ideal.exists_eq_span_singleton_of_isRadical_of_ringKrullDim_quotient_eq_one
      hdim ((RingHom.ker_isRadical_iff_reduced_of_surjective hBsurj).2 inferInstance) hBdim'
  obtain ⟨hgm, hg0⟩ :=
    Ideal.mem_maximalIdeal_and_ne_zero_of_ringKrullDim_quotient_eq_one hdim (hgI ▸ hBdim')
  -- the regular curve `H` is principal, given by an equation of order one
  obtain ⟨_, _⟩ := hH
  have hHsurj := dH.surjective_ΓSpecIso_inv_comp_appTop
  have hHdim' : ringKrullDim (strictHenselization s ⧸ specIdeal dH) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hHsurj)).trans
      (IsDiscreteValuationRing.ringKrullDim_eq_one Γ(H, ⊤))
  obtain ⟨h, hhI⟩ : ∃ h, specIdeal dH = Ideal.span {h} :=
    Ideal.exists_eq_span_singleton_of_isRadical_of_ringKrullDim_quotient_eq_one
      hdim (RingHom.ker_isPrime _).isRadical hHdim'
  have h2 : 2 ≤ (IsLocalRing.maximalIdeal (strictHenselization s)).spanFinrank := by
    have h := hreg.spanFinrank_maximalIdeal.trans hdim
    exact_mod_cast h.ge
  have hh := IsLocalRing.hasOrder_one_of_ker_eq_span_singleton h2
    (IsPrincipalIdealRing.principal _) _ hHsurj hhI
  rw [hfI, hgI] at hDB
  rw [hfI, hhI] at hDH
  -- the complements of `D` and `D ∪ H` are the basic opens of `f` and `fh`
  have hU := dD.openComplement_eq_basicOpen hfI
  have hV : dD.openComplement ⊓ dH.openComplement =
      Scheme.specBasicOpen (R := .of _) (f * h) := by
    rw [hU, dH.openComplement_eq_basicOpen hhI]
    exact (PrimeSpectrum.basicOpen_mul f h).symm
  -- `B - t` maps to the punctured spectrum of `R / (g)`
  have : Fact (g ∈ IsLocalRing.maximalIdeal (strictHenselization s)) := ⟨hgm⟩
  have hle : dB ⁻¹ᵁ dD.openComplement ≤
      dB.toSpecQuotient hgI.ge ⁻¹ᵁ puncturedSpec (strictHenselization s ⧸ Ideal.span {g}) := by
    intro x hx hx'
    have hc := dB.apply_eq_closedPoint_of_toSpecQuotient hgI.ge hx'
    have hx : dB x ∈ dD.openComplement := hx
    rw [hU, hc] at hx
    exact hx hfm
  refine sectionsRestriction_app_eq_zero_of_globalSectionsRestriction_eq_zero _ _ _ _ ?_
  refine globalSectionsRestriction_eq_zero_of_eq_basicOpen (Over.mk aS) s hℓ hΛ hs hf0 hg0 hh
    hDB hDH hU hV _ _ ((dB.toSpecQuotient hgI.ge).resLE _ _ hle) ?_ E hE
  rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.toSpecQuotient_comp, Scheme.Hom.resLE_comp_ι]

end AlgebraicGeometry.Etale
