/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleModel
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.TraceFormula.CurveLocal.BlowupRestriction
public import WeilConjectures.TraceFormula.CurveLocal.CoverDatumExistence
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverProperties

/-!

# Prime-to-`ℓ` covers separating the graph and the diagonal

This file states the covering step of the proof of blueprint `lemma-vanishing-local-term-zero-stalk`
(`lemma-tangent-cones-on-cover`, together with the identification of
`lemma-vanishing-local-term-zero-stalk--1` (i) pulled back to the cover).

In the strictly local model `T` of a `CurveLocalModel` (with the graph `G`, the diagonal `B`, the
vertical axis `V` and the horizontal axis `H = X × {y}`), let `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`. There are finite covers `X' ⟶ X`, `Y' ⟶ Y` of the two strictly
local traits by strictly local regular traits, of the same degree `d` prime to `ℓ` and generically
étale, such that, with `T'` the localization of `X' × Y'` at its closed point and `G', V', H', B'`
the reduced inverse images:

1. **(i)** the pullbacks `N', Q'` of `N = L|_{X ∖ y}` and `Q = K|_{Y ∖ y}` admit bounded finite
   projective lisse models whose termwise monodromy factors through finite `ℓ`-groups;
2. **(ii)** `T'` is a strictly local smooth surface, finite flat of rank `d²` over `T` and étale
   away from `H ∪ V`; in particular `B' ∖ y' ⟶ B ∖ y` is finite étale of degree `d²`;
3. **(iii)** the support of the tangent cone of `G' ∪ V'` meets neither that of `B'` nor that of
   `H'` outside the origin.

Since `K_ȳ = 0`, `K = j_{Y!} Q`, and `P` restricted to `T ∖ (G ∪ V)` is the extension by zero of
`(N ⊠ Q)|_{T ∖ (G ∪ V ∪ H)}` (`lemma-vanishing-local-term-zero-stalk--1` (i)); its pullback to
`T' ∖ (G' ∪ V')` is the extension by zero of `E' = (N' ⊠ Q')|_{T' ∖ (G' ∪ V' ∪ H')}`, whose
cohomology sheaves have finite `ℓ`-group monodromy by (i). The statement
`AlgebraicGeometry.Etale.CurveLocalModel.exists_restrictionZeroCover` records exactly the data
used in the proof of `lemma-vanishing-local-term-zero-stalk`: the strictly local smooth surface `T'`
with the curves `D' = G' ∪ V'`, `H'`, `B'` satisfying the hypotheses of
`lemma-vanishing-restrictions-after-blowing-up--1`, the finite étale map `B' ∖ y' ⟶ B ∖ y` of degree
prime to `ℓ` compatible with the punctured diagonals, and the identification of the pullback of `P`
to `T' ∖ D'` with `i'_! E'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

omit [IsAlgClosed k] in
/-- **Flat constructible models** (blueprint `lemma-flat-models-generators`, used in
`lemma-tangent-cones-on-cover` (i)): an object of `D^b_{ctf}(X, Λ)` is represented by a bounded
complex of flat constructible sheaves. -/
theorem exists_flatConstructibleModel {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ M.X K) :
    ∃ P : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
      (∃ a b, IsBoundedFlatComplex Λ a b P) ∧ (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  have := SmoothOfRelativeDimension.smooth 1 M.f
  have : CompactSpace M.X := QuasiCompact.compactSpace_of_compactSpace M.f
  exact DerivedCategory.exists_flatConstructibleModel_of_locallyOfFiniteType M.f K hK

/-- **Existence of the cover datum** (blueprint `lemma-tangent-cones-on-cover` (i), first
half): for bounded complexes `PL`, `PK` of flat constructible sheaves on `X` there is a cover
datum: the terms are lisse on a punctured neighbourhood of `y`, a finite étale Galois cover
trivializes them, its `ℓ`-Sylow quotient has degree prime to `ℓ`, and in its normalization `C` one
of the points over `y` has ramification index prime to `ℓ`. -/
theorem exists_coverDatum (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hPL : ∃ a b, IsBoundedFlatComplex Λ a b PL) (hPK : ∃ a b, IsBoundedFlatComplex Λ a b PK)
    (hcL : ∀ q : ℤ, IsConstructibleSheaf (PL.X q)) (hcK : ∀ q : ℤ, IsConstructibleSheaf (PK.X q)) :
    Nonempty (M.CoverDatum ℓ PL PK) :=
  M.nonempty_coverDatum ℓ PL PK hPL hPK hcL hcK

/-- **The covers from a cover datum** (blueprint `lemma-tangent-cones-on-cover` (ii), (iii)
and the pulled back identification of `lemma-vanishing-local-term-zero-stalk--1` (i)): from a cover
datum `p : C ⟶ X`, `c`, `e`, take `T'` the strict localization of `C ×_k C` at `(c, c)`, the
reduced inverse images `D' = G' ∪ V'`, `H'`, `B'` of the curves, the finite étale map
`B' ∖ y' ⟶ B ∖ y` of degree `e²`, and `E'` the restriction of `N ⊠ Q` to `T' ∖ (D' ∪ H')`. -/
theorem exists_restrictionZeroCover_of_coverDatum (ℓ : ℕ) [Fact ℓ.Prime]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hPL : ∃ a b, IsBoundedFlatComplex Λ a b PL) (hPK : ∃ a b, IsBoundedFlatComplex Λ a b PK)
    (eL : L ≅ DerivedCategory.Q.obj PL) (eK : K ≅ DerivedCategory.Q.obj PK)
    (D : M.CoverDatum ℓ PL PK)
    (P : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))
    (ψ : M.yB.openComplement.toScheme ⟶ M.O.toScheme)
    (hψ : ψ ≫ M.O.ι = M.yB.openComplement.ι ≫ M.b) :
    ∃ (S' : Scheme.{u}) (aS' : S' ⟶ Spec (.of k)) (_ : SmoothOfRelativeDimension 2 aS')
      (s' : Spec (.of k) ⟶ S') (_ : s' ≫ aS' = 𝟙 _) (π : strictLocalization s' ⟶ M.T)
      (D' H' B' : Scheme.{u}) (dD' : D' ⟶ strictLocalization s')
      (dH' : H' ⟶ strictLocalization s') (dB' : B' ⟶ strictLocalization s')
      (_ : IsClosedImmersion dD') (_ : IsClosedImmersion dH') (_ : IsClosedImmersion dB')
      (_ : Nonempty D') (_ : Nonempty H') (_ : Nonempty B')
      (_ : ∃ _ : IsDomain Γ(H', ⊤), IsDiscreteValuationRing Γ(H', ⊤))
      (_ : IsReduced D' ∧ ringKrullDim Γ(D', ⊤) = 1)
      (_ : IsReduced B' ∧ ringKrullDim Γ(B', ⊤) = 1)
      (_ : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s') (specIdeal dD')
        (specIdeal dB'))
      (_ : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s') (specIdeal dD')
        (specIdeal dH'))
      (_ : dD'.openComplement ≤ π ⁻¹ᵁ M.O)
      (πU : (dB' ⁻¹ᵁ dD'.openComplement).toScheme ⟶ M.yB.openComplement.toScheme)
      (_ : IsFinite πU) (_ : Etale πU) (d : ℕ)
      (_ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ M.yB.openComplement.toScheme),
        Nat.card (πU.GeometricFiber s) = d)
      (_ : IsUnit (d : Λ))
      (_ : πU ≫ ψ ≫ M.O.ι =
        dB'.resLE dD'.openComplement (dB' ⁻¹ᵁ dD'.openComplement) le_rfl ≫
          dD'.openComplement.ι ≫ π)
      (E' : DerivedCategory (Sheaf
        (dD'.openComplement ⊓ dH'.openComplement).toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))
      (_ : (∃ a b : ℤ, E'.IsGE a ∧ E'.IsLE b) ∧ ∀ n : ℤ,
        ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
          (c : Scheme.GaloisCover G (dD'.openComplement ⊓ dH'.openComplement).toScheme)
          (N : ModuleCat.{u + 1} Λ) (_ : Finite N),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
              ((DerivedCategory.homologyFunctor _ n).obj E') ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)),
      Nonempty ((dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
          ((π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) ≅
        ((strictLocalization s').homOfLE (inf_le_left :
          dD'.openComplement ⊓ dH'.openComplement ≤ dD'.openComplement))_!open[ModuleCat.{u + 1} Λ]
          |>.mapDerivedCategory.obj E') := by
  have hψM : ψ = M.ψ := by
    rw [← cancel_mono M.O.ι, hψ, M.ψ_comp_ι]
  subst hψM
  have he : IsUnit ((D.e ^ 2 : ℕ) : Λ) := by
    obtain ⟨n, hn⟩ := hΛ
    have hcop : Nat.Coprime (D.e ^ 2) (ℓ ^ n) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
        (Fact.out : ℓ.Prime)).2 D.not_dvd_e)))
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (D.e ^ 2 : ℕ) + b * (ℓ ^ n : ℕ) = 1 := by
      have h := Nat.gcd_eq_gcd_ab (D.e ^ 2) (ℓ ^ n)
      rw [hcop.gcd_eq_one] at h
      exact ⟨Nat.gcdA (D.e ^ 2) (ℓ ^ n), Nat.gcdB (D.e ^ 2) (ℓ ^ n), by
        push_cast at h ⊢; linarith⟩
    refine IsUnit.of_mul_eq_one (a : Λ) ?_
    have := congrArg (Int.cast : ℤ → Λ) hab
    push_cast at this
    rw [hn, mul_zero, add_zero] at this
    rw [mul_comm]
    exact_mod_cast this
  obtain ⟨hnD, hnH, hnB⟩ := D.nonempty_curves
  obtain ⟨hdD, hdB⟩ := D.ringKrullDim_D'_B'
  obtain ⟨hDB, hDH⟩ := D.tangentConesMeetAtOrigin
  obtain ⟨πU, hfin, het, hdeg, hsq⟩ := D.exists_puncturedDiagonal_finite_etale
  obtain ⟨E', hE', hiso⟩ := D.exists_E' L K hKy hPL hPK eL eK P eP
  have : SmoothOfRelativeDimension 2 (pullback.fst D.fC D.fC ≫ D.fC) :=
    show SmoothOfRelativeDimension (1 + 1) _ from inferInstance
  exact ⟨D.S', pullback.fst D.fC D.fC ≫ D.fC, this, D.s',
    by rw [CoverDatum.s', pullback.lift_fst_assoc, D.c_comp_fC],
    D.π, D.D', D.H', D.B', D.dD', D.dH', D.dB', inferInstance, inferInstance, inferInstance, hnD,
    hnH, hnB, D.isDiscreteValuationRing_H', ⟨inferInstance, hdD⟩, ⟨inferInstance, hdB⟩, hDB, hDH,
    D.openComplement_dD'_le, πU, hfin, het, D.e ^ 2, hdeg, he, hsq, E', hE', hiso⟩

/-- **Prime-to-`ℓ` covers separating the graph and the diagonal** (blueprint
`lemma-tangent-cones-on-cover`, with the identification of
`lemma-vanishing-local-term-zero-stalk--1` (i) pulled back to the cover). Let `ℓ` be a prime
invertible in `k`, `Λ` a finite commutative `ℓ`-primary ring, `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0`, `P = (L ⊠ K)|_T` on the strictly local model `T`, and `ψ : B ∖ Y ⟶ T ∖ (G ∪ V)` the
inclusion of the punctured diagonal. Then there are: the strict localization `T'` of a smooth
surface `S'` at a `k`-point, a morphism `π : T' ⟶ T`, closed curves `D' = G' ∪ V'`, `H'`, `B'` of
`T'` satisfying the hypotheses of `lemma-vanishing-restrictions-after-blowing-up--1` (`H'` regular,
`D'`, `B'` reduced curves, `C_t D' ∩ C_t B' = {0}`, `C_t D' ∩ T_t H' = {0}`), with
`T' ∖ D' ⊆ π⁻¹(T ∖ (G ∪ V))`, a finite étale map `B' ∖ y' ⟶ B ∖ Y` all of whose geometric
fibres have `d` points (`d` prime to `ℓ`) compatible with `ψ`, and a bounded complex `E'` on
`T' ∖ (D' ∪ H')` with finite locally constant cohomology and finite `ℓ`-group monodromy whose
extension by zero to `T' ∖ D'` is the pullback of `P`. -/
theorem exists_restrictionZeroCover (ℓ : ℕ) [Fact ℓ.Prime]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.boundedConstructibleFiniteTor Λ M.X L)
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ M.X K)
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))
    (ψ : M.yB.openComplement.toScheme ⟶ M.O.toScheme)
    (hψ : ψ ≫ M.O.ι = M.yB.openComplement.ι ≫ M.b) :
    ∃ (S' : Scheme.{u}) (aS' : S' ⟶ Spec (.of k)) (_ : SmoothOfRelativeDimension 2 aS')
      (s' : Spec (.of k) ⟶ S') (_ : s' ≫ aS' = 𝟙 _) (π : strictLocalization s' ⟶ M.T)
      (D' H' B' : Scheme.{u}) (dD' : D' ⟶ strictLocalization s')
      (dH' : H' ⟶ strictLocalization s') (dB' : B' ⟶ strictLocalization s')
      (_ : IsClosedImmersion dD') (_ : IsClosedImmersion dH') (_ : IsClosedImmersion dB')
      (_ : Nonempty D') (_ : Nonempty H') (_ : Nonempty B')
      (_ : ∃ _ : IsDomain Γ(H', ⊤), IsDiscreteValuationRing Γ(H', ⊤))
      (_ : IsReduced D' ∧ ringKrullDim Γ(D', ⊤) = 1)
      (_ : IsReduced B' ∧ ringKrullDim Γ(B', ⊤) = 1)
      (_ : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s') (specIdeal dD')
        (specIdeal dB'))
      (_ : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s') (specIdeal dD')
        (specIdeal dH'))
      (_ : dD'.openComplement ≤ π ⁻¹ᵁ M.O)
      (πU : (dB' ⁻¹ᵁ dD'.openComplement).toScheme ⟶ M.yB.openComplement.toScheme)
      (_ : IsFinite πU) (_ : Etale πU) (d : ℕ)
      (_ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ M.yB.openComplement.toScheme),
        Nat.card (πU.GeometricFiber s) = d)
      (_ : IsUnit (d : Λ))
      (_ : πU ≫ ψ ≫ M.O.ι =
        dB'.resLE dD'.openComplement (dB' ⁻¹ᵁ dD'.openComplement) le_rfl ≫
          dD'.openComplement.ι ≫ π)
      (E' : DerivedCategory (Sheaf
        (dD'.openComplement ⊓ dH'.openComplement).toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))
      (_ : (∃ a b : ℤ, E'.IsGE a ∧ E'.IsLE b) ∧ ∀ n : ℤ,
        ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
          (c : Scheme.GaloisCover G (dD'.openComplement ⊓ dH'.openComplement).toScheme)
          (N : ModuleCat.{u + 1} Λ) (_ : Finite N),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
              ((DerivedCategory.homologyFunctor _ n).obj E') ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)),
      Nonempty ((dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
          ((π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) ≅
        ((strictLocalization s').homOfLE (inf_le_left :
          dD'.openComplement ⊓ dH'.openComplement ≤ dD'.openComplement))_!open[ModuleCat.{u + 1} Λ]
          |>.mapDerivedCategory.obj E') := by
  obtain ⟨PL, hPL, hcL, ⟨eL⟩⟩ := M.exists_flatConstructibleModel L hL
  obtain ⟨PK, hPK, hcK, ⟨eK⟩⟩ := M.exists_flatConstructibleModel K hK
  obtain ⟨D⟩ := M.exists_coverDatum ℓ PL PK hPL hPK hcL hcK
  exact M.exists_restrictionZeroCover_of_coverDatum ℓ hΛ L K hKy PL PK hPL hPK eL eK D P eP
    ψ hψ

end AlgebraicGeometry.Etale.CurveLocalModel
