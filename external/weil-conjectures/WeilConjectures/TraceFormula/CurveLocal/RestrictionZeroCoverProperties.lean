/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.TraceFormula.CurveLocal.CoverComplexE
public import WeilConjectures.TraceFormula.CurveLocal.CoverCurves
public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedDiagonal
public import WeilConjectures.TraceFormula.CurveLocal.CoverTangentCones
public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverConstruction

/-!

# Properties of the surface `T'` of a cover datum

The properties (ii), (iii) of blueprint `lemma-tangent-cones-on-cover` for the surface `T'` of a
cover datum, in the form used by `lemma-vanishing-restrictions-after-blowing-up--1`, together with
the pulled back identification of `lemma-vanishing-local-term-zero-stalk--1` (i):

* the curves `D'`, `H'`, `B'` pass through the closed point, `H'` is regular and `D'`, `B'` are
  reduced curves;
* the tangent cones of `D'` and `B'`, and of `D'` and `H'`, meet only at the origin: in the
  regular parameters `ξ`, `η` of the two factors, `G' ∪ V'`, `B'` and `H'` contain functions with
  initial forms `ξ^{2e}`, `αξ^e − βη^e` and `η`;
* the punctured diagonal `B' ∖ y'` is finite étale of degree `e²` over `B ∖ y`;
* the pullback of `P` to `T' ∖ D'` is the extension by zero of a complex `E'` on
  `T' ∖ (D' ∪ H')` with finite `ℓ`-group monodromy.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {M : CurveLocalModel k} {ℓ : ℕ}
  {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

/-- The curves `D'`, `H'`, `B'` pass through the closed point of `T'`
(blueprint `lemma-tangent-cones-on-cover`). -/
theorem nonempty_curves : Nonempty D.D' ∧ Nonempty D.H' ∧ Nonempty D.B' :=
  D.nonempty_curves'

/-- The curve `H'` is regular: its ring is a discrete valuation ring (blueprint
`lemma-tangent-cones-on-cover` (ii): `H'` is the axis `η = 0` of `T'`). -/
theorem isDiscreteValuationRing_H' :
    ∃ _ : IsDomain Γ(D.H', ⊤), IsDiscreteValuationRing Γ(D.H', ⊤) :=
  D.isDiscreteValuationRing_H''

/-- The curves `D'` and `B'` have dimension one (blueprint `lemma-tangent-cones-on-cover`). -/
theorem ringKrullDim_D'_B' : ringKrullDim Γ(D.D', ⊤) = 1 ∧ ringKrullDim Γ(D.B', ⊤) = 1 :=
  D.ringKrullDim_D'_B''

/-- **Tangent cones** (blueprint `lemma-tangent-cones-on-cover` (iii)): the tangent cone of
`G' ∪ V'` meets neither that of `B'` nor that of `H'` outside the origin. -/
theorem tangentConesMeetAtOrigin :
    IsLocalRing.TangentConesMeetAtOrigin (strictHenselization D.s') (specIdeal D.dD')
        (specIdeal D.dB') ∧
      IsLocalRing.TangentConesMeetAtOrigin (strictHenselization D.s') (specIdeal D.dD')
        (specIdeal D.dH') :=
  D.tangentConesMeetAtOrigin_specIdeal

/-- **The punctured diagonal** (blueprint `lemma-tangent-cones-on-cover` (ii)): `B' ∖ y'` is
finite étale of degree `e²` over `B ∖ y`, compatibly with the inclusions into `T' ∖ D'` and
`T ∖ (G ∪ V)`. -/
theorem exists_puncturedDiagonal_finite_etale :
    ∃ (πU : (D.dB' ⁻¹ᵁ D.dD'.openComplement).toScheme ⟶ M.yB.openComplement.toScheme)
      (_ : IsFinite πU) (_ : Etale πU),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ M.yB.openComplement.toScheme),
        Nat.card (πU.GeometricFiber s) = D.e ^ 2) ∧
      πU ≫ M.ψ ≫ M.O.ι =
        D.dB'.resLE D.dD'.openComplement (D.dB' ⁻¹ᵁ D.dD'.openComplement) le_rfl ≫
          D.dD'.openComplement.ι ≫ D.π :=
  D.exists_puncturedDiagonal_finite_etale'

/-- **The complex `E'`** (blueprint `lemma-tangent-cones-on-cover` (i) and
`lemma-vanishing-local-term-zero-stalk--1` (i)): for `L ≅ PL`, `K ≅ PK` with `K_ȳ = 0` and
`P = (L ⊠ K)|_T`, the pullback of `P` to `T' ∖ D'` is the extension by zero of a bounded complex
`E'` on `T' ∖ (D' ∪ H')` whose cohomology sheaves are trivialized by a finite étale Galois cover
with group a finite `ℓ`-group, with finite values. -/
theorem exists_E' [Finite Λ]
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (hPL : ∃ a b, IsBoundedFlatComplex Λ a b PL) (hPK : ∃ a b, IsBoundedFlatComplex Λ a b PK)
    (eL : L ≅ DerivedCategory.Q.obj PL) (eK : K ≅ DerivedCategory.Q.obj PK)
    (P : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    ∃ (E' : DerivedCategory (Sheaf
        (D.dD'.openComplement ⊓ D.dH'.openComplement).toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))
      (_ : (∃ a b : ℤ, E'.IsGE a ∧ E'.IsLE b) ∧ ∀ n : ℤ,
        ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
          (c : Scheme.GaloisCover G (D.dD'.openComplement ⊓ D.dH'.openComplement).toScheme)
          (N : ModuleCat.{u + 1} Λ) (_ : Finite N),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
              ((DerivedCategory.homologyFunctor _ n).obj E') ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)),
      Nonempty ((D.dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
          ((D.π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) ≅
        ((strictLocalization D.s').homOfLE (inf_le_left :
          D.dD'.openComplement ⊓ D.dH'.openComplement ≤ D.dD'.openComplement))_!open[
            ModuleCat.{u + 1} Λ]
          |>.mapDerivedCategory.obj E') :=
  D.exists_complexE L K P hKy hPL hPK eL eK eP

end AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum
