/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ExtensionTowerLocallyConstant
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowStratification

/-!
# The uniform stratification of the higher direct images of a tower of extensions

Let `Λ` be a noetherian ring and `I` an ideal with all `Λ ⧸ Iⁿ` finite, of exponent invertible on
`T`, and `F : ℕ → Sh(T_ét, Λ)` a tower of extensions `0 ⟶ F 0 ⟶ F (n + 1) ⟶ F n ⟶ 0` with `F n`
killed by `Iⁿ⁺¹` and `F 0` the restriction of scalars of a constructible sheaf of
`Λ ⧸ I`-modules (for instance the reductions of an `𝒪_E`-lattice in a lisse `ℓ`-adic sheaf).
For `g : T ⟶ Y` quasi-compact between schemes locally of finite type over a field, `Y`
quasi-compact, there is a stratification of `Y` over whose strata all the `Hᵏ(Rg_* F n)` are
`IsSetFLC` (`AlgebraicGeometry.Etale.exists_stratification_isSetFLC_upperStar_of_tower`).

This generalises the uniform stratification of the constant tower `Λ ⧸ Iⁿ`
(`AlgebraicGeometry.Etale.exists_stratification_isSetFLC_upperStar_higherDirectImageQuotPowTower`)
and rests on the finiteness theorem for torsion coefficients
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`)
applied to `F 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) {T Y S : Scheme.{u}} (g : T ⟶ Y)
  (j : S ⟶ Y)

/-- The restriction to `j` of `Hᵏ(Rg_* M)`, for a sheaf `M` of `Λ ⧸ I`-modules with scalars
restricted to `Λ`, is the restriction of scalars of the restriction to `j` of `Hᵏ(Rg_* M)`
computed over `Λ ⧸ I`. -/
noncomputable def upperStarHomologyRightDerivedRestrictScalarsIso
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I))) (k : ℤ) :
    (upperStarHomologyRightDerived g j k).obj
        ((Sheaf.restrictScalars T.smallEtaleTopology (Ideal.Quotient.mk I)).obj M) ≅
      (Sheaf.restrictScalars S.smallEtaleTopology (Ideal.Quotient.mk I)).obj
        ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj ((_root_.DerivedCategory.homologyFunctor _ k).obj
          ((R((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) :=
  (j)^*[ModuleCat.{u + 1} Λ].mapIso
      ((_root_.DerivedCategory.homologyFunctor _ k).mapIso
          (restrictScalarsRightDerivedLowerStarSingleIso (Ideal.Quotient.mk I) g M).symm ≪≫
        (((Sheaf.restrictScalars Y.smallEtaleTopology
          (Ideal.Quotient.mk I)).mapDerivedCategoryHomologyFunctorIso k).app _).symm) ≪≫
    (upperStarRestrictScalarsIso (Ideal.Quotient.mk I) j).app _

variable {𝕜 : Type u} [Field 𝕜]

/-- **The uniform stratification of a tower of extensions.** Let `Λ` be noetherian, all
`Λ ⧸ Iⁿ` finite with `Λ ⧸ I` of exponent invertible on `T`, `g : T ⟶ Y` quasi-compact between
schemes locally of finite type over a field with `Y` quasi-compact, and `F : ℕ → Sh(T_ét, Λ)` with
`F n` killed by `Iⁿ⁺¹`, short exact sequences `0 ⟶ F 0 ⟶ F (n + 1) ⟶ F n ⟶ 0` and `F 0` the
restriction of scalars of a constructible sheaf `F₀` of `Λ ⧸ I`-modules. Then there is a
stratification of `Y` over whose strata all the `Hᵏ(Rg_* F n)`, `n : ℕ`, `k : ℤ`, are
`IsSetFLC`: by the finiteness theorem for torsion coefficients `Rg_* F₀` is bounded with
constructible cohomology sheaves, which are finite locally constant on the strata of a single
stratification, and finite local constancy propagates along the tower
(`AlgebraicGeometry.Etale.isSetFLC_upperStar_homology_rightDerived_of_tower`). -/
theorem exists_stratification_isSetFLC_upperStar_of_tower [IsNoetherianRing Λ]
    [∀ n, Finite (Λ ⧸ I ^ n)] [Finite (Λ ⧸ I)] [HasInvertibleExponent (Λ ⧸ I) T]
    [QuasiCompact g] (aT : T ⟶ Spec (.of 𝕜)) (aY : Y ⟶ Spec (.of 𝕜)) [LocallyOfFiniteType aT]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT)
    (F : ℕ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ n, ∀ r ∈ I ^ (n + 1), r • 𝟙 (F n) = 0)
    (SC : ℕ → ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hSC : ∀ n, (SC n).ShortExact) (e₁ : ∀ n, (SC n).X₁ ≅ F 0)
    (e₂ : ∀ n, (SC n).X₂ ≅ F (n + 1)) (e₃ : ∀ n, (SC n).X₃ ≅ F n)
    (F₀ : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I))) [IsConstructibleSheaf F₀]
    (e₀ : (Sheaf.restrictScalars T.smallEtaleTopology (Ideal.Quotient.mk I)).obj F₀ ≅ F 0) :
    ∃ R : Stratification Y, ∀ l (n : ℕ) (k : ℤ),
      IsSetFLC ((upperStarHomologyRightDerived g (R.immersion l) k).obj (F n)) := by
  obtain ⟨R, hR⟩ := exists_stratification_isFiniteLocallyConstantSheaf_upperStar_homology _
    (boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (Λ ⧸ I) g aT aY hg _
      (DerivedCategory.boundedConstructible_singleFunctor_obj F₀ 0))
  refine ⟨R, fun l n k ↦ isSetFLC_upperStar_homology_rightDerived_of_tower g (R.immersion l)
    F hF SC hSC e₁ e₂ e₃ (fun k ↦ ?_) n k⟩
  have := hR k l
  exact IsFiniteLocallyConstantSheaf.of_iso
    ((upperStarHomologyRightDerived g (R.immersion l) k).mapIso e₀.symm ≪≫
      upperStarHomologyRightDerivedRestrictScalarsIso I g (R.immersion l) F₀ k).symm

end AlgebraicGeometry.Etale
