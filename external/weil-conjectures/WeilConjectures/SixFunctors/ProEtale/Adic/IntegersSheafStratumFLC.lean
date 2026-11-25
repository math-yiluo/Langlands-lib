/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowStratification
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratumTopology

/-!
# The integral identification on the strata of the uniform stratification

Let `E` be a finite extension of `ℚ_ℓ`, `Λ = Shrink 𝒪_E`, `g : T ⟶ Y` quasi-compact and
quasi-separated, and `j : S ⟶ Y` a stratum over which all the higher direct images
`Rᵏg_* (Λ ⧸ ℓ)_T` are finite locally constant. Then:

- `AlgebraicGeometry.ProEtale.isSetFLC_upperStar_higherDirectImageQuotPowTower_integers`: all the
  levels of the restricted towers `n ↦ j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))`, `k : ℤ`, are `IsSetFLC`, which is
  also the hypothesis of `AlgebraicGeometry.ProEtale.towerLimit_isModuleTopology_integersStratum`;
- `AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum_of_flcProperty`: for
  `j = i ≫ o` with `i : S ⟶ U` a closed immersion into a scheme with noetherian underlying space
  and `o` an open immersion, the integral identification `Hᵏ(j^* Rg_* 𝒪_{E,T}) ≅ C(-, lim_n Gₙ)`
  on the universal covers of `S`
  (`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum`);
- `AlgebraicGeometry.ProEtale.exists_stratification_flcProperty_integers`: for `g` and `Y` of
  finite type over a field, `Y` quasi-compact and `ℓ` invertible on `T`, such strata, in the form
  `j = j.liftCoborder ≫ j.coborderRange.ι`, form a stratification of `Y`
  (`AlgebraicGeometry.Etale.exists_stratification_flcProperty_rightDerived_constantQuotSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl Pretriangulated TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y)

/-- `Rᵏg_* (Λ ⧸ ℓ)_T` restricted to `j`, as a sheaf of `Λ ⧸ ℓ`-modules, `Λ = Shrink 𝒪_E`. -/
noncomputable abbrev upperStarRightDerivedIntegersModL (k : ℕ) :
    Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E)) :=
  (Etale.upperStar (ModuleCat.{u + 1}
    (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E)) j).obj
      (((Etale.lowerStar (ModuleCat.{u + 1}
        (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E)) g).rightDerived k).obj
          (Etale.constantQuotSheaf (integersShrink.{u} l E) (integersShrinkIdeal.{u} l E) T))

/-- **The restricted towers of `𝒪_E ⧸ ℓⁿ`-direct images are `IsSetFLC`** on a stratum over which
the `Rᵏg_* (Λ ⧸ ℓ)_T` are finite locally constant, in all degrees `k : ℤ`. -/
theorem isSetFLC_upperStar_higherDirectImageQuotPowTower_integers
    (h : ∀ k : ℕ, Etale.flcProperty S (upperStarRightDerivedIntegersModL l E g j k))
    (n : ℕ) (k : ℤ) :
    IsSetFLC ((Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) j).obj
      ((Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k).obj (op n))) :=
  haveI : IsNoetherianRing (integersShrink.{u} l E) := isNoetherianRing_shrink_integers l E
  haveI : Finite (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E) :=
    finite_quotient_span_natCast_shrink l E
  haveI (n : ℕ) : Finite (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E ^ n) :=
    finite_quotient_span_natCast_pow_shrink l E n
  Etale.isSetFLC_upperStar_higherDirectImageQuotPowTower_obj_of_flcProperty_one
    (I := integersShrinkIdeal.{u} l E) g j
    (natCast_mem_nonZeroDivisors_shrink.{u} l E) rfl h n k
variable [QuasiCompact g] [QuasiSeparated g]

/-- **The integral identification on a stratum with finite locally constant torsion direct
images.** Let `j = i ≫ o` with `i : S ⟶ U` a closed immersion into a scheme with noetherian
underlying space and `o : U ⟶ Y` an open immersion, such that all the `Rᵏg_* (Λ ⧸ ℓ)_T`,
`Λ = Shrink 𝒪_E`, restrict to finite locally constant sheaves on `S`. Then on the universal cover
`Ỹ_y` of `S`, the pullback of `Hᵏ(j^* Rg_* 𝒪_{E,T})` is `C(-, lim_n Gₙ)`, `Gₙ` the (finite)
stalks of `j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))` at the base point. -/
theorem nonempty_iso_homologyUpperStar_integersStratum_of_flcProperty {U : Scheme.{u}}
    [NoetherianSpace U] (i : S ⟶ U) [IsClosedImmersion i] (o : U ⟶ Y) [IsOpenImmersion o]
    (h : ∀ k : ℕ, Etale.flcProperty S (upperStarRightDerivedIntegersModL l E g (i ≫ o) k))
    {Ω : Type u} [Field Ω] (Ũ : Scheme.UniversalCovers S Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ S) (k : ℤ) :
    let H' := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
      Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) (i ≫ o)
    let St := (pointSmallEtale (Ũ.pt y ≫ Ũ.proj y)).sheafFiber
      (A := ModuleCat.{u + 1} (integersShrink.{u} l E))
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) :=
      (isSetFLC_upperStar_higherDirectImageQuotPowTower_integers l E g (i ≫ o) h n
        k).finite_sheafFiber _
    Nonempty ((DerivedCategory.homologyFunctor _ k).obj
        ((ProEtale.upperStar AddCommGrpCat.{u + 1} (Ũ.proj y)).mapDerivedCategory.obj
          ((ProEtale.upperStar AddCommGrpCat.{u + 1} (i ≫ o)).mapDerivedCategory.obj
            (integersCone l E g).pt)) ≅
      ProEtale.continuousMapAddSheaf (Ũ.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom))) := by
  let V : U.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : IsCompl (Set.range i.base) (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have : NoetherianSpace V.toScheme := inferInstanceAs (NoetherianSpace (V : Set U))
  exact nonempty_iso_homologyUpperStar_integersStratum l E g i V.ι hij o Ũ y k
    (isSetFLC_upperStar_higherDirectImageQuotPowTower_integers l E g (i ≫ o) h · (k - 1))
    (isSetFLC_upperStar_higherDirectImageQuotPowTower_integers l E g (i ≫ o) h · k)

omit [QuasiSeparated g] in
/-- **The uniform stratification for `𝒪_E`.** For `g : T ⟶ Y` quasi-compact and
quasi-separated between schemes locally of finite type over a field, `Y` quasi-compact, and `ℓ`
invertible on `T`, there is a stratification of `Y` on whose strata all the `Rᵏg_* (Λ ⧸ ℓ)_T`,
`Λ = Shrink 𝒪_E`, are finite locally constant. It is stated for the factorisations
`j.liftCoborder ≫ j.coborderRange.ι` of the immersions of the strata, the form used by
`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum_of_flcProperty`. -/
theorem exists_stratification_flcProperty_integers {𝕜 : Type u} [Field 𝕜]
    [HasInvertibleExponent (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E) T]
    (aT : T ⟶ Spec (.of 𝕜)) (aY : Y ⟶ Spec (.of 𝕜)) [LocallyOfFiniteType aT]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) :
    ∃ R : Scheme.Stratification Y, ∀ m (k : ℕ), Etale.flcProperty (R.domain m)
      (upperStarRightDerivedIntegersModL l E g
        ((R.immersion m).liftCoborder ≫ (R.immersion m).coborderRange.ι) k) := by
  have : Finite (integersShrink.{u} l E ⧸ integersShrinkIdeal.{u} l E) :=
    finite_quotient_span_natCast_shrink l E
  obtain ⟨R, hR⟩ := Etale.exists_stratification_flcProperty_rightDerived_constantQuotSheaf
    (integersShrinkIdeal.{u} l E) g aT aY hg
  refine ⟨R, fun m k ↦ ?_⟩
  rw [Scheme.Hom.liftCoborder_ι]
  exact hR k m

end AlgebraicGeometry.ProEtale
