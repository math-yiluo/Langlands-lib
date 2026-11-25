/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.SixFunctors.Etale.ConstantCohomologyExt

/-!
# Pro-étale cohomology with coefficients `ℤ/ℓᵐ` as classes in `D(S_ét, ℤ/ℓᵐ)`

For a quasi-compact quasi-separated scheme `S`, the pro-étale cohomology
`Hⁿ(S_proét, C(-, ℤ_ℓ/ℓᵐ))` (`AlgebraicGeometry.ProEtale.FiniteAdicH`) is the group of morphisms
`Λ_S ⟶ Λ_S[n]` in the derived category `D(S_ét, Λ)` of étale sheaves of `Λ`-modules,
`Λ = ℤ/ℓᵐ` (`AlgebraicGeometry.ProEtale.nonempty_addEquiv_finiteAdicH_unitShift`). This is where
the finite-level Poincaré duality of `D(S_ét, Λ)` lives.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The underlying abelian sheaf of the constant étale sheaf of `Λ`-modules `Λ` is the constant
abelian sheaf `Λ`. -/
noncomputable def sheafForget₂ConstantRingIso :
    (sheafForget₂ Λ X).obj (Sheaf.constantRing X.smallEtaleTopology Λ) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of Λ) := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let r : ℤ →+* Λ := Int.castRingHom Λ
  let R := ModuleCat.restrictScalars.{u + 1} r
  let T := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : R.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} r).isLeftAdjoint
  have : V.IsLeftAdjoint := inferInstanceAs (R ⋙ T).IsLeftAdjoint
  have : X.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _ (Adjunction.ofIsLeftAdjoint V)
  exact (constantCommuteCompose X.smallEtaleTopology V).app (ModuleCat.of Λ Λ)

end Etale

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- `ℤ/ℓᵐ` is the quotient of `ℤ_ℓ` by the open subgroup `ℓᵐ ℤ_ℓ`. -/
noncomputable def zmodAddEquivQuotientPowOpenAddSubgroup (m : ℕ) :
    ZMod (l ^ m) ≃+ ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l]) :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective
      (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toAddMonoidHom
      (ZMod.ringHom_surjective _)).symm).trans
    (QuotientAddGroup.quotientAddEquivOfEq (by
      ext x
      exact (SetLike.ext_iff.1 (PadicInt.ker_toZModPow (p := l) m) x)))

/-- **Finite-level pro-étale cohomology is étale `Ext`.** On a quasi-compact quasi-separated
scheme `S`, `Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` is the group of morphisms `Λ_S ⟶ Λ_S[n]` in `D(S_ét, Λ)`,
`Λ = ℤ/ℓᵐ`. -/
theorem nonempty_addEquiv_finiteAdicH_unitShift (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] (m n : ℕ) :
    Nonempty (FiniteAdicH S l m n ≃+
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(n : ℤ)⟧)) := by
  let Λ := ULift.{u + 1} (ZMod (l ^ m))
  let A := ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])
  obtain ⟨e₁⟩ := nonempty_addEquiv_H_continuousSheaf S A n
  let eA : AddCommGrpCat.of (ULift.{u + 1} A) ≅ AddCommGrpCat.of Λ :=
    (AddEquiv.ulift.trans ((zmodAddEquivQuotientPowOpenAddSubgroup l m).symm.trans
      AddEquiv.ulift.symm)).toAddCommGrpIso
  let e₂ := (Sheaf.functorH S.smallEtaleTopology n).mapIso
    ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso eA ≪≫
      (Etale.sheafForget₂ConstantRingIso Λ S).symm)
  exact ⟨e₁.trans (e₂.addCommGroupIsoToAddEquiv.trans (Etale.unitShiftAddEquivH Λ S n).symm)⟩

end ProEtale

end AlgebraicGeometry
