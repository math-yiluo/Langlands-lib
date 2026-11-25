/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.TateTwistPowerDatum
public import WeilConjectures.WeilSheaf.ConstantTwistCondensed
public import WeilConjectures.WeilSheaf.FrobeniusTwist

/-!
# The condensed Tate twist and the native constant twist `ℚ̄_ℓ ⊗ 𝓑_{χ^d}`

In the condensed model of Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed`, Weil
structures for `(Fr_X⁻¹)_*`), the native Tate sheaf `ℚ̄_ℓ(d) = ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)^d}` becomes the
regular module with structure `χ_ℓ(σ)^d` times the structure of `ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.toCondensedObjConstantTwistAdicConstantIso`). The condensed Tate
twist `ℚ̄_ℓ,X̄(d)` (`AlgebraicGeometry.ProEtale.tateTwistNat`) with its pullback datum along the
Frobenius `Fr_X^*` (`AlgebraicGeometry.ProEtale.upperStarTateTwistNatIso`), transported to the
`(Fr_X⁻¹)_*` model along `upperStarIsoLowerStarInv`, is the pair
`AlgebraicGeometry.WeilSheaf.tateTwistLowerPair`. Given
- a trivialization of `ℚ̄_ℓ,X̄(1)` carrying the pullback datum to `χ_ℓ(σ)` times the unit constraint
  (the `d = 1` input `e₁`), and
- the compatibility of the unit structures: the native structure of `ℚ̄_ℓ` in the condensed model is
  the unit constraint of `Fr_X^*` transported to `(Fr_X⁻¹)_*` (`hunit`),
the two pairs are isomorphic for every `d`
(`AlgebraicGeometry.WeilSheaf.nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor Functor.OplaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] neZero_natCast_algebraicClosure

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- Powers of the scalar `b` on the regular module are the scalar `b ^ d`. -/
lemma scalarPow_regularSmulIso_hom (b : (PadicAlgCl l)ˣ) :
    ∀ d : ℕ, (IsoAlgebra.scalarPow (regularSmulIso k₀ l X b) d).hom =
      (regularSmulIso k₀ l X (b ^ d)).hom
  | 0 => by
    simp only [IsoAlgebra.scalarPow, Iso.refl_hom, regularSmulIso_hom, pow_zero, Units.val_one,
      map_one]
    rfl
  | d + 1 => by
    rw [IsoAlgebra.scalarPow, Iso.trans_hom, scalarPow_regularSmulIso_hom b d, regularSmulIso_hom,
      regularSmulIso_hom, regularSmulIso_hom, ← End.mul_asHom]
    erw [← map_mul, ← map_mul]
    rw [← Units.val_mul, ← pow_succ']
    rfl

/-- The Frobenius of the geometric fibre `X̄`, as an isomorphism. -/
noncomputable abbrev geometricFiberFrobeniusIso :
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso

/-- The comparison `Fr_X^* ≅ (Fr_X⁻¹)_*` of the two Frobenius functors of the condensed model. -/
noncomputable abbrev frobeniusUpperStarIsoLowerStarInv :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricFiberFrobeniusIso k₀ X).hom ≅
      CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (geometricFiberFrobeniusIso k₀ X).inv :=
  CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l)
    (geometricFiberFrobeniusIso k₀ X)

/-- The condensed Tate twist `ℚ̄_ℓ,X̄(d)` with its Frobenius pullback datum, transported to the
`(Fr_X⁻¹)_*` model of condensed Weil sheaves. -/
noncomputable def tateTwistLowerPair (d : ℕ) :
    IsoAlgebra (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv) :=
  IsoAlgebra.mk (tateTwistNat (X ↘ Spec (CommRingCat.of k₀)).geometricFiber l d)
    (((frobeniusUpperStarIsoLowerStarInv k₀ l X).app _).symm ≪≫
      upperStarTateTwistNatIso l (geometricFiberFrobeniusIso k₀ X).hom
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure d)

/-- **The condensed Tate twist is the native constant twist**, given the `d = 1` trivialization
`e₁` and the compatibility `hunit` of the unit structures. -/
theorem nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist
    (e₁ : tateTwistOnePair l (geometricFiberFrobeniusIso k₀ X).hom
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≅
      IsoAlgebra.unitScalarPair _ (regularSmulIso k₀ l X (cyclotomicUnit k₀ l)))
    (hunit : (adicConstantCondensedStr k₀ l X).hom =
      (frobeniusUpperStarIsoLowerStarInv k₀ l X).inv.app (𝟙_ _) ≫
        tateUnitDatum l (geometricFiberFrobeniusIso k₀ X).hom)
    (d : ℕ) :
    Nonempty (tateTwistLowerPair k₀ l X d ≅
      (toCondensed k₀ l X).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ l X (cyclotomicUnit k₀ l ^ d)).obj
          (ProEtaleWeilSheaf.adicConstant k₀ l X))) := by
  obtain ⟨ê, hê⟩ := exists_iso_tateTwistNat_of_one l (geometricFiberFrobeniusIso k₀ X).hom
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _ e₁ d
  exact ⟨IsoAlgebra.isoMkOfConj (frobeniusUpperStarIsoLowerStarInv k₀ l X)
      (upperStarTateTwistNatIso l (geometricFiberFrobeniusIso k₀ X).hom
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure d)
      (tateUnitDatum l (geometricFiberFrobeniusIso k₀ X).hom)
      (IsoAlgebra.scalarPow (regularSmulIso k₀ l X (cyclotomicUnit k₀ l)) d).hom
      (adicConstantCondensedStr k₀ l X) (regularSmulIso k₀ l X (cyclotomicUnit k₀ l ^ d)) ê hê
      hunit (scalarPow_regularSmulIso_hom k₀ l X (cyclotomicUnit k₀ l) d).symm ≪≫
    (toCondensedObjConstantTwistAdicConstantIso k₀ l X _).symm⟩

end AlgebraicGeometry.WeilSheaf
