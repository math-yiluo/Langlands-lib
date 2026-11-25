/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFlat
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek
public import WeilConjectures.TateTwist.ComparisonSingle
public import WeilConjectures.TateTwist.EtaleTateSheafPow
public import WeilConjectures.TateTwist.FiniteRootsOfUnity
public import WeilConjectures.TateTwist.IntegralLocallyFree
public import WeilConjectures.TateTwist.TateModuleReduction

/-!
# The reduction modulo `ℓⁿ` of the integral Tate twists

Let `k` be a field of characteristic different from the prime `ℓ`, `E ⊆ ℚ̄_ℓ` a finite extension
of `ℚ_ℓ` with ring of integers `𝒪_E`, and `Y` a separated `k`-scheme of finite type. Write
`Λ = 𝒪_E ⧸ ℓⁿ` and `red_Y : Dᵇc(Y)⟦𝒪_E⟧ ⥤ D(Y_ét, Λ)` for the reduction modulo `ℓⁿ` read on the
small étale site (`ProEtale.CondensedRing.etaleReduction`). This file proves that `red_Y` sends
the integral Tate twist `𝒪_{E,Y}(d)`, `d ∈ ℕ`, to the étale Tate twist `Λ_Y(d)` of the Tate twist
datum `Etale.hasTateTwist` (`ProEtale.CondensedRing.etaleReductionIntegralTateTwistIso`).

The proof goes one factor of `red_Y = Rν_* ∘ Φ ∘ (- ⊗ᴸ Λ)` at a time:

* `𝒪_{E,Y}(d)` is locally free, hence flat, so its derived reduction is the underived one
  `Λ_Y ⊗_{𝒪_{E,Y}} 𝒪_{E,Y}(d)` placed in degree `0`
  (`Functor.leftDerivedFunctorSingleFunctorIsoOfFlat`);
* on sheaves, `Φ(Λ_Y ⊗_{𝒪_{E,Y}} 𝒪_{E,Y}(1)) ≅ ν^*(Λ ⊗ μ_{ℓⁿ})`: by transitivity of extension of
  scalars along `ℤ_ℓ ⟶ 𝒪_E ⟶ Λ` it is the reduction of the Tate module, which is
  `Λ_Y ⊗ μ_{ℓⁿ}` (`ProEtale.extendScalarsTateModuleIso`), and
  `ProEtale.finiteCoefficientModEquivalenceFreeRootsOfUnityIso` applies
  (`ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso`); all functors
  involved being monoidal, `Φ(Λ_Y ⊗_{𝒪_{E,Y}} 𝒪_{E,Y}(d)) ≅ ν^*(Λ_Y(1)^{⊗ d})`
  (`ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistNatIso`);
* `Rν_* ν^* S ≅ S` for a sheaf `S` placed in degree `0`
  (`ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso`), and `Λ_Y(d)` is
  `Λ_Y(1)^{⊗ d}` placed in degree `0` (`Etale.tateObjectNatIsoSingleFunctor`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] (n : ℕ)

/-- The reduction `ℤ̲_ℓ ⟶ (𝒪_E ⧸ ℓⁿ)̲` of ring objects of condensed abelian groups: the inclusion
`ℤ̲_ℓ ⟶ 𝒪̲_E` followed by the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`. -/
noncomputable def padicIntRingObjToIntegersModPow :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ integersModPowRingObj ℓ E n :=
  padicIntRingObjToPadicIntegers ℓ E ≫ padicIntegersRingObjToIntegersModPow ℓ E n

instance : IsMonHom (padicIntRingObjToIntegersModPow.{u} ℓ E n) := by
  unfold padicIntRingObjToIntegersModPow
  infer_instance

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] (n : ℕ)
  {k : Type u} [Field k] {X : Scheme.{u}}

omit [Fact ℓ.Prime] in
/-- If `ℓ` is invertible in the field `k`, then `ℓⁿ` is invertible on every `k`-scheme. -/
lemma isUnit_natCast_pow_of_neZero (f : X ⟶ Spec (.of k)) [NeZero (ℓ : k)] :
    IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)) := by
  have hu : IsUnit ((ℓ ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact (Ne.isUnit (NeZero.ne (ℓ : k))).pow _
  simpa using (hu.map (Scheme.ΓSpecIso (.of k)).inv.hom).map f.appTop.hom

variable [NeZero (ℓ : k)]

/-- The reduction modulo `ℓⁿ` of the integral Tate twist `𝒪_{E,X}(1)` is `Λ_X ⊗ μ_{ℓⁿ}`, for
`Λ = 𝒪_E ⧸ ℓⁿ`: by transitivity of extension of scalars along `ℤ_ℓ ⟶ 𝒪_E ⟶ Λ`, it is the
reduction modulo `ℓⁿ` of the Tate module (`ProEtale.extendScalarsTateModuleIso`). -/
noncomputable def extendScalarsIntegralTateTwistOneIntegersModPowIso (f : X ⟶ Spec (.of k)) :
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).obj (integralTateTwistOne X ℓ E) ≅
      (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).obj
        (rootsOfUnitySheaf X (ℓ ^ n)) :=
  (Mod.extendScalarsCompIsoOfEq (coefficientMap_comp_eq _ _ _ rfl X)).app (tateModule X ℓ) ≪≫
    extendScalarsTateModuleIso f ℓ (Profinite.padicIntRingObjToIntegersModPow ℓ E n) n
      (Profinite.natCast_pow_zsmul_id_integersModPowRingObj_eq_zero ℓ E n)

variable [FiniteDimensional ℚ_[ℓ] E]

/-- The reduction modulo `ℓⁿ` of the integral Tate twist `𝒪_{E,X}(1)`, read as a pro-étale sheaf
of `Λ`-modules for `Λ = 𝒪_E ⧸ ℓⁿ`, is `ν^*` of the étale Tate sheaf `Λ_X(1) = μ_{ℓⁿ} ⊗ Λ`. -/
noncomputable def finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
    (f : X ⟶ Spec (.of k)) :
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).obj
          (integralTateTwistOne X ℓ E)) ≅
      ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) X) :=
  (finiteCoefficientModEquivalence X _).functor.mapIso
      (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f) ≪≫
    finiteCoefficientModEquivalenceFreeRootsOfUnityIso X (ℓ ^ n) _
      (pow_pos (Fact.out : ℓ.Prime).pos n) (isUnit_natCast_pow_of_neZero ℓ n f) ≪≫
    ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].mapIso
      ((Etale.extendScalars _ X).mapIso
        (eqToIso (by rw [ringChar_integersModPowCoeff])))

/-- The reduction modulo `ℓⁿ` of the integral Tate twist `𝒪_{E,X}(d)`, `d ∈ ℕ`, read as a
pro-étale sheaf of `Λ`-modules for `Λ = 𝒪_E ⧸ ℓⁿ`, is `ν^*` of the tensor power `Λ_X(1)^{⊗ d}`
of the étale Tate sheaf: extension of scalars, the comparison `Φ` and `ν^*` are monoidal, and see
`finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso` for `d = 1`. -/
noncomputable def finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistNatIso
    (f : X ⟶ Spec (.of k)) :
    (d : ℕ) → (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E n)).obj
          (integralTateTwistNat X ℓ E d)) ≅
      ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        (Etale.tateSheafPow (integersModPowCoeff.{u} ℓ E n) X d)
  | 0 =>
    letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
    (finiteCoefficientModEquivalence X _).functor.mapIso (Functor.Monoidal.εIso _).symm ≪≫
      finiteCoefficientModEquivalenceUnitIso X _ ≪≫ Functor.Monoidal.εIso _
  | d + 1 =>
    letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
    (finiteCoefficientModEquivalence X _).functor.mapIso (Functor.Monoidal.μIso _ _ _).symm ≪≫
      ((finiteCoefficientModEquivalenceTensorIso X _).app _).app _ ≪≫
      tensorIso (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistNatIso f d)
        (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f) ≪≫
      Functor.Monoidal.μIso _ _ _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The reduction modulo `ℓⁿ` of the integral Tate twists**: for a separated `k`-scheme of
finite type `Y`, the reduction modulo `ℓⁿ` read on the small étale site sends the integral Tate
twist `𝒪_{E,Y}(d)`, `d ∈ ℕ`, to the étale Tate twist `Λ_Y(d)`, `Λ = 𝒪_E ⧸ ℓⁿ`. The integral
twist is flat, so its derived reduction is the underived one, which is `ν^*(Λ_Y(1)^{⊗ d})`
(`ProEtale.finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistNatIso`), and
`Rν_* ν^* S ≅ S` for a sheaf `S` placed in degree `0`. -/
noncomputable def etaleReductionIntegralTateTwistIso (d : ℕ) :
    (etaleReduction ℓ E n Y).obj (integralTateTwistBoundedConstructible ℓ E Y.hom d) ≅
      Etale.tateObject (integersModPowCoeff.{u} ℓ E n) Y.left d :=
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).mapIso
      ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).app
            (integralTateTwistBoundedConstructible ℓ E Y.hom d) ≪≫
          Functor.leftDerivedFunctorSingleFunctorIsoOfFlat _
            (isLocallyFree_integralTateTwistNat ℓ E Y.hom d).flat) ≪≫
        ((finiteCoefficientModEquivalence Y.left _).functor.mapDerivedCategorySingleFunctor
          0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistNatIso ℓ E n Y.hom d)) ≪≫
    rightDerivedComparisonLowerStarSingleFunctorIso _ _ _ ≪≫
    (Etale.tateObjectNatIsoSingleFunctor _ _ d).symm

end AlgebraicGeometry.ProEtale.CondensedRing
