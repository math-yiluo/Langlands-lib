/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullCompatible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.CategoryTheory.DerivedCategory.IsZeroOfIsIsoZSMul
public import WeilConjectures.CategoryTheory.Sites.SheafModuleZSMul

/-!
# Reduction modulo `ℓⁿ`, read on the étale site: pushforward and conservativity

Write `red_X = ProEtale.CondensedRing.etaleReduction ℓ E n X :
Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small étale site. This
file supplies the two properties of `red` that, together with its compatibility with pullback
(`ProEtale.CondensedRing.etaleReductionUpperStarIso`) and with the tensor product
(`ProEtale.CondensedRing.nonempty_etaleReductionTensorIso`), transport vanishing statements from
finite to integral coefficients:

* `ProEtale.CondensedRing.etaleReductionLowerStarIso`: `red` commutes with the pushforward
  along any morphism (blueprint `lemma-change-coefficients-direct-image` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read
  on the étale site): the condensed reduction commutes with `Rf_*`
  (`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction'`), and so
  does its étale reading (`ProEtale.CondensedRing.finiteEtaleReadingLowerStarIso`);
* `ProEtale.CondensedRing.isZero_of_isZero_etaleReduction`: `red` detects zero objects (for
  `n ≠ 0`; derived Nakayama, blueprint `lemma-reduction-derived-nakayama`). The étale reading is
  fully faithful (`ProEtale.CondensedRing.finiteEtaleReadingFullyFaithful`), and if the condensed
  reduction of `K` vanishes then `ℓⁿ` acts invertibly on `K` by the reduction triangle
  `K --ℓⁿ--> K ⟶ K ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶ K[1]`
  (`ProEtale.exists_distinguished_integersModPowReduction`), so that the first derived reduction
  of `K`, on which `ℓ` acts by zero, vanishes, and `K = 0` by derived Nakayama
  (`ProEtale.isIso_of_isIso_derivedReduction_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section LowerStar

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with the pushforward** along any
morphism `d : Z ⟶ Y` of separated `k`-schemes of finite type:
`Rd_* ⋙ red_Y ≅ red_Z ⋙ Rd_*` (blueprint `lemma-change-coefficients-direct-image` for
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`). It chains the commutation of the condensed reduction with `Rd_*`
(`isIso_boundedConstructibleLowerStarIntegersModPowReduction'`) and of its étale reading
(`finiteEtaleReadingLowerStarIso`). -/
noncomputable def etaleReductionLowerStarIso (d : Z ⟶ Y) :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E d ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n Z ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) d.left) :=
  have := isNoetherian_of_locallyOfFiniteType Z.hom
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction' ℓ E n d
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d))
      (finiteEtaleReading ℓ E n Y) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleIntegersModPowReduction Z.left ℓ E n)
      (finiteEtaleReadingLowerStarIso ℓ E n d) ≪≫
    (Functor.associator _ _ _).symm

end LowerStar

section Conservative

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Reduction modulo `ℓⁿ`, read on the étale site, detects zero objects** (`n ≠ 0`): a bounded
constructible `𝒪_E`-complex `K` whose reduction `red_X K` vanishes is zero. The étale reading is
fully faithful, so the condensed reduction `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` vanishes; by the reduction triangle
`ℓⁿ` acts invertibly on `K`, hence on its first derived reduction, where `ℓ` acts by zero; so the
first derived reduction vanishes and `K = 0` by derived Nakayama (blueprint
`lemma-reduction-derived-nakayama`). -/
theorem isZero_of_isZero_etaleReduction (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {n : ℕ}
    (hn : n ≠ 0) {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (h : IsZero ((etaleReduction ℓ E n X).obj K)) : IsZero K := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  -- the étale reading is fully faithful, so the condensed reduction of `K` vanishes
  have hred : IsZero ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K) := by
    rw [IsZero.iff_id_eq_zero]
    exact (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X)).map_injective
      (h.eq_of_src _ _)
  have hext : IsZero (L(Mod.extendScalars (integersModPowReduction X.left ℓ E n)).obj K.obj) :=
    Functor.map_isZero (boundedConstructible _).ι hred
  -- by the reduction triangle, `ℓⁿ` acts invertibly on `K`
  obtain ⟨g, δ, hT⟩ := exists_distinguished_integersModPowReduction X.left ℓ E n K.obj
  have hK : IsIso ((ℓ : ℤ) ^ n • 𝟙 K.obj) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 (Functor.map_isZero _ hext)
  -- hence `K = 0` by derived Nakayama
  exact isZero_of_isIso_pow_zsmul_id X.left ℓ E hn hK

end Conservative

end AlgebraicGeometry.ProEtale.CondensedRing
