/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitReplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
public import WeilConjectures.NumberTheory.Padics.IntegersModPow
public import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-!
# The sheaf `𝒪_{E,X}` as a limit of pullbacks of constant torsion étale sheaves

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E`, and `X` a
scheme. The abelian sheaf `𝒪_{E,X} = C(-, 𝒪_E)` on `X_proét` underlying
`AlgebraicGeometry.ProEtale.padicIntegersSheaf` (Bhatt–Scholze, *The pro-étale topology for
schemes*, §6.8) satisfies:

- `AlgebraicGeometry.ProEtale.shortExact_padicIntegersReductionShortComplex`: the sequence
  `0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ C(-, 𝒪_E ⧸ ℓⁿ) ⟶ 0` is short exact, and
  `C(-, 𝒪_E ⧸ ℓⁿ)` is the pullback `ν^*` of the constant étale sheaf with value `𝒪_E ⧸ ℓⁿ`
  (`AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf`);
- `AlgebraicGeometry.ProEtale.isLimitPadicIntegersSheafCone`: `𝒪_{E,X}` is the limit of the
  tower `n ↦ C(-, 𝒪_E ⧸ ℓⁿ)`, whose transition maps are epimorphisms by the first point.
- `AlgebraicGeometry.ProEtale.isHomotopyLimit_padicIntegersSheafCone`: by repleteness of the
  pro-étale topos this limit is a derived limit, `𝒪_{E,X} ≅ R lim_n C(-, 𝒪_E ⧸ ℓⁿ)` in the
  derived category of abelian sheaves.

This is step (3) of the comparison of `ℓ`-adic sheaves with `ℓ`-adic towers of torsion étale
sheaves for the constant sheaf: `𝒪_{E,X} ≅ R lim_n ν^*(𝒪_E ⧸ ℓⁿ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

lemma integersModPowMk_natCast_pow (n : ℕ) :
    integersModPowMk l E n ((l : integers l E) ^ n) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- **Reduction of `𝒪_{E,X}` modulo `ℓⁿ`**: the sequence
`0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ C(-, 𝒪_E ⧸ ℓⁿ) ⟶ 0` of abelian sheaves on `X_proét` is short
exact. -/
theorem shortExact_padicIntegersReductionShortComplex (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    (continuousMapReductionShortComplex X ((l : integers l E) ^ n) (integersModPowMk l E n)
      (continuous_integersModPowMk l E n) (integersModPowMk_natCast_pow l E n)).ShortExact :=
  letI := normedFieldOfAlgebra l E
  shortExact_continuousMapReductionShortComplex X _ _ _ _ (integersModPowMk_surjective l E n)
    (exists_natCast_pow_mul_eq l E n) (isEmbedding_natCast_pow_mul l E n)

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- **`𝒪_{E,X} = lim_n 𝒪_{E,X} / ℓⁿ`**: for a finite extension `E` of `ℚ_ℓ`, the abelian sheaf
`𝒪_{E,X} = C(-, 𝒪_E)` is the limit of the tower of sheaves `C(-, 𝒪_E ⧸ ℓⁿ)`, the topological ring
`𝒪_E` being the limit of the discrete rings `𝒪_E ⧸ ℓⁿ`. -/
noncomputable def isLimitPadicIntegersSheafCone :
    letI := normedFieldOfAlgebra l E
    IsLimit (continuousMapAbSheafCone X (integersModPowTransition l E)
      (fun _ ↦ continuous_of_discreteTopology) (integersModPowMk l E)
      (continuous_integersModPowMk l E) (integersModPowTransition_comp l E)) :=
  letI := normedFieldOfAlgebra l E
  isLimitContinuousMapAbSheafCone X _ _ _ _ _ (fun _ _ h ↦ integersModPowMk_injective l E h)
    (exists_integersModPowMk_eq l E) (isInducing_integersModPowMk l E)

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- The transition maps `C(-, 𝒪_E ⧸ ℓⁿ⁺¹) ⟶ C(-, 𝒪_E ⧸ ℓⁿ)` are epimorphisms. -/
lemma epi_padicIntegersTower_map (n : ℕ) :
    Epi ((continuousMapAbSheafTower X (integersModPowTransition l E)
      (fun _ ↦ continuous_of_discreteTopology)).map (homOfLE n.le_succ).op) := by
  rw [continuousMapAbSheafTower_map_succ]
  exact epi_continuousMapAbSheafMap X _ _
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.2
      (pow_dvd_pow _ n.le_succ)))

/-- **`𝒪_{E,X} = R lim_n ν^*(𝒪_E ⧸ ℓⁿ)`**: for a finite extension `E` of `ℚ_ℓ`, the sheaf
`𝒪_{E,X}` placed in degree `0` is the derived limit of the tower `n ↦ C(-, 𝒪_E ⧸ ℓⁿ)` in the
derived category of abelian sheaves on `X_proét`. The tower has epimorphic transitions, so its
limit `𝒪_{E,X}` is its derived limit by repleteness of the pro-étale topos
(`DerivedCategory.isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi`). -/
theorem isHomotopyLimit_padicIntegersSheafCone :
    letI := normedFieldOfAlgebra l E
    Pretriangulated.IsHomotopyLimit ((DerivedCategory.singleFunctor _ 0).mapCone
      (continuousMapAbSheafCone X (integersModPowTransition l E)
        (fun _ ↦ continuous_of_discreteTopology) (integersModPowMk l E)
        (continuous_integersModPowMk l E) (integersModPowTransition_comp l E))) :=
  letI := normedFieldOfAlgebra l E
  DerivedCategory.isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_ab (epi_padicIntegersTower_map X l E)
    (isLimitPadicIntegersSheafCone X l E)

end AlgebraicGeometry.ProEtale
