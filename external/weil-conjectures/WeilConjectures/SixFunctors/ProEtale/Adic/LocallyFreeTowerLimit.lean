/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantModuleTower
public import WeilConjectures.LinearAlgebra.Basis.ULiftPowQuotient
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyFreeTowerWContractible

/-!
# The limit of a locally free torsion tower on a w-contractible object

For a tower `L` of étale sheaves on `S` with epimorphic transitions, étale-locally
`(Λ ⧸ Iⁿ⁺¹)^r`, and `W ≅ Spec R` in `S_proét` with `R` w-contractible, the abelian tower
underlying `W^* ν^* Lₙ` has limit `C(-, lim Qₙ)`:

- `AlgebraicGeometry.ProEtale.exists_isLimit_upperStar_comparisonUpperStar_powQuotientTower`,
  for any discrete rings `Qₙ ≅ (Λ ⧸ Iⁿ⁺¹)^r` compatible with the reductions;
- `ProEtale.exists_isLimit_upperStar_comparisonUpperStar_uliftPowQuotientTower`: the case
  `Λ = ULift R`, `Qₙ = (R ⧸ Jⁿ⁺¹)^r` (e.g. `R = 𝒪_E`, `J = (ℓ)`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **The limit of a locally free torsion tower on a w-contractible object.** Let `Λ` be a
local ring with a proper ideal `I`, `L` a tower of étale sheaves of `Λ`-modules on `S` with
epimorphic transitions, each `Lₙ` étale-locally `(Λ ⧸ Iⁿ⁺¹)^r`, and `W ≅ Spec R` an object of
`S_proét` with `R` w-contractible. If `(Λ ⧸ Iⁿ⁺¹)^r ≅ Qₙ` additively for discrete rings `Qₙ`,
compatibly with the reduction maps and ring maps `τₙ : Qₙ₊₁ → Qₙ` (e.g. `Λ = ULift 𝒪_E`,
`Qₙ = (𝒪_E ⧸ ℓⁿ⁺¹)^r`), then the abelian tower underlying `W^* ν^* Lₙ` has limit
`C(-, lim Qₙ)`. -/
theorem exists_isLimit_upperStar_comparisonUpperStar_powQuotientTower
    {Λ : Type (u + 1)} [CommRing Λ] [IsLocalRing Λ] (I : Ideal Λ) (hI : I ≠ ⊤) (r : ℕ)
    {S : Scheme.{u}} (L : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∀ n : ℕ, Epi (L.map (homOfLE (n.le_add_right 1)).op))
    (htriv : ∀ n, ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S),
      (∀ i, Etale (u i)) ∧ (∀ x, ∃ i, x ∈ Set.range (u i)) ∧
      ∀ i, Nonempty ((Etale.upperStar _ (u i)).obj (L.obj (op n)) ≅
        (constantSheaf (U i).smallEtaleTopology _).obj
          (ModuleCat.of Λ (Fin r → Λ ⧸ I ^ (n + 1)))))
    (W : S.ProEt) {R : CommRingCat.{u}} [IsWContractibleRing R] (eW : W.left ≅ Spec R)
    {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, CommRing (Qs n)]
    [∀ n, IsTopologicalRing (Qs n)] [∀ n, DiscreteTopology (Qs n)] (τ : ∀ n, Qs (n + 1) →+* Qs n)
    (e : ∀ n, (Fin r → Λ ⧸ I ^ (n + 1)) ≃+ ULift.{u + 1} (Qs n))
    (he : ∀ n x, e n (I.powQuotientReduction r n x) = ULift.up (τ n (e (n + 1) x).down)) :
    ∃ c : Cone (L ⋙ comparisonUpperStar _ S ⋙ ProEtale.upperStar _ W.hom ⋙
        sheafCompose (ProEt.topology W.left) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})),
      c.pt = continuousMapAbSheaf W.left (towerLimitRing τ) ∧ Nonempty (IsLimit c) := by
  obtain ⟨i⟩ := nonempty_iso_powQuotientTower_upperStar_comparisonUpperStar I hI r L hL htriv W eW
  exact exists_isLimit_continuousMapAbSheaf_of_iso W.left τ
    (fun n ↦ ModuleCat.of Λ (Fin r → Λ ⧸ I ^ (n + 1)))
    (fun n ↦ ModuleCat.ofHom (I.powQuotientReduction r n)) e he
    ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _) ≪≫ i) _)

/-- **`W^* lim ν^* Lₙ ≅ C(-, lim (R ⧸ Jⁿ⁺¹)^r)` for a locally free torsion tower**, with
coefficients `Λ = ULift R` for a local ring `R` (e.g. `𝒪_E` and `J = (ℓ)`), the quotients
`R ⧸ Jⁿ⁺¹` being discrete topological rings: the abelian tower underlying `W^* ν^* Lₙ` has
limit the sheaf of continuous maps to `lim_n (R ⧸ Jⁿ⁺¹)^r`. -/
theorem exists_isLimit_upperStar_comparisonUpperStar_uliftPowQuotientTower
    {R : Type} [CommRing R] [IsLocalRing R] (J : Ideal R) (hJ : J ≠ ⊤) (r : ℕ)
    [∀ n, TopologicalSpace (R ⧸ J ^ (n + 1))] [∀ n, DiscreteTopology (R ⧸ J ^ (n + 1))]
    [∀ n, IsTopologicalRing (R ⧸ J ^ (n + 1))]
    [IsLocalRing (ULift.{u + 1} R)]
    {S : Scheme.{u}} (L : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (hL : ∀ n : ℕ, Epi (L.map (homOfLE (n.le_add_right 1)).op))
    (htriv : ∀ n, ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S),
      (∀ i, Etale (u i)) ∧ (∀ x, ∃ i, x ∈ Set.range (u i)) ∧
      ∀ i, Nonempty ((Etale.upperStar _ (u i)).obj (L.obj (op n)) ≅
        (constantSheaf (U i).smallEtaleTopology _).obj
          (ModuleCat.of _ (Fin r → ULift.{u + 1} R ⧸ (Ideal.uliftIdeal.{u + 1} J) ^ (n + 1)))))
    (W : S.ProEt) {R' : CommRingCat.{u}} [IsWContractibleRing R'] (eW : W.left ≅ Spec R') :
    ∃ c : Cone (L ⋙ comparisonUpperStar _ S ⋙ ProEtale.upperStar _ W.hom ⋙
        sheafCompose (ProEt.topology W.left)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) AddCommGrpCat.{u + 1})),
      c.pt = continuousMapAbSheaf W.left
        (towerLimitRing (Qs := fun n ↦ Fin r → R ⧸ J ^ (n + 1))
          (J.powQuotientReductionRingHom r)) ∧ Nonempty (IsLimit c) := by
  have hI : Ideal.uliftIdeal.{u + 1} J ≠ ⊤ := by
    intro h
    apply hJ
    have h1 := Ideal.uliftIdeal_pow_map.{u + 1} J 1
    rw [pow_one, pow_one, h, Ideal.map_top] at h1
    exact h1
  exact exists_isLimit_upperStar_comparisonUpperStar_powQuotientTower _ hI r L hL htriv W eW
    (Qs := fun n ↦ Fin r → R ⧸ J ^ (n + 1))
    (J.powQuotientReductionRingHom r) (J.powQuotientULiftEquiv r)
    (J.powQuotientULiftEquiv_reduction r)

end AlgebraicGeometry.ProEtale
