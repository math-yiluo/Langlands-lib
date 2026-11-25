/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-!
# `ℓ`-adic sheaves on trivial coverings

Let `p : P ⟶ X` be a *trivial covering*: a separated morphism with finitely many sections
`σ k : X ⟶ P` such that `∐ₖ X ⟶ P`, `σ k` on the `k`-th summand, is an isomorphism. Then the
pushforward along `p` of a lisse `ℓ`-adic sheaf `F` is lisse: `F` is the sum of the
`(σ k)_* (σ k)^* F`, so that `p_* F ≅ ⨁ₖ (σ k)^* F`. Likewise a constructible sheaf on a finite
disjoint union of spectra of fields is lisse, being lisse on each of them.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit_of_cover`:
  a sheaf is the sum of its restrictions to finitely many disjoint closed subschemes covering the
  scheme.
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.adicLowerStar_of_isIso_sigmaDesc`: pushforward
  along a trivial covering preserves lisse sheaves.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isIso_sigmaDesc`:
  constructible sheaves on a finite disjoint union of spectra of fields are lisse.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Decomposition

variable {X : Scheme.{u}} {κ : Type} [Finite κ] {Z : κ → Scheme.{u}} (s : ∀ k, Z k ⟶ X)
  [∀ k, IsClosedImmersion (s k)]

/-- **A sheaf is the sum of its restrictions to finitely many disjoint closed subschemes
covering the scheme.** For closed immersions `s k : Z k ⟶ X` with pairwise disjoint ranges
covering `X`, the units `F ⟶ (s k)_* (s k)^* F` induce an isomorphism
`F ≅ ⨁ₖ (s k)_* (s k)^* F`: along `s k` all summands but the `k`-th vanish, while the `k`-th
component is inverse to the counit isomorphism by a triangle identity. -/
theorem isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit_of_cover
    (hs : Pairwise fun k k' ↦ Disjoint (Set.range (s k).base) (Set.range (s k').base))
    (hcov : ∀ x, ∃ k, x ∈ Set.range (s k).base) (F : AdicSheaf l X) :
    IsIso (biproduct.lift fun k ↦ (adicUpperStarLowerStarAdjunction l (s k)).unit.app F) := by
  have hcl (k : κ) : IsClosed (Set.range (s k).base) := (s k).isClosedEmbedding.isClosed_range
  refine isIso_of_forall_isIso_adicUpperStar_map s hcov _ fun k ↦ ?_
  let Φ := (s k)^*ᵃ[l]
  let adj := adicUpperStarLowerStarAdjunction l (s k)
  have hk : IsIso (Φ.map (adj.unit.app F)) := by
    have : IsIso (Φ.map (adj.unit.app F) ≫ adj.counit.app (Φ.obj F)) := by
      rw [adj.left_triangle_components F]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have : IsIso (biproduct.lift fun k' ↦
      Φ.map ((adicUpperStarLowerStarAdjunction l (s k')).unit.app F)) :=
    biproduct.isIso_lift_of_isZero _ k fun k' hk' ↦
      isZero_adicUpperStar_adicLowerStar_of_disjoint (s k') (hcl k') (s k) (hs hk') _
  have h := biproduct.map_lift_mapBiprod Φ _
    (fun k' ↦ (adicUpperStarLowerStarAdjunction l (s k')).unit.app F)
  rw [← h] at this
  exact IsIso.of_isIso_comp_right (Φ.map _) ((Φ.mapBiproduct _).hom)

end Decomposition

/-- A finite direct sum of lisse sheaves is lisse. -/
theorem IsAdicLisseSheaf.biproduct {X : Scheme.{u}} {κ : Type} [Finite κ]
    {S : κ → AdicSheaf l X} (hS : ∀ k, IsAdicLisseSheaf (S k)) : IsAdicLisseSheaf (⨁ S) := by
  have := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  exact (IsAdicLisseSheaf.biproduct_fin _ (fun i ↦ S (e.symm i)) fun i ↦ hS _).of_iso
    (biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _)

section TrivialCovering

variable {P X : Scheme.{u}} {κ : Type} [Finite κ] (σ : κ → (X ⟶ P))

omit [Finite κ] in
/-- The sections of a trivial covering have pairwise disjoint ranges. -/
lemma pairwise_disjoint_range_of_isIso_sigmaDesc [IsIso (Sigma.desc σ)] :
    Pairwise fun k k' ↦ Disjoint (Set.range (σ k).base) (Set.range (σ k').base) := by
  intro k k' hkk'
  have h (k : κ) : Set.range (σ k).base =
      (Sigma.desc σ).base '' Set.range (Sigma.ι (fun _ : κ ↦ X) k).base := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, colimit.ι_desc]
    rfl
  rw [h, h]
  refine Disjoint.image ?_ (Set.injOn_of_injective (Sigma.desc σ).isOpenEmbedding.injective)
    (Set.subset_univ _) (Set.subset_univ _)
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  exact hkk' (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 hb)).symm

omit [Finite κ] in
/-- The sections of a trivial covering cover it. -/
lemma exists_mem_range_of_isIso_sigmaDesc [IsIso (Sigma.desc σ)] (x : P) :
    ∃ k, x ∈ Set.range (σ k).base := by
  have hx : (Sigma.desc σ).base ((inv (Sigma.desc σ)).base x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  obtain ⟨k, z, hz⟩ := (sigmaOpenCover (fun _ : κ ↦ X)).exists_eq ((inv (Sigma.desc σ)).base x)
  refine ⟨k, z, ?_⟩
  rw [← hx, ← hz, ← Scheme.Hom.comp_apply, sigmaOpenCover_f, colimit.ι_desc]
  rfl

omit [Finite κ] in
/-- The sections of a trivial covering are open immersions. -/
lemma isOpenImmersion_of_isIso_sigmaDesc [IsIso (Sigma.desc σ)] (k : κ) :
    IsOpenImmersion (σ k) := by
  have h : Sigma.ι (fun _ : κ ↦ X) k ≫ Sigma.desc σ = σ k := colimit.ι_desc _ _
  rw [← h]
  infer_instance

/-- **Pushforward along a trivial covering preserves lisse sheaves.** If `p : P ⟶ X` is
separated with finitely many sections `σ k` inducing an isomorphism `∐ₖ X ≅ P`, then for a
lisse sheaf `F` on `P`, `p_* F ≅ ⨁ₖ (σ k)^* F` is lisse: the `σ k` are closed immersions, being
sections of a separated morphism, with disjoint ranges covering `P`, so that
`F ≅ ⨁ₖ (σ k)_* (σ k)^* F`. -/
theorem IsAdicLisseSheaf.adicLowerStar_of_isIso_sigmaDesc (p : P ⟶ X) [IsSeparated p]
    (hσ : ∀ k, σ k ≫ p = 𝟙 X) [IsIso (Sigma.desc σ)] {F : AdicSheaf l P}
    (hF : IsAdicLisseSheaf F) : IsAdicLisseSheaf ((p)_*ᵃ[l].obj F) := by
  have (k : κ) : IsClosedImmersion (σ k) := by
    have : IsClosedImmersion (σ k ≫ p) := by
      rw [hσ]
      infer_instance
    exact IsClosedImmersion.of_comp (σ k) p
  let e : (p)_*ᵃ[l].obj F ≅ ⨁ fun k ↦ (σ k)^*ᵃ[l].obj F :=
    (p)_*ᵃ[l].mapIso (@asIso _ _ _ _ _
      (isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit_of_cover σ
        (pairwise_disjoint_range_of_isIso_sigmaDesc σ)
        (exists_mem_range_of_isIso_sigmaDesc σ) F)) ≪≫
      (p)_*ᵃ[l].mapBiproduct _ ≪≫
      biproduct.mapIso fun k ↦ (adicLowerStarComp l (σ k) p).app _ ≪≫
        (adicLowerStarCongr l (hσ k)).app _ ≪≫ (adicLowerStarId l X).app _
  exact (IsAdicLisseSheaf.biproduct fun k ↦ IsAdicLisseSheaf.upperStar (σ k) hF).of_iso e.symm

omit [Finite κ] in
/-- **Constructible sheaves on a disjoint union of spectra of fields are lisse.** If the
morphisms `σ k : Spec K ⟶ P` induce an isomorphism `∐ₖ Spec K ≅ P`, then every constructible
sheaf on `P` is lisse: the `σ k` form a Zariski cover of `P`, and a constructible sheaf on the
spectrum of a field is lisse. -/
theorem IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isIso_sigmaDesc {K : Type u} [Field K]
    (σ : κ → (Spec (.of K) ⟶ P)) [IsIso (Sigma.desc σ)] {F : AdicSheaf l P}
    (hF : IsAdicConstructibleSheaf F) : IsAdicLisseSheaf F := by
  have := isOpenImmersion_of_isIso_sigmaDesc σ
  exact IsAdicLisseSheaf.of_cover σ (Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2
      ⟨exists_mem_range_of_isIso_sigmaDesc σ, fun k ↦ inferInstance⟩)) fun k ↦
    (hF.upperStar (σ k)).isAdicLisseSheaf_of_isField
end TrivialCovering

end AlgebraicGeometry.ProEtale
