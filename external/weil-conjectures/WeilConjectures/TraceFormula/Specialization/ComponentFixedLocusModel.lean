/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentSpecialFibre
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances
public import WeilConjectures.TraceFormula.Specialization.NearbyCycles

/-!
# A component of the fixed locus inside the deformed fixed locus

Let `c` be contracting at `y`, `F` a fixed locus of `c` and `j : B ⟶ F` with a rational point `b`
of `B` over `y`. The deformation `𝒟_b B` of `B` along its point `b` maps to the deformation `𝒞`
of `C` (`componentModelHom`), and the two deformed legs agree on it, since `c₁ ∘ ι = c₂ ∘ ι`.
Hence it factors through the total space `F̃ = 𝒞 ×_{𝒳 ×_S 𝒳} 𝒳` of the deformed fixed locus
(`deformationFixedLocusModel`): this is the map `ι_F` of blueprint
`lemma-fixed-point-scheme-deformation` (E.20), for `Z = {x}`. If `B ⊂ C` is closed, it is a
closed immersion (`isClosedImmersion_componentFixedLocusTotalLift`).

## Main definitions and statements

- `Correspondence.IsContractingAt.componentFixedLocusTotalLift`
- `Correspondence.IsContractingAt.isClosedImmersion_componentFixedLocusTotalLift`:
  `ι_F` is a closed immersion.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  (F : c.FixedLocus) {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)

include hb in
/-- Functions vanishing at `x` pull back along `B ⊂ F ⊂ C ⟶ X` to functions vanishing at `b`. -/
lemma map_siteIdeal_le_ker_component_comp_c₁ :
    ∀ ⦃U' : B.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (j ≫ F.ι ≫ c.c₁).left ⁻¹ᵁ U.1),
      ((y ≫ c.c₁).left.ker.siteIdeal U).map ((j ≫ F.ι ≫ c.c₁).left.appLE U.1 U'.1 hU).hom ≤
        b.left.ker.siteIdeal U' :=
  map_siteIdeal_ker_le_of_comp_eq _ (by rw [← hb]; simp only [Category.assoc])

/-- The total space `F̃ = 𝒞 ×_{𝒳 ×_S 𝒳} 𝒳` of the deformation model of the fixed locus `F`. -/
noncomputable abbrev deformedFixedLocusTotal : Scheme.{u} :=
  (deformationFixedLocusModel k' c.c₁ c.c₂ hc.ker_map_le_c₁ hc.ker_map_le_c₂ F.isPullback).total

/-- The two deformed legs agree on the deformation `𝒟_b B` of a subscheme `B` of the fixed locus:
`(c̃₁, c̃₂) ∘ b̃ = Δ ∘ (c̃₁ ∘ b̃)`. -/
lemma componentModelHom_total_comp_deformationProdLiftTotal :
    (componentModelHom k' j hb).total ≫
        deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂ =
      deformationTotalMap (j ≫ F.ι ≫ c.c₁)
          (map_siteIdeal_le_ker_component_comp_c₁ F j hb) k' ≫
        deformationDiagTotal X (y ≫ c.c₁).left.ker k' := by
  have e₁ : (j ≫ F.ι) ≫ c.c₁ = j ≫ F.ι ≫ c.c₁ := Category.assoc _ _ _
  have e₂ : (j ≫ F.ι) ≫ c.c₂ = j ≫ F.ι ≫ c.c₁ := by
    rw [Category.assoc, F.w]
  apply pullback.hom_ext
  · rw [Category.assoc, deformationProdLiftTotal, pullback.lift_fst, Category.assoc,
      deformationDiagTotal, pullback.lift_fst, Category.comp_id, componentModelHom,
      deformationModelHom_total, deformationTotalMap_comp k' _ _ _ _ (by
        rw [e₁]; exact map_siteIdeal_le_ker_component_comp_c₁ F j hb)]
    exact deformationTotalMap_eq_of_eq k' e₁ _ _
  · rw [Category.assoc, deformationProdLiftTotal, pullback.lift_snd, Category.assoc,
      deformationDiagTotal, pullback.lift_snd, Category.comp_id, componentModelHom,
      deformationModelHom_total, deformationTotalMap_comp k' _ _ _ _ (by
        rw [e₂]; exact map_siteIdeal_le_ker_component_comp_c₁ F j hb)]
    exact deformationTotalMap_eq_of_eq k' e₂ _ _

/-- **The map `ι_F` of blueprint `lemma-fixed-point-scheme-deformation`** (E.20), for `Z = {x}`:
the deformation `𝒟_b B` of a subscheme `B` of the fixed locus along a rational point `b` over `y`
factors through the total space `F̃` of the deformed fixed locus. -/
noncomputable def componentFixedLocusTotalLift :
    deformationTotal B b.left.ker k' ⟶ deformedFixedLocusTotal hc k' F :=
  pullback.lift (componentModelHom k' j hb).total
    (deformationTotalMap (j ≫ F.ι ≫ c.c₁) (map_siteIdeal_le_ker_component_comp_c₁ F j hb) k')
    (componentModelHom_total_comp_deformationProdLiftTotal hc k' F j hb)

/-- The map `ι_F` lies over the morphism `𝒟_b B ⟶ 𝒞` of deformation models. -/
@[reassoc (attr := simp)]
lemma componentFixedLocusTotalLift_fst :
    componentFixedLocusTotalLift hc k' F j hb ≫ pullback.fst
        (deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂)
        (deformationDiagTotal X (y ≫ c.c₁).left.ker k') =
      (componentModelHom k' j hb).total :=
  pullback.lift_fst _ _ _

/-- **`ι_F` is a closed immersion** (blueprint `lemma-fixed-point-scheme-deformation`, `Z = {x}`):
if `B ⊂ F ⊂ C` is closed, the deformation `𝒟_b B` is a closed subscheme of the total space `F̃`
of the deformed fixed locus. -/
theorem isClosedImmersion_componentFixedLocusTotalLift [IsClosedImmersion (j ≫ F.ι).left] :
    IsClosedImmersion (componentFixedLocusTotalLift hc k' F j hb) := by
  have : IsClosedImmersion (componentModelHom k' j hb).total :=
    isClosedImmersion_componentModelHom_total k' j hb
  have : IsClosedImmersion (pullback.fst
      (deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂)
      (deformationDiagTotal X (y ≫ c.c₁).left.ker k')) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsClosedImmersion (componentFixedLocusTotalLift hc k' F j hb ≫ pullback.fst
      (deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂)
      (deformationDiagTotal X (y ≫ c.c₁).left.ker k')) := by
    rw [componentFixedLocusTotalLift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.fst
    (deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂)
    (deformationDiagTotal X (y ≫ c.c₁).left.ker k'))

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
