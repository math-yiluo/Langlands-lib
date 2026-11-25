/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedFactors

/-!

# Finiteness of `π : T' ⟶ T`

For a cover datum the morphism `π : T' ⟶ T` of strict localizations is finite
(`CoverDatum.isFinite_π`, blueprint `lemma-tangent-cones-on-cover` (ii): `T'` is finite over
`T`): `p × p` factors as the finite morphism `C × C ⟶ U × U` followed by the open immersion
`U × U ⟶ X × X`; along the first, the strict localization `T'` is an open and closed subscheme of
the finite base change of the strict localization of `U × U`
(`isOpenImmersion_and_isClosedImmersion_strictLocalizationToPullback`), and along the second the
strict localizations agree (`isIso_strictLocalizationMap_of_isOpenImmersion`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {M : CurveLocalModel k} {ℓ : ℕ}
  {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

omit [IsAlgClosed k] in
lemma fC_eq : D.fC = D.pU ≫ D.U.ι ≫ M.f := by
  rw [← Category.assoc, D.pU_ι, D.p_comp]

/-- The finite morphism `pU × pU : C ×_k C ⟶ U ×_k U`. -/
noncomputable def gU : D.S' ⟶ pullback (D.U.ι ≫ M.f) (D.U.ι ≫ M.f) :=
  pullback.map _ _ _ _ D.pU D.pU (𝟙 _) (by rw [Category.comp_id, D.fC_eq])
    (by rw [Category.comp_id, D.fC_eq])

instance : IsFinite D.gU :=
  MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance D.fC_eq D.fC_eq

/-- The open immersion `U ×_k U ⟶ X ×_k X`. -/
noncomputable def jUU : pullback (D.U.ι ≫ M.f) (D.U.ι ≫ M.f) ⟶ pullback M.f M.f :=
  pullback.map _ _ _ _ D.U.ι D.U.ι (𝟙 _) (by simp) (by simp)

instance : IsOpenImmersion D.jUU := by
  unfold jUU
  infer_instance

omit [IsAlgClosed k] in
lemma gU_jUU : D.gU ≫ D.jUU = D.g := by
  apply pullback.hom_ext <;> simp [gU, jUU, g, D.pU_ι]

lemma spec_map_strictHenselizationEval_comp_eqToHom {S : Scheme.{u}} {a b : Spec (.of k) ⟶ S}
    (e : a = b) (h : strictLocalization a = strictLocalization b) :
    Spec.map (strictHenselizationEval a) ≫ eqToHom h = Spec.map (strictHenselizationEval b) := by
  subst e
  simp

omit [IsAlgClosed k] in
lemma s'_gU_jUU : (D.s' ≫ D.gU) ≫ D.jUU = M.diagPoint := by
  rw [Category.assoc, D.gU_jUU, D.s'_comp_g]

/-- `π` factors through the strict localization of `U ×_k U`. -/
lemma π_eq : D.π = strictLocalizationMap D.gU D.s' ≫
    strictLocalizationMap D.jUU (D.s' ≫ D.gU) ≫ eqToHom (by rw [D.s'_gU_jUU]) := by
  refine hom_strictLocalization_ext M.diagPoint ?_ (Spec.map (strictHenselizationEval D.s'))
    (IsLocalRing.closedPoint k) (spec_map_strictHenselizationEval_apply _ _) ?_
  · rw [D.π_comp_τ, Category.assoc, Category.assoc,
      eqToHom_comp_strictLocalizationToBase D.s'_gU_jUU,
      strictLocalizationMap_comp_strictLocalizationToBase, ← Category.assoc,
      strictLocalizationMap_comp_strictLocalizationToBase, Category.assoc, D.gU_jUU]
  · rw [π, ← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
      spec_map_strictHenselizationEval_comp_eqToHom D.s'_comp_g, ← Category.assoc,
      spec_map_strictHenselizationEval_comp_strictLocalizationMap, ← Category.assoc,
      spec_map_strictHenselizationEval_comp_strictLocalizationMap,
      spec_map_strictHenselizationEval_comp_eqToHom D.s'_gU_jUU]

/-- **`π : T' ⟶ T` is finite** (blueprint `lemma-tangent-cones-on-cover` (ii)). -/
instance isFinite_π : IsFinite D.π := by
  rw [π_eq]
  have : IsFinite (strictLocalizationMap D.gU D.s') := by
    rw [show strictLocalizationMap D.gU D.s' = strictLocalizationToPullback D.gU D.s' ≫
      pullback.fst _ _ from (strictLocalizationToPullback_fst D.gU D.s').symm]
    infer_instance
  have := isIso_strictLocalizationMap_of_isOpenImmersion D.jUU (D.s' ≫ D.gU)
  infer_instance

end AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum
