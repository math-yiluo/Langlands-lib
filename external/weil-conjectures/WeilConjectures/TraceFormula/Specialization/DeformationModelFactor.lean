/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationModelProduct

/-!

# Projections of product models and factorizations of `ε`

This file constructs
* the projections `𝒳 ×_S 𝒴 ⟶ 𝒳` and `𝒳 ×_S 𝒴 ⟶ 𝒴` of the product of two deformation models as
  morphisms of models
  (`AlgebraicGeometry.ProEtale.CondensedRing.deformationProdFstModelHom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.deformationProdSndModelHom`);
* factorizations `ε = j ≫ e` of the identifications of the deformation models, their products and
  the models of fixed loci through their total spaces
  (`AlgebraicGeometry.ProEtale.CondensedRing.deformationModel_exists_comp_ε`,
  `AlgebraicGeometry.ProEtale.CondensedRing.deformationProdModel_exists_comp_ε`,
  `AlgebraicGeometry.ProEtale.CondensedRing.deformationFixedLocusModel_exists_comp_ε`).
  Such a factorization says that the complexes `Lε^* A` on the geometric generic fibre come from
  the generic fibre; the finiteness and Künneth theorems for nearby cycles are stated for these
  models.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Pullback

variable {C X P F C' X' P' F' : Scheme.{u}} {MC : NearbyCyclesModel C C'}
  {MX : NearbyCyclesModel X X'} {MP : NearbyCyclesModel P P'} {c : C ⟶ P} {δ : X ⟶ P}
  {c' : C' ⟶ P'} {δ' : X' ⟶ P'} (s : MC.Hom MP c c') (t : MX.Hom MP δ δ')
  {ι : F ⟶ C} {d : F ⟶ X} (h : IsPullback ι d c δ) (ι' : F' ⟶ C') (d' : F' ⟶ X')
  (w' : ι' ≫ c' = d' ≫ δ')

/-- If the identifications `ε` of `M_C` and `M_X` factor through their total spaces, compatibly
with `s` and `t` and a morphism `e_P` from the total space of `M_P`, then so does the
identification of the fibre product of models. -/
lemma pullbackModel_exists_comp_ε {eC : MC.total ⟶ C} {eX : MX.total ⟶ X} {eP : MP.total ⟶ P}
    (hC : MC.j ≫ eC = MC.ε) (hX : MX.j ≫ eX = MX.ε) (hs : s.total ≫ eP = eC ≫ c)
    (ht : t.total ≫ eP = eX ≫ δ) :
    ∃ e : (pullbackModel s t h ι' d' w').total ⟶ F,
      (pullbackModel s t h ι' d' w').j ≫ e = (pullbackModel s t h ι' d' w').ε := by
  refine ⟨h.lift (pullback.fst _ _ ≫ eC) (pullback.snd _ _ ≫ eX)
    (by rw [Category.assoc, Category.assoc, ← hs, ← ht, pullback.condition_assoc]), ?_⟩
  apply h.hom_ext
  · simp only [pullbackModel, Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc, hC]
  · simp only [pullbackModel, Category.assoc, IsPullback.lift_snd, pullback.lift_snd_assoc, hX]

end Pullback

end NearbyCyclesModel

section Model

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The identification of the deformation model factors through its total space. -/
lemma deformationModel_exists_comp_ε :
    ∃ e : (deformationModel X I k').total ⟶ X.left,
      (deformationModel X I k').j ≫ e = (deformationModel X I k').ε :=
  ⟨deformationTotalToBase X I k', rfl⟩

end Model

section Product

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (Y : Over (Spec (.of k))) (J : Y.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-- The map `𝒳 ×_S 𝒴 ⟶ X ⨯ Y` of the total space of the product of two deformation models. -/
noncomputable def deformationProdTotalToProd : deformationProdTotal X I Y J k' ⟶ (X ⨯ Y).left :=
  (isPullback_prod_left X Y).lift (pullback.fst _ _ ≫ deformationTotalToBase X I k')
    (pullback.snd _ _ ≫ deformationTotalToBase Y J k')
    (by simp only [Category.assoc, deformationTotalToBase_hom, pullback.condition_assoc])

@[reassoc (attr := simp)]
lemma deformationProdTotalToProd_fst :
    deformationProdTotalToProd X I Y J k' ≫ (prod.fst : X ⨯ Y ⟶ X).left =
      pullback.fst _ _ ≫ deformationTotalToBase X I k' :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma deformationProdTotalToProd_snd :
    deformationProdTotalToProd X I Y J k' ≫ (prod.snd : X ⨯ Y ⟶ Y).left =
      pullback.snd _ _ ≫ deformationTotalToBase Y J k' :=
  IsPullback.lift_snd _ _ _ _

/-- The identification `ε × ε` of the product model factors through `𝒳 ×_S 𝒴 ⟶ X ⨯ Y`. -/
lemma deformationProdGenericToTotal_toProd :
    deformationProdGenericToTotal X I Y J k' ≫ deformationProdTotalToProd X I Y J k' =
      deformationProdGenericToProd X I Y J k' := by
  apply (isPullback_prod_left X Y).hom_ext
  · rw [Category.assoc, deformationProdTotalToProd_fst, deformationProdGenericToProd,
      IsPullback.lift_fst]
  · rw [Category.assoc, deformationProdTotalToProd_snd, deformationProdGenericToProd,
      IsPullback.lift_snd]

/-- The identification of the product model factors through its total space. -/
lemma deformationProdModel_exists_comp_ε :
    ∃ e : (deformationProdModel X I Y J k').total ⟶ (X ⨯ Y).left,
      (deformationProdModel X I Y J k').j ≫ e = (deformationProdModel X I Y J k').ε :=
  ⟨deformationProdTotalToProd X I Y J k', deformationProdGenericToTotal_toProd X I Y J k'⟩

/-- The first projection `(𝒳 ×_S 𝒴)_Ω ⟶ 𝒳_Ω` of geometric generic fibres. -/
noncomputable def deformationProdFstGeneric :
    deformationProdGeneric X I Y J k' ⟶ deformationGeneric X I k' :=
  pullback.map _ _ _ _ (pullback.fst _ _) (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; rfl)
    (by rw [Category.comp_id, Category.id_comp])

/-- The second projection `(𝒳 ×_S 𝒴)_Ω ⟶ 𝒴_Ω` of geometric generic fibres. -/
noncomputable def deformationProdSndGeneric :
    deformationProdGeneric X I Y J k' ⟶ deformationGeneric Y J k' :=
  pullback.map _ _ _ _ (pullback.snd _ _) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationProdTotalToTrait, pullback.condition])
    (by rw [Category.comp_id, Category.id_comp])

/-- The first projection of the product of two deformation models, as a morphism of models over
the projections `X ⨯ Y ⟶ X` and `X' ⨯ Y' ⟶ X'`. -/
noncomputable def deformationProdFstModelHom :
    (deformationProdModel X I Y J k').Hom (deformationModel X I k') (prod.fst : X ⨯ Y ⟶ X).left
      (prod.fst : deformationSpecialFibre X I k' ⨯ deformationSpecialFibre Y J k' ⟶ _).left where
  total := pullback.fst _ _
  generic := deformationProdFstGeneric X I Y J k'
  comm_j := pullback.lift_fst _ _ _
  comm_i := (pullback.lift_fst _ _ _).symm
  comm_ε := by
    change _ ≫ deformationGenericToTotal _ _ _ ≫ deformationTotalToBase _ _ _ =
      deformationProdGenericToProd X I Y J k' ≫ _
    rw [← deformationProdGenericToTotal_toProd, Category.assoc, deformationProdTotalToProd_fst,
      deformationProdFstGeneric, deformationGenericToTotal, pullback.lift_fst_assoc]
    rfl

/-- The second projection of the product of two deformation models, as a morphism of models over
the projections `X ⨯ Y ⟶ Y` and `X' ⨯ Y' ⟶ Y'`. -/
noncomputable def deformationProdSndModelHom :
    (deformationProdModel X I Y J k').Hom (deformationModel Y J k') (prod.snd : X ⨯ Y ⟶ Y).left
      (prod.snd : deformationSpecialFibre X I k' ⨯ deformationSpecialFibre Y J k' ⟶ _).left where
  total := pullback.snd _ _
  generic := deformationProdSndGeneric X I Y J k'
  comm_j := pullback.lift_fst _ _ _
  comm_i := (pullback.lift_snd _ _ _).symm
  comm_ε := by
    change _ ≫ deformationGenericToTotal _ _ _ ≫ deformationTotalToBase _ _ _ =
      deformationProdGenericToProd X I Y J k' ≫ _
    rw [← deformationProdGenericToTotal_toProd, Category.assoc, deformationProdTotalToProd_snd,
      deformationProdSndGeneric, deformationGenericToTotal, pullback.lift_fst_assoc]
    rfl

/-- The diagonal of the total spaces is compatible with the diagonal of `X`. -/
@[reassoc]
lemma deformationDiagTotal_toProd :
    deformationDiagTotal X I k' ≫ deformationProdTotalToProd X I X I k' =
      deformationTotalToBase X I k' ≫ (diag X).left := by
  apply (isPullback_prod_left X X).hom_ext
  · rw [Category.assoc, deformationProdTotalToProd_fst, deformationDiagTotal,
      pullback.lift_fst_assoc, Category.id_comp, Category.assoc, ← Over.comp_left, diag,
      prod.lift_fst, Over.id_left, Category.comp_id]
  · rw [Category.assoc, deformationProdTotalToProd_snd, deformationDiagTotal,
      pullback.lift_snd_assoc, Category.id_comp, Category.assoc, ← Over.comp_left, diag,
      prod.lift_snd, Over.id_left, Category.comp_id]

variable {X Y} {C : Over (Spec (.of k))} {K : C.left.IdealSheafData} {I J} (c₁ : C ⟶ X)
  (hJ₁ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₁.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')
  (c₂ : C ⟶ Y)
  (hJ₂ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₂.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (c₂.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')

/-- The morphism `(c₁, c₂)` of total spaces is compatible with `(c₁, c₂) : C ⟶ X ⨯ Y`. -/
@[reassoc]
lemma deformationProdLiftTotal_toProd :
    deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂ ≫ deformationProdTotalToProd X I Y J k' =
      deformationTotalToBase C K k' ≫ (prod.lift c₁ c₂).left := by
  apply (isPullback_prod_left X Y).hom_ext
  · rw [Category.assoc, deformationProdTotalToProd_fst, deformationProdLiftTotal,
      pullback.lift_fst_assoc, deformationTotalMap_toBase, Category.assoc, ← Over.comp_left,
      prod.lift_fst]
  · rw [Category.assoc, deformationProdTotalToProd_snd, deformationProdLiftTotal,
      pullback.lift_snd_assoc, deformationTotalMap_toBase, Category.assoc, ← Over.comp_left,
      prod.lift_snd]

end Product

section DeformationFixedLocus

variable {k : Type u} [Field k] {C X : Over (Spec (.of k))} {K : C.left.IdealSheafData}
  {I : X.left.IdealSheafData} (k' : Type u) [Field k'] [Algebra k k'] (c₁ c₂ : C ⟶ X)
  (hJ₁ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₁.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')
  (hJ₂ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₂.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₂.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')
  {F : Over (Spec (.of k))} {ι : F ⟶ C} {d : F ⟶ X}
  (hF : IsPullback ι d (prod.lift c₁ c₂) (diag X))

/-- The identification of the model of a fixed locus factors through its total space. -/
lemma deformationFixedLocusModel_exists_comp_ε :
    ∃ e : (deformationFixedLocusModel k' c₁ c₂ hJ₁ hJ₂ hF).total ⟶ F.left,
      (deformationFixedLocusModel k' c₁ c₂ hJ₁ hJ₂ hF).j ≫ e =
        (deformationFixedLocusModel k' c₁ c₂ hJ₁ hJ₂ hF).ε :=
  NearbyCyclesModel.pullbackModel_exists_comp_ε _ _ _ _ _ _ (eC := deformationTotalToBase C K k')
    (eX := deformationTotalToBase X I k') (eP := deformationProdTotalToProd X I X I k') rfl rfl
    (deformationProdLiftTotal_toProd k' c₁ hJ₁ c₂ hJ₂) (deformationDiagTotal_toProd X I k')

end DeformationFixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
