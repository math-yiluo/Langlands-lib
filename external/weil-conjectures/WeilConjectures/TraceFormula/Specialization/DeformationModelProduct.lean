/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Product
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# Products and fixed loci of deformation models

For deformation models `𝒳 = D_I X ×_{𝔸¹_k} S` and `𝒴 = D_J Y ×_{𝔸¹_k} S` over the trait
`S = Spec k'⟦t⟧` (`AlgebraicGeometry.ProEtale.CondensedRing.deformationModel`), the fibre product
`𝒳 ×_S 𝒴` is a nearby cycles model of `X ⨯ Y` with special fibre `X' ⨯ Y'`
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationProdModel`). The diagonal and the maps
`(c₁, c₂) : C ⟶ X ⨯ Y` extend to morphisms of models
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationDiagModelHom`,
`AlgebraicGeometry.ProEtale.CondensedRing.deformationProdLiftModelHom`).

For the fixed locus `F = C ×_{X ⨯ X} X` of a pair `c₁, c₂ : C ⟶ X`, the fibre product of these two
morphisms of models is a model of `F` (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
.pullbackModel`) whose special fibre is the fixed locus of the special legs
`γ₁, γ₂ : C' ⟶ X'` (`AlgebraicGeometry.ProEtale.CondensedRing.fixedLocusOfDiag`): this is the model
`AlgebraicGeometry.ProEtale.CondensedRing.deformationFixedLocusModel` of the fixed square of
Varshavsky's specialization argument (*Lefschetz–Verdier trace formula and a generalization of a
theorem of Fujiwara*, §1.4–§2).

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.pullbackModel`: the fibre product of
  two morphisms of models with a common target.
- `AlgebraicGeometry.ProEtale.CondensedRing.fixedLocusOfDiag`: the fixed locus
  `C ×_{X ⨯ X} X` of two morphisms `c₁, c₂ : C ⟶ X` over a field, an equalizer of `c₁` and `c₂`
  (`AlgebraicGeometry.ProEtale.CondensedRing.fixedLocusOfDiag.isLimit`).
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationProdModel`: the product model.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationFixedLocusModel`: the model of a fixed
  locus, with the morphisms of models `deformationFixedLocusModelι` and
  `deformationFixedLocusModelD` over `ι : F ⟶ C` and `d : F ⟶ X`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Fibre products of models -/

namespace NearbyCyclesModel

section Pullback

variable {C X P F C' X' P' F' : Scheme.{u}} {MC : NearbyCyclesModel C C'}
  {MX : NearbyCyclesModel X X'} {MP : NearbyCyclesModel P P'} {c : C ⟶ P} {δ : X ⟶ P}
  {c' : C' ⟶ P'} {δ' : X' ⟶ P'} (s : MC.Hom MP c c') (t : MX.Hom MP δ δ')
  {ι : F ⟶ C} {d : F ⟶ X} (h : IsPullback ι d c δ) (ι' : F' ⟶ C') (d' : F' ⟶ X')
  (w' : ι' ≫ c' = d' ≫ δ')

/-- The fibre product of two morphisms of models `s : M_C ⟶ M_P` and `t : M_X ⟶ M_P` over a
cartesian square `F = C ×_P X`, with special fibre `F'` mapping to `C'` and `X'` compatibly: the
total space and the geometric generic fibre are the fibre products of those of `s` and `t`, and
`ε` is induced by the cartesian square. -/
noncomputable def pullbackModel : NearbyCyclesModel F F' where
  total := pullback s.total t.total
  generic := pullback s.generic t.generic
  j := pullback.map _ _ _ _ MC.j MX.j MP.j s.comm_j t.comm_j
  i := pullback.lift (ι' ≫ MC.i) (d' ≫ MX.i) (by
    rw [Category.assoc, Category.assoc, ← s.comm_i, ← t.comm_i, reassoc_of% w'])
  ε := h.lift (pullback.fst _ _ ≫ MC.ε) (pullback.snd _ _ ≫ MX.ε) (by
    rw [Category.assoc, Category.assoc, ← s.comm_ε, ← t.comm_ε, pullback.condition_assoc])

/-- The first projection of the fibre product of models, over `ι : F ⟶ C`. -/
noncomputable def pullbackModelFst : (pullbackModel s t h ι' d' w').Hom MC ι ι' where
  total := pullback.fst _ _
  generic := pullback.fst _ _
  comm_j := (pullback.lift_fst _ _ _).symm
  comm_i := (pullback.lift_fst _ _ _).symm
  comm_ε := (h.lift_fst _ _ _).symm

/-- The second projection of the fibre product of models, over `d : F ⟶ X`. -/
noncomputable def pullbackModelSnd : (pullbackModel s t h ι' d' w').Hom MX d d' where
  total := pullback.snd _ _
  generic := pullback.snd _ _
  comm_j := (pullback.lift_snd _ _ _).symm
  comm_i := (pullback.lift_snd _ _ _).symm
  comm_ε := (h.lift_snd _ _ _).symm

end Pullback

end NearbyCyclesModel

/-! ### Fixed loci as fibre products with the diagonal -/

section FixedLocus

variable {𝒞 : Type*} [Category 𝒞] {F C X : 𝒞} [HasBinaryProduct X X] {c₁ c₂ : C ⟶ X}
  {ι : F ⟶ C} {d : F ⟶ X}

/-- In a fibre product with the diagonal, `ι ≫ c₁ = d`. -/
lemma _root_.CategoryTheory.IsPullback.comp_fst_eq_of_diag
    (h : IsPullback ι d (prod.lift c₁ c₂) (diag X)) :
    ι ≫ c₁ = d := by
  simpa using h.w =≫ prod.fst

/-- In a fibre product with the diagonal, `ι ≫ c₂ = d`. -/
lemma _root_.CategoryTheory.IsPullback.comp_snd_eq_of_diag
    (h : IsPullback ι d (prod.lift c₁ c₂) (diag X)) :
    ι ≫ c₂ = d := by
  simpa using h.w =≫ prod.snd

/-- The fibre product `C ×_{X ⨯ X} X` of `(c₁, c₂)` and the diagonal is an equalizer of `c₁`
and `c₂`. -/
noncomputable def _root_.CategoryTheory.IsPullback.isLimitForkOfDiag
    (h : IsPullback ι d (prod.lift c₁ c₂) (diag X)) :
    IsLimit (Fork.ofι ι ((h.comp_fst_eq_of_diag).trans h.comp_snd_eq_of_diag.symm)) :=
  Fork.IsLimit.mk _
    (fun s ↦ h.lift s.ι (s.ι ≫ c₁) (by
      apply prod.hom_ext <;> simp [s.condition]))
    (fun s ↦ h.lift_fst _ _ _)
    (fun s m hm ↦ h.hom_ext (by simpa using hm) (by
      rw [h.lift_snd, ← h.comp_fst_eq_of_diag, ← Category.assoc,
        show m ≫ ι = s.ι by simpa using hm]))

end FixedLocus

section FixedLocusOfDiag

variable {K : Type u} [Field K] {C X : Over (Spec (.of K))} (c₁ c₂ : C ⟶ X)

/-- The fixed locus `C ×_{X ⨯ X} X` of two morphisms `c₁, c₂ : C ⟶ X` over a field `K`, as the
fibre product of the schemes. -/
noncomputable def fixedLocusOfDiag : Over (Spec (.of K)) :=
  Over.mk (pullback.fst (prod.lift c₁ c₂).left (diag X).left ≫ C.hom)

/-- The inclusion `ι : Fix(c₁, c₂) ⟶ C`. -/
noncomputable def fixedLocusOfDiag.ι : fixedLocusOfDiag c₁ c₂ ⟶ C :=
  Over.homMk (pullback.fst _ _) rfl

/-- The map `d : Fix(c₁, c₂) ⟶ X`. -/
noncomputable def fixedLocusOfDiag.d : fixedLocusOfDiag c₁ c₂ ⟶ X :=
  Over.homMk (pullback.snd _ _) (by
    change _ = pullback.fst _ _ ≫ C.hom
    rw [← Over.w (diag X), ← pullback.condition_assoc, Over.w])

/-- The fixed square `Fix(c₁, c₂) = C ×_{X ⨯ X} X` is cartesian. -/
lemma fixedLocusOfDiag.isPullback :
    IsPullback (fixedLocusOfDiag.ι c₁ c₂) (fixedLocusOfDiag.d c₁ c₂) (prod.lift c₁ c₂)
      (diag X) :=
  IsPullback.of_map (Over.forget _)
    (Over.OverMorphism.ext (by rw [Over.comp_left, Over.comp_left]; exact pullback.condition))
    (IsPullback.of_hasPullback (prod.lift c₁ c₂).left (diag X).left)

/-- The two morphisms agree on the fixed locus. -/
lemma fixedLocusOfDiag.w :
    fixedLocusOfDiag.ι c₁ c₂ ≫ c₁ = fixedLocusOfDiag.ι c₁ c₂ ≫ c₂ :=
  ((isPullback c₁ c₂).comp_fst_eq_of_diag).trans (isPullback c₁ c₂).comp_snd_eq_of_diag.symm

/-- The fixed locus is an equalizer of `c₁` and `c₂`. -/
noncomputable def fixedLocusOfDiag.isLimit :
    IsLimit (Fork.ofι (fixedLocusOfDiag.ι c₁ c₂) (fixedLocusOfDiag.w c₁ c₂)) :=
  (isPullback c₁ c₂).isLimitForkOfDiag

instance [IsSeparated X.hom] : IsClosedImmersion (fixedLocusOfDiag.ι c₁ c₂).left :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance [IsSeparated X.hom] [LocallyOfFiniteType C.hom] :
    LocallyOfFiniteType (fixedLocusOfDiag c₁ c₂).hom :=
  inferInstanceAs (LocallyOfFiniteType ((fixedLocusOfDiag.ι c₁ c₂).left ≫ C.hom))

instance [IsSeparated X.hom] [QuasiCompact C.hom] : QuasiCompact (fixedLocusOfDiag c₁ c₂).hom :=
  inferInstanceAs (QuasiCompact ((fixedLocusOfDiag.ι c₁ c₂).left ≫ C.hom))

instance [IsSeparated X.hom] [IsSeparated C.hom] : IsSeparated (fixedLocusOfDiag c₁ c₂).hom :=
  inferInstanceAs (IsSeparated ((fixedLocusOfDiag.ι c₁ c₂).left ≫ C.hom))

end FixedLocusOfDiag

/-! ### Products of deformation models -/

section Product

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (Y : Over (Spec (.of k))) (J : Y.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-- The total space `𝒳 ×_S 𝒴` of the product of two deformation models. -/
noncomputable def deformationProdTotal : Scheme.{u} :=
  pullback (deformationTotalToTrait X I k') (deformationTotalToTrait Y J k')

/-- The structure morphism `𝒳 ×_S 𝒴 ⟶ S`. -/
noncomputable def deformationProdTotalToTrait : deformationProdTotal X I Y J k' ⟶ trait k' :=
  pullback.fst _ _ ≫ deformationTotalToTrait X I k'

/-- The geometric generic fibre `(𝒳 ×_S 𝒴) ×_S Spec Ω` of the product. -/
noncomputable def deformationProdGeneric : Scheme.{u} :=
  pullback (deformationProdTotalToTrait X I Y J k') (traitGenericPoint k')

/-- The inclusion of the geometric generic fibre of the product. -/
noncomputable def deformationProdGenericToTotal :
    deformationProdGeneric X I Y J k' ⟶ deformationProdTotal X I Y J k' :=
  pullback.fst _ _

/-- The map `ε × ε : (𝒳 ×_S 𝒴)_Ω ⟶ X ⨯ Y`. -/
noncomputable def deformationProdGenericToProd :
    deformationProdGeneric X I Y J k' ⟶ (X ⨯ Y).left :=
  (isPullback_prod_left X Y).lift
    (deformationProdGenericToTotal X I Y J k' ≫ pullback.fst _ _ ≫ deformationTotalToBase X I k')
    (deformationProdGenericToTotal X I Y J k' ≫ pullback.snd _ _ ≫ deformationTotalToBase Y J k')
    (by simp only [Category.assoc, deformationTotalToBase_hom, pullback.condition_assoc])

/-- The inclusion `X' ⨯ Y' ⟶ 𝒳 ×_S 𝒴` of the special fibre of the product. -/
noncomputable def deformationProdSpecialToTotal :
    (deformationSpecialFibre X I k' ⨯ deformationSpecialFibre Y J k').left ⟶
      deformationProdTotal X I Y J k' :=
  pullback.lift ((prod.fst : _ ⨯ _ ⟶ deformationSpecialFibre X I k').left ≫
      deformationSpecialToTotal X I k')
    ((prod.snd : _ ⨯ _ ⟶ deformationSpecialFibre Y J k').left ≫ deformationSpecialToTotal Y J k')
    (by
      rw [Category.assoc, Category.assoc, (isPullback_deformationSpecialFibre X I k').w,
        (isPullback_deformationSpecialFibre Y J k').w, Over.w_assoc, Over.w_assoc])

/-- The product of two deformation models: a nearby cycles model of `X ⨯ Y` with total space
`𝒳 ×_S 𝒴`, geometric generic fibre `(𝒳 ×_S 𝒴)_Ω`, special fibre `X' ⨯ Y'` and `ε = ε × ε`. -/
noncomputable def deformationProdModel :
    NearbyCyclesModel (X ⨯ Y).left (deformationSpecialFibre X I k' ⨯
      deformationSpecialFibre Y J k').left where
  total := deformationProdTotal X I Y J k'
  generic := deformationProdGeneric X I Y J k'
  j := deformationProdGenericToTotal X I Y J k'
  i := deformationProdSpecialToTotal X I Y J k'
  ε := deformationProdGenericToProd X I Y J k'

/-! #### The diagonal -/

/-- The diagonal `𝒳 ⟶ 𝒳 ×_S 𝒳` of the total space. -/
noncomputable def deformationDiagTotal :
    deformationTotal X I k' ⟶ deformationProdTotal X I X I k' :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]
lemma deformationDiagTotal_toTrait :
    deformationDiagTotal X I k' ≫ deformationProdTotalToTrait X I X I k' =
      deformationTotalToTrait X I k' := by
  rw [deformationDiagTotal, deformationProdTotalToTrait, pullback.lift_fst_assoc,
    Category.id_comp]

/-- The diagonal of the geometric generic fibre. -/
noncomputable def deformationDiagGeneric :
    deformationGeneric X I k' ⟶ deformationProdGeneric X I X I k' :=
  pullback.map _ _ _ _ (deformationDiagTotal X I k') (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationDiagTotal_toTrait])
    (by rw [Category.comp_id, Category.id_comp])

/-- The diagonal as a morphism of models from the deformation model of `X` to the product model,
over the diagonals `Δ_X` and `Δ_{X'}`. -/
noncomputable def deformationDiagModelHom :
    (deformationModel X I k').Hom (deformationProdModel X I X I k') (diag X).left
      (diag (deformationSpecialFibre X I k')).left where
  total := deformationDiagTotal X I k'
  generic := deformationDiagGeneric X I k'
  comm_j := pullback.lift_fst _ _ _
  comm_i := by
    apply pullback.hom_ext
    · simp only [deformationModel, deformationProdModel, deformationProdSpecialToTotal,
        deformationDiagTotal, Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [← Over.comp_left_assoc, diag, prod.lift_fst, Over.id_left, Category.id_comp]
    · simp only [deformationModel, deformationProdModel, deformationProdSpecialToTotal,
        deformationDiagTotal, Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [← Over.comp_left_assoc, diag, prod.lift_snd, Over.id_left, Category.id_comp]
  comm_ε := by
    apply (isPullback_prod_left X X).hom_ext
    · simp only [deformationModel, deformationProdModel, deformationProdGenericToProd,
        Category.assoc, IsPullback.lift_fst]
      rw [← Over.comp_left, diag, prod.lift_fst, Over.id_left, Category.comp_id,
        deformationProdGenericToTotal, deformationDiagGeneric, pullback.lift_fst_assoc,
        deformationDiagTotal, Category.assoc, pullback.lift_fst_assoc, Category.id_comp]
      rfl
    · simp only [deformationModel, deformationProdModel, deformationProdGenericToProd,
        Category.assoc, IsPullback.lift_snd]
      rw [← Over.comp_left, diag, prod.lift_snd, Over.id_left, Category.comp_id,
        deformationProdGenericToTotal, deformationDiagGeneric, pullback.lift_fst_assoc,
        deformationDiagTotal, Category.assoc, pullback.lift_snd_assoc, Category.id_comp]
      rfl

/-! #### Pairs of morphisms -/

variable {X Y} {C : Over (Spec (.of k))} {K : C.left.IdealSheafData} {I J} (c₁ : C ⟶ X)
  (hJ₁ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₁.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')
  (c₂ : C ⟶ Y)
  (hJ₂ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₂.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (c₂.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')

/-- The morphism `(c₁, c₂) : 𝒞 ⟶ 𝒳 ×_S 𝒴` of total spaces. -/
noncomputable def deformationProdLiftTotal :
    deformationTotal C K k' ⟶ deformationProdTotal X I Y J k' :=
  pullback.lift (deformationTotalMap c₁ hJ₁ k') (deformationTotalMap c₂ hJ₂ k')
    (by rw [deformationTotalMap_toTrait, deformationTotalMap_toTrait])

@[reassoc (attr := simp)]
lemma deformationProdLiftTotal_toTrait :
    deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂ ≫ deformationProdTotalToTrait X I Y J k' =
      deformationTotalToTrait C K k' := by
  rw [deformationProdLiftTotal, deformationProdTotalToTrait, pullback.lift_fst_assoc,
    deformationTotalMap_toTrait]

/-- The morphism `(c₁, c₂)` of geometric generic fibres. -/
noncomputable def deformationProdLiftGeneric :
    deformationGeneric C K k' ⟶ deformationProdGeneric X I Y J k' :=
  pullback.map _ _ _ _ (deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationProdLiftTotal_toTrait])
    (by rw [Category.comp_id, Category.id_comp])

/-- The pair `(c₁, c₂) : C ⟶ X ⨯ Y` as a morphism of models from the deformation model of `C` to
the product model, over the pair `(γ₁, γ₂) : C' ⟶ X' ⨯ Y'` of the special legs. -/
noncomputable def deformationProdLiftModelHom :
    (deformationModel C K k').Hom (deformationProdModel X I Y J k') (prod.lift c₁ c₂).left
      (prod.lift (deformationSpecialFibreMap c₁ hJ₁ k')
        (deformationSpecialFibreMap c₂ hJ₂ k')).left where
  total := deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂
  generic := deformationProdLiftGeneric k' c₁ hJ₁ c₂ hJ₂
  comm_j := pullback.lift_fst _ _ _
  comm_i := by
    apply pullback.hom_ext
    · simp only [deformationModel, deformationProdModel, deformationProdSpecialToTotal,
        deformationProdLiftTotal, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left_assoc, prod.lift_fst, deformationSpecialFibreMap_toTotal]
    · simp only [deformationModel, deformationProdModel, deformationProdSpecialToTotal,
        deformationProdLiftTotal, Category.assoc, pullback.lift_snd]
      rw [← Over.comp_left_assoc, prod.lift_snd, deformationSpecialFibreMap_toTotal]
  comm_ε := by
    apply (isPullback_prod_left X Y).hom_ext
    · simp only [deformationModel, deformationProdModel, deformationProdGenericToProd,
        Category.assoc, IsPullback.lift_fst]
      rw [← Over.comp_left, prod.lift_fst, deformationProdGenericToTotal,
        deformationProdLiftGeneric, pullback.lift_fst_assoc, deformationProdLiftTotal,
        Category.assoc, pullback.lift_fst_assoc, deformationTotalMap_toBase]
      rfl
    · simp only [deformationModel, deformationProdModel, deformationProdGenericToProd,
        Category.assoc, IsPullback.lift_snd]
      rw [← Over.comp_left, prod.lift_snd, deformationProdGenericToTotal,
        deformationProdLiftGeneric, pullback.lift_fst_assoc, deformationProdLiftTotal,
        Category.assoc, pullback.lift_snd_assoc, deformationTotalMap_toBase]
      rfl

end Product

/-! ### The model of a fixed locus -/

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

/-- The fixed locus `F' = Fix(γ₁, γ₂)` of the special legs `γᵢ : C' ⟶ X'` of the deformation
models. -/
noncomputable abbrev deformationSpecialFixedLocus : Over (Spec (.of k')) :=
  fixedLocusOfDiag (deformationSpecialFibreMap c₁ hJ₁ k') (deformationSpecialFibreMap c₂ hJ₂ k')

/-- The model of a fixed locus `F = C ×_{X ⨯ X} X`: the fibre product of the morphisms of models
`(c₁, c₂) : 𝒞 ⟶ 𝒳 ×_S 𝒳` and `Δ : 𝒳 ⟶ 𝒳 ×_S 𝒳`, with special fibre the fixed locus of the special
legs. -/
noncomputable def deformationFixedLocusModel :
    NearbyCyclesModel F.left (deformationSpecialFixedLocus k' c₁ c₂ hJ₁ hJ₂).left :=
  NearbyCyclesModel.pullbackModel (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂)
    (deformationDiagModelHom X I k') (hF.map (Over.forget _))
    (fixedLocusOfDiag.ι _ _).left (fixedLocusOfDiag.d _ _).left
    (by rw [← Over.comp_left, ← Over.comp_left, (fixedLocusOfDiag.isPullback _ _).w])

/-- The morphism of models over `ι : F ⟶ C`. -/
noncomputable def deformationFixedLocusModelι :
    (deformationFixedLocusModel k' c₁ c₂ hJ₁ hJ₂ hF).Hom (deformationModel C K k') ι.left
      (fixedLocusOfDiag.ι _ _).left :=
  NearbyCyclesModel.pullbackModelFst _ _ _ _ _ _

/-- The morphism of models over `d : F ⟶ X`. -/
noncomputable def deformationFixedLocusModelD :
    (deformationFixedLocusModel k' c₁ c₂ hJ₁ hJ₂ hF).Hom (deformationModel X I k') d.left
      (fixedLocusOfDiag.d _ _).left :=
  NearbyCyclesModel.pullbackModelSnd _ _ _ _ _ _

end DeformationFixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
