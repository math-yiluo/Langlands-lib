/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationModelProduct
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Deformation models are models of finite type over the trait

The deformation model `𝒳 = D_I X ×_{𝔸¹_k} Spec k'⟦t⟧` of a separated `k`-scheme `X` of finite type
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationModel`), the product of two such models
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationProdModel`) and the model of a fixed locus
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationFixedLocusModel`) are models of finite type
over the trait (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModel`).

The fibres of the product and fixed locus models are identified by a general base change lemma
(`CategoryTheory.IsPullback.of_isPullback_of_baseChange`): the fibre product of base changes is
the base change of the fibre product.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.IsPullback

variable {𝒞 : Type*} [Category 𝒞] {T T' A B P A' B' P' Z Z' : 𝒞} {b : T' ⟶ T}
  {qA : A ⟶ T} {qB : B ⟶ T} {qP : P ⟶ T} {s : A ⟶ P} {t : B ⟶ P}
  {aA : A' ⟶ A} {pA : A' ⟶ T'} {aB : B' ⟶ B} {pB : B' ⟶ T'} {aP : P' ⟶ P} {pP : P' ⟶ T'}
  {s' : A' ⟶ P'} {t' : B' ⟶ P'} {zs : Z ⟶ A} {zt : Z ⟶ B} {zs' : Z' ⟶ A'} {zt' : Z' ⟶ B'}
  {z : Z' ⟶ Z}

/-- Fibre products commute with base change: if `A'`, `B'`, `P'` are the base changes along
`b : T' ⟶ T` of `A`, `B`, `P` over `T`, then the fibre product `Z' = A' ×_{P'} B'` is the base
change along `b` of `Z = A ×_P B`. -/
lemma of_isPullback_of_baseChange (hA : IsPullback aA pA qA b) (hB : IsPullback aB pB qB b)
    (hP : IsPullback aP pP qP b) (ht : t ≫ qP = qB) (ht' : t' ≫ pP = pB)
    (hs' : s' ≫ aP = aA ≫ s) (htP : t' ≫ aP = aB ≫ t) (hZ : IsPullback zs zt s t)
    (hZ' : IsPullback zs' zt' s' t') (hzs : z ≫ zs = zs' ≫ aA) (hzt : z ≫ zt = zt' ≫ aB) :
    IsPullback z (zs' ≫ pA) (zs ≫ qA) b := by
  have hBP : IsPullback aB t' t aP :=
    IsPullback.of_bot (by rw [ht, ht']; exact hB) htP.symm hP
  have h₁ := hZ'.flip.paste_horiz hBP
  rw [hs', ← hzt] at h₁
  exact (IsPullback.of_right h₁ hzs hZ.flip).paste_vert hA

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Model

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The deformation model of a separated `k`-scheme of finite type is a model of finite type over
the trait. -/
theorem isTraitModel_deformationModel [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] : (deformationModel X I k').IsTraitModel :=
  ⟨⟨deformationTotalToTrait X I k', pullback.snd _ _, inferInstance, inferInstance, inferInstance,
    IsPullback.of_hasPullback _ _, isPullback_deformationSpecialFibre X I k'⟩⟩

end Model

section Product

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (Y : Over (Spec (.of k))) (J : Y.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-- The special fibre `X' ⨯ Y'` of the product model is the fibre of `𝒳 ×_S 𝒴` over the closed
point of the trait. -/
lemma isPullback_deformationProdSpecialToTotal :
    IsPullback (deformationProdSpecialToTotal X I Y J k')
      (deformationSpecialFibre X I k' ⨯ deformationSpecialFibre Y J k').hom
      (deformationProdTotalToTrait X I Y J k') (traitClosedPoint k') := by
  have h := IsPullback.of_isPullback_of_baseChange (z := deformationProdSpecialToTotal X I Y J k')
    (isPullback_deformationSpecialFibre X I k')
    (isPullback_deformationSpecialFibre Y J k') (IsPullback.id_vert (traitClosedPoint k'))
    (Category.comp_id _) (Category.comp_id _) (isPullback_deformationSpecialFibre X I k').w.symm
    (isPullback_deformationSpecialFibre Y J k').w.symm
    (IsPullback.of_hasPullback (deformationTotalToTrait X I k') (deformationTotalToTrait Y J k'))
    (isPullback_prod_left _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  rw [Over.w] at h
  exact h

instance [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsSeparated (deformationProdTotalToTrait X I Y J k') := by
  have : IsSeparated (pullback.fst (deformationTotalToTrait X I k')
      (deformationTotalToTrait Y J k')) := MorphismProperty.pullback_fst _ _ inferInstance
  rw [deformationProdTotalToTrait]
  infer_instance

instance [QuasiCompact X.hom] [QuasiCompact Y.hom] :
    QuasiCompact (deformationProdTotalToTrait X I Y J k') := by
  have : QuasiCompact (pullback.fst (deformationTotalToTrait X I k')
      (deformationTotalToTrait Y J k')) := MorphismProperty.pullback_fst _ _ inferInstance
  rw [deformationProdTotalToTrait]
  infer_instance

instance [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (deformationProdTotalToTrait X I Y J k') := by
  have : LocallyOfFiniteType (pullback.fst (deformationTotalToTrait X I k')
      (deformationTotalToTrait Y J k')) := MorphismProperty.pullback_fst _ _ inferInstance
  rw [deformationProdTotalToTrait]
  infer_instance

/-- The product of the deformation models of separated `k`-schemes of finite type is a model of
finite type over the trait. -/
theorem isTraitModel_deformationProdModel [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    (deformationProdModel X I Y J k').IsTraitModel :=
  ⟨⟨deformationProdTotalToTrait X I Y J k', pullback.snd _ _, inferInstance, inferInstance,
    inferInstance, IsPullback.of_hasPullback _ _,
    isPullback_deformationProdSpecialToTotal X I Y J k'⟩⟩

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

instance [IsSeparated X.hom] : IsClosedImmersion (deformationDiagTotal X I k') :=
  inferInstanceAs (IsClosedImmersion (pullback.diagonal (deformationTotalToTrait X I k')))

/-- The model of a fixed locus `F = C ×_{X ⨯ X} X`, for `C` separated of finite type and `X`
separated over `k`, is a model of finite type over the trait. -/
theorem isTraitModel_deformationFixedLocusModel [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [IsSeparated X.hom] :
    (deformationFixedLocusModel k' c₁ c₂ hJ₁ hJ₂ hF).IsTraitModel := by
  have : IsClosedImmersion (deformationDiagModelHom X I k').total :=
    inferInstanceAs (IsClosedImmersion (deformationDiagTotal X I k'))
  have : IsClosedImmersion (pullback.fst (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂).total
      (deformationDiagModelHom X I k').total) := MorphismProperty.pullback_fst _ _ inferInstance
  refine ⟨⟨pullback.fst _ _ ≫ deformationTotalToTrait C K k',
    pullback.fst _ _ ≫ pullback.snd _ _, inferInstance, inferInstance, inferInstance, ?_, ?_⟩⟩
  · exact IsPullback.of_isPullback_of_baseChange (IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      (deformationDiagTotal_toTrait X I k') (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  · exact IsPullback.of_isPullback_of_baseChange (isPullback_deformationSpecialFibre C K k')
      (isPullback_deformationSpecialFibre X I k')
      (isPullback_deformationProdSpecialToTotal X I X I k')
      (deformationDiagTotal_toTrait X I k') (Over.w _)
      (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂).comm_i
      (deformationDiagModelHom X I k').comm_i
      (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end DeformationFixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
