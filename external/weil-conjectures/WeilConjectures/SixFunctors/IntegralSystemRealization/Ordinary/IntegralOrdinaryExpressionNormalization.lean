/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Transposing ordinary expression reduction

Source: blueprint fix-prop-coherence, primitive coefficient transpose and finite recursion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

private theorem transpose_substitution
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {R : A ⥤ C} {L : C ⥤ A} {R' : B ⥤ D} {L' : D ⥤ B}
    (adj : R ⊣ L) (adj' : R' ⊣ L') (F : A ⥤ B) (P : C ⥤ D)
    (τ : F ⋙ R' ⟶ R ⋙ P) {K : A} {M : C} (q : R.obj K ⟶ M) :
    (adj'.homEquiv _ _) (τ.app K ≫ P.map q) =
      F.map ((adj.homEquiv _ _) q) ≫
        (adj'.homEquiv _ _) (τ.app (L.obj M) ≫ P.map (adj.counit.app M)) := by
  let δ := (adj.homEquiv _ _) q
  have hq : R.map δ ≫ adj.counit.app M = q := by
    exact (adj.homEquiv _ _).symm_apply_apply q
  have hn := τ.naturality δ
  change R'.map (F.map δ) ≫ τ.app (L.obj M) = τ.app K ≫ P.map (R.map δ) at hn
  have h : τ.app K ≫ P.map q =
      R'.map (F.map δ) ≫ (τ.app (L.obj M) ≫ P.map (adj.counit.app M)) := by
    rw [← hq, P.map_comp, ← Category.assoc, ← hn, Category.assoc]
  rw [h, adj'.homEquiv_naturality_left]
  rfl

private theorem transpose_inverse_normalized
    {A C : Type*} [Category A] [Category C]
    {R : A ⥤ C} {L : C ⥤ A} (adj : R ⊣ L)
    {H : A} {M N : C} (c : L.obj M ≅ H) (r : N ⟶ R.obj H) (b : N ⟶ M)
    [IsIso r] [Mono (adj.unit.app H)]
    (h : L.map b ≫ c.hom ≫ adj.unit.app H = L.map r) :
    (adj.homEquiv _ _) (inv r ≫ b) = c.inv := by
  apply (cancel_mono c.hom).1
  apply (cancel_mono (adj.unit.app H)).1
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rw [h, ← L.map_comp, IsIso.inv_hom_id, L.map_id]
  exact Category.comp_id _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverseOrZero_eq_inv {A : Type*} [Category A] [HasZeroMorphisms A]
    {K H : A} (f : K ⟶ H) [IsIso f] : GeneratorReduction.inverseOrZero f = inv f := by
  simp only [GeneratorReduction.inverseOrZero, dite_eq_left (inferInstance : IsIso f)]

private theorem pull_transpose (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (f : U ⟶ V) {K : Integral l E V} {M : System l E V}
    (q : (calculus l E V).reduction.obj K ⟶ M) :
    ((calculus l E U).adjunction.homEquiv _ _)
      ((a.realizationModel.reductionPull f).hom.app K ≫ (pull l E f).map q) =
      (ringedPull l E f).map (((calculus l E V).adjunction.homEquiv _ _) q) ≫
        ((a.ringedModels.pull f).unit l E).app ((coefficientSequenceLimit l E V).obj M) ≫
        (pullbackTensorIntegralPullbackModel l E f).hom.app
          ((coefficientSequenceLimit l E V).obj M) ≫
        (coefficientSequenceLimit l E U).map
          ((pull l E f).map ((calculus l E V).adjunction.counit.app M)) := by
  rw [transpose_substitution (calculus l E V).adjunction (calculus l E U).adjunction
    (ringedPull l E f) (pull l E f) (a.realizationModel.reductionPull f).hom q,
    Adjunction.homEquiv_naturality_right]
  have h := (GeneratorReduction.primitiveQuotientAugmentations l E a.ringedModels o
    a.realizationModel).2 f ((coefficientSequenceLimit l E V).obj M) |>.2
  change _ = _ at h
  rw [show ((calculus l E U).adjunction.homEquiv _ _)
      ((a.realizationModel.reductionPull f).hom.app
        ((coefficientSequenceLimit l E V).obj M)) = _ from h.symm]
  simp only [Category.assoc]

private def productAdjunction {A C : Type*} [Category A] [Category C]
    {R : A ⥤ C} {L : C ⥤ A} (adj : R ⊣ L) : R.prod R ⊣ L.prod L where
  unit := adj.unit.prod adj.unit
  counit := adj.counit.prod adj.counit
  left_triangle_components K := by ext <;> exact adj.left_triangle_components _
  right_triangle_components M := by ext <;> exact adj.right_triangle_components _

private theorem tensor_transpose (o : Operations l E) (a : AmbientModels l E o)
    (W : Scheme.{u}) {K H : Integral l E W} {M N : System l E W}
    (q : (calculus l E W).reduction.obj K ⟶ M)
    (r : (calculus l E W).reduction.obj H ⟶ N) :
    ((calculus l E W).adjunction.homEquiv _ _)
      ((ordinaryTensorReduction l E a.ringedModels W).app (K, H) ≫
        (calculus l E W).systemClosed.tensor.map (Prod.mkHom q r)) =
      (a.ringedModels.tensor W).ordinary.tensor.map
        (Prod.mkHom (((calculus l E W).adjunction.homEquiv _ _) q)
          (((calculus l E W).adjunction.homEquiv _ _) r)) ≫
        ((a.ringedModels.tensor W).chi l E).app
          ((coefficientSequenceLimit l E W).obj M, (coefficientSequenceLimit l E W).obj N) ≫
        (pullbackTensorIntegralTensorModel l E W).hom.app
          ((coefficientSequenceLimit l E W).obj M, (coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceLimit l E W).map
          ((calculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((calculus l E W).adjunction.counit.app M)
              ((calculus l E W).adjunction.counit.app N))) := by
  have h := transpose_substitution (productAdjunction (calculus l E W).adjunction)
    (calculus l E W).adjunction (a.ringedModels.tensor W).ordinary.tensor
    (calculus l E W).systemClosed.tensor (ordinaryTensorReduction l E a.ringedModels W)
    (K := (K, H)) (M := (M, N)) (Prod.mkHom q r)
  have ht := (GeneratorReduction.primitiveQuotientAugmentations l E a.ringedModels o
    a.realizationModel).1 W ((coefficientSequenceLimit l E W).obj M)
      ((coefficientSequenceLimit l E W).obj N) |>.2
  conv at h =>
    rhs
    rw [Adjunction.homEquiv_naturality_right]
  have ht' : ((calculus l E W).adjunction.homEquiv _ _)
      ((ordinaryTensorReduction l E a.ringedModels W).app
        ((coefficientSequenceLimit l E W).obj M, (coefficientSequenceLimit l E W).obj N)) =
      ((a.ringedModels.tensor W).chi l E).app
          ((coefficientSequenceLimit l E W).obj M, (coefficientSequenceLimit l E W).obj N) ≫
        (pullbackTensorIntegralTensorModel l E W).hom.app
          ((coefficientSequenceLimit l E W).obj M, (coefficientSequenceLimit l E W).obj N) := by
    simpa only [ordinaryTensorReduction, Adjunction.homEquiv_unit, NatTrans.comp_app,
      Functor.whiskerRight_app, eqToIso.hom, eqToHom_app] using ht.symm
  erw [ht'] at h
  have hq : ((productAdjunction (calculus l E W).adjunction).homEquiv (K, H) (M, N))
      (Prod.mkHom q r) =
      Prod.mkHom (((calculus l E W).adjunction.homEquiv _ _) q)
        (((calculus l E W).adjunction.homEquiv _ _) r) := by
    rfl
  have hε : (productAdjunction (calculus l E W).adjunction).counit.app (M, N) =
      Prod.mkHom ((calculus l E W).adjunction.counit.app M)
        ((calculus l E W).adjunction.counit.app N) := by
    rfl
  erw [hq, hε] at h
  simpa only [Category.assoc] using h

private theorem push_transpose (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (f : U ⟶ V) {K : Integral l E U} {M : System l E U}
    (q : (calculus l E U).reduction.obj K ⟶ M) :
    ((calculus l E V).adjunction.homEquiv _ _)
      ((ordinaryPushReduction l E o a.realizationModel f).app K ≫
        (Operations.push l E o f).map q) =
      (ringedPush l E f).map (((calculus l E U).adjunction.homEquiv _ _) q) ≫
        (a.realizationModel.push l E f).inv.app M := by
  have h := GeneratorReduction.mate_reconstruction
    (calculus l E U).adjunction (calculus l E V).adjunction
    (ringedAdj l E f) (o.direct f).adj (a.realizationModel.reductionPull f).symm K
  have ht : ((calculus l E V).adjunction.homEquiv _ _)
      ((ordinaryPushReduction l E o a.realizationModel f).app K) =
      (ringedPush l E f).map ((calculus l E U).adjunction.unit.app K) ≫
        (a.realizationModel.push l E f).inv.app ((calculus l E U).reduction.obj K) := by
    apply ((calculus l E V).adjunction.homEquiv _ _).symm.injective
    simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
      ordinaryPushReduction, RealizationModel.push, Iso.symm_inv, Iso.symm_hom,
      conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv] using! h.symm
  rw [Adjunction.homEquiv_naturality_right, ht, Category.assoc]
  have hn := (a.realizationModel.push l E f).inv.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

private theorem open_transpose (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    {K : Integral l E U} (M : System l E U)
    (hM : Good l E U M) (hJ : Good l E V ((Operations.shriek l E o j).obj M))
    (q : (calculus l E U).reduction.obj K ⟶ M) :
    ((calculus l E V).adjunction.homEquiv _ _)
      (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app K) ≫
        (Operations.shriek l E o j).map q) =
      (ringedOpen l E j).map (((calculus l E U).adjunction.homEquiv _ _) q) ≫
        (a.openRealization j inferInstance M hM hJ).inv := by
  have : ∀ H, IsIso ((a.realizationModel.openReduction l E j).app H) :=
    fun H ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j H
  have : IsIso (a.realizationModel.openReduction l E j) := NatIso.isIso_of_isIso_app _
  rw [inverseOrZero_eq_inv, ← NatIso.isIso_inv_app]
  rw [transpose_substitution (calculus l E U).adjunction (calculus l E V).adjunction
    (ringedOpen l E j) (Operations.shriek l E o j)
    (inv (a.realizationModel.openReduction l E j)) q]
  have : IsIso ((calculus l E V).adjunction.unit.app
      ((coefficientSequenceLimit l E V).obj ((Operations.shriek l E o j).obj M))) :=
    (purNormalizedReconstructionOfScheme l E V (calculus l E V)).2 _
      (((purNormalizedReconstructionOfScheme l E V (calculus l E V)).1 _ hJ.1).1)
  let c := a.openRealization j inferInstance M hM hJ
  have hu := (calculus l E V).adjunction.unit.naturality c.hom
  have hi : IsIso ((calculus l E V).adjunction.unit.app
      ((coefficientSequenceLimit l E V).obj ((Operations.shriek l E o j).obj M)) ≫
      (coefficientSequenceLimit l E V).map ((calculus l E V).reduction.map c.hom)) := by
    infer_instance
  have hi' : IsIso (c.hom ≫ (calculus l E V).adjunction.unit.app
      ((ringedOpen l E j).obj ((coefficientSequenceLimit l E U).obj M))) := by
    exact hu.symm ▸ hi
  have : IsIso ((calculus l E V).adjunction.unit.app ((ringedOpen l E j).obj
      ((coefficientSequenceLimit l E U).obj M))) :=
    IsIso.of_isIso_comp_left c.hom _
  congr 1
  rw [NatIso.isIso_inv_app]
  exact transpose_inverse_normalized (calculus l E V).adjunction c
    ((a.realizationModel.openReduction l E j).app
      ((coefficientSequenceLimit l E U).obj M))
    ((Operations.shriek l E o j).map ((calculus l E U).adjunction.counit.app M))
    (a.openNormalization j M hM hJ)

-- The tensor case unifies the two recursive normalizations through nested chart transports.
/-- The transpose of the explicit ordinary coefficient recursion, followed by any
comparison satisfying the recursion laws, is the actual expression completion map.
Source: blueprint fix-prop-coherence, primitive transpose and expression-tree recursion.
(blueprint: lem-sf-integral-ordinary-expression-normalization).

Proof: induct on the expression. The variable case is inputNormalization. Naturality
of each primitive coefficient map substitutes the transpose of the child coefficient
map. The quotient augmentation equations identify the pull and tensor transposes.
For proper image, the adjoint-conjugate comparison has exactly the transpose of its
reduction mate. For open extension, transpose openNormalization and cancel the unit
at the good open image; its fixed reduction mate is invertible. Apply the recursion
law for the parent comparison, cancel its primitive isomorphism and use the child
induction hypothesis. At tensor do this in both slots. Compact support is exactly
open extension followed by proper image, with the recorded good open intermediate.
No structural generator or pair of expressions is used. -/
theorem ordinaryExpressionNormalization (D : FiniteFieldDatum.{u})
    (o : Operations l E) (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o)
    (laws : RecursionLaws l E D o a comparison)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    ((calculus l E W.left).adjunction.homEquiv _ _)
      (e.ordinaryReduction l E o a K.obj) ≫ (comparison e g).hom.app K =
      e.completionMap l E a.ringedModels K.obj := by
  induction e with
  | var i =>
    erw [Expression.ordinaryReduction, Adjunction.homEquiv_unit,
      CategoryTheory.Functor.map_id, Category.comp_id, Expression.completionMap]
    exact laws.inputNormalization i g K
  | pull f e ih =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2⟩
    erw [Expression.ordinaryReduction, pull_transpose]
    simp only [Category.assoc]
    erw [laws.pull f e g.2.2.2.2.2 g K, Iso.hom_inv_id_app_assoc]
    erw [← ((a.ringedModels.pull f.left).unit l E).naturality]
    simp only [← Category.assoc]
    erw [← CategoryTheory.Functor.map_comp, ih g.2.2.2.2.2 Ke]
    rfl
  | push f hp e ih =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2⟩
    erw [Expression.ordinaryReduction, push_transpose,
      laws.push f hp e g.2.2 g K]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, ih g.2.2 Ke]
    rfl
  | shriek j hj hq e ih =>
    let := hj
    let := hq
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2⟩
    erw [Expression.ordinaryReduction,
      open_transpose l E o a j.left _ (e.admissibleGood l E o _ Ke.property.2)
        K.property.2.1,
      laws.shriek j e g.2.2 g K]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, ih g.2.2 Ke]
    rfl
  | compactSupport f c e ih =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.1⟩
    let : QuasiCompact c.i := compactOpenQuasiCompact c g.2.2.2.2.1
    erw [Expression.ordinaryReduction, push_transpose,
      open_transpose l E o a c.i _ (e.admissibleGood l E o _ Ke.property.2)
        K.property.2.2.2,
      laws.supportRecursion f c e g.2.2.2.2.2 g K]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, ih g.2.2.2.2.2 Ke]
    rfl
  | @tensor W e t ihe iht =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.1⟩
    let Kt : (t.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.2⟩
    erw [Expression.ordinaryReduction, tensor_transpose]
    simp only [Category.assoc]
    erw [laws.tensor e t g.2.2.1 g.2.2.2 g K, Iso.hom_inv_id_app_assoc]
    erw [← ((a.ringedModels.tensor W.left).chi l E).naturality]
    erw [← CategoryTheory.Functor.map_comp_assoc]
    try simp only [prod_comp]
    erw [ihe g.2.2.1 Ke, iht g.2.2.2 Kt]
    rfl

end WeilConjectures.IntegralSystemRealization
