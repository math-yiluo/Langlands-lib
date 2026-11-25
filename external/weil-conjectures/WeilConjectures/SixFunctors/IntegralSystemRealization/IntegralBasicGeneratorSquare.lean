/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCanonicalIsoSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryProperOpenSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExchangeProjectionSquares
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCompactificationSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Realization squares for canonical expression pairs

Source: blueprint fix-prop-coherence, strict-system expression realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverse_square {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {K H : C} {M N : D} (r : K ≅ H) (s : M ≅ N)
    (q : R.obj K ⟶ M) (t : R.obj H ⟶ N)
    (h : q ≫ s.hom = R.map r.hom ≫ t) :
    t ≫ s.inv = R.map r.inv ≫ q := by
  apply (cancel_epi (R.map r.hom)).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

private theorem ordinary_basic_square (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)}
    {r : e.ringedObj l E a.ringedModels K ⟶ t.ringedObj l E a.ringedModels K}
    (h : BasicPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K) K e t s r) :
    e.ordinaryReduction l E o a K ≫ s =
      (calculus l E W.left).reduction.map r ≫ t.ordinaryReduction l E o a K := by
  cases h with
  | isoHom h => exact ordinaryCanonicalIsoSquare l E o a K _ _ _ _ h
  | isoInv h =>
    exact inverse_square _ _ _ _ _ (ordinaryCanonicalIsoSquare l E o a K _ _ _ _ h)
  | pullUnit f hf e =>
    exact GeneratorReduction.mate_unit_square (ringedAdj l E f.left)
      (o.direct f.left).adj (a.realizationModel.reductionPull f.left).symm
      (e.ordinaryReduction l E o a K)
  | pullCounit f hf _ =>
    have hm := GeneratorReduction.mate_counit_square (ringedAdj l E f.left)
      (o.direct f.left).adj (a.realizationModel.reductionPull f.left).symm
      (Expression.ordinaryReduction l E o a t K)
    simpa only [Expression.ordinaryReduction, ordinaryPushReduction, Category.assoc,
      Iso.symm_hom, Iso.symm_inv] using! hm
  | openUnit j qj e =>
    have hi : IsIso ((a.realizationModel.openReduction l E j.left).app
        (Expression.ringedObj l E e a.ringedModels K)) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left _
    change IsIso (((mateEquiv (ringedOpenAdj l E j.left) (o.extension j.left).adj).symm
      (a.realizationModel.reductionPull j.left).hom).app
        (Expression.ringedObj l E e a.ringedModels K)) at hi
    exact GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j.left)
      (o.extension j.left).adj (a.realizationModel.reductionPull j.left).hom
      (Expression.ordinaryReduction l E o a e K)
  | openCounit j qj _ =>
    have hi : IsIso ((a.realizationModel.openReduction l E j.left).app
        ((ringedPull l E j.left).obj (Expression.ringedObj l E t a.ringedModels K))) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left _
    change IsIso (((mateEquiv (ringedOpenAdj l E j.left) (o.extension j.left).adj).symm
      (a.realizationModel.reductionPull j.left).hom).app
        ((ringedPull l E j.left).obj
          (Expression.ringedObj l E t a.ringedModels K))) at hi
    have hm := GeneratorReduction.inverse_mate_counit_square (ringedOpenAdj l E j.left)
      (o.extension j.left).adj (a.realizationModel.reductionPull j.left).hom
      (Expression.ordinaryReduction l E o a t K)
    simpa only [Expression.ordinaryReduction, RealizationModel.openReduction,
      ringedOpenAdj, Operations.shriek, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using! hm
  | properOpen k r p i w e => exact ordinaryProperOpenSquare l E o a K k r p i w e
  | exchange k r p i hr hp w e =>
    exact (ordinaryExchangeProjectionSquares l E o a K).1 k r p i hr hp w e
  | projection f hf e t => exact (ordinaryExchangeProjectionSquares l E o a K).2 f hf e t
  | compactExchange f f' cf cf' x y z wi wp hi e =>
    exact (ordinaryCompactificationSquares l E o a K).1 f f' cf cf' x y z wi wp hi e
  | compactProjection f cf e t =>
    exact (ordinaryCompactificationSquares l E o a K).2 f cf e t

private theorem realize_ordinary_square
    {C D : Type*} [Category C] [Category D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    {A B K H : C} {M N : D} (c : L.obj M ≅ K) (d : L.obj N ≅ H)
    (χ : A ⟶ K) (ψ : B ⟶ H) [IsIso χ]
    (q : R.obj A ⟶ M) (t : R.obj B ⟶ N) (s : M ⟶ N) (r : A ⟶ B)
    (hc : (adj.homEquiv _ _) q ≫ c.hom = χ)
    (hd : (adj.homEquiv _ _) t ≫ d.hom = ψ)
    (h : q ≫ s = R.map r ≫ t) :
    L.map s ≫ d.hom = c.hom ≫ inv χ ≫ r ≫ ψ := by
  let δ := (adj.homEquiv _ _) q
  have hδ : δ = χ ≫ c.inv := by
    apply (cancel_mono c.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  have : IsIso δ := by rw [hδ]; infer_instance
  have hs : δ ≫ L.map s = r ≫ (adj.homEquiv _ _) t := by
    have hh := congrArg (adj.homEquiv _ _) h
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left] at hh
    exact hh
  apply (cancel_epi δ).1
  calc
    δ ≫ (L.map s ≫ d.hom) = r ≫ ψ := by rw [← Category.assoc, hs, Category.assoc, hd]
    _ = δ ≫ (c.hom ≫ inv χ ≫ r ≫ ψ) := by
      rw [← Category.assoc, hc, IsIso.hom_inv_id_assoc]

/-- The generator case, before closure under expression contexts or composition.
Source: blueprint fix-prop-coherence, basic-generator coefficient squares.
(blueprint: lem-sf-integral-basic-generator-square).

Proof: construct the ordinary coefficient recursion independently of the comparison
family. Expression induction transposes its primitive reduction arrows and identifies
the result followed by the recursively prescribed comparison with the actual
completion map. The ordinary coefficient square follows by cases on BasicPair:
the forward canonical, proper/open, exchange/projection and compactification
squares are the four stated diagram lemmas; units and counits are the generic mate
identities; the inverse square follows by cancellation. Transpose the ordinary
square under reduction and limit. The source completion is invertible, so the
normalization equation makes its coefficient transpose invertible as well. Cancel
that transpose and substitute both completion equations to obtain the displayed
realization square. No inverse of the target completion or generator is used. -/
theorem integralBasicGeneratorSquare (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o)
    (laws : RecursionLaws l E D o a comparison)
    {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj)
    (s : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r : e.ringedObj l E a.ringedModels K.obj ⟶
      t.ringedObj l E a.ringedModels K.obj)
    (h : BasicPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e t s r)
    (he : IsIso (e.completionMap l E a.ringedModels K.obj)) :
    (coefficientSequenceLimit l E W.left).map s ≫
      (comparison t gt).hom.app ⟨K.obj, ht⟩ =
    (comparison e ge).hom.app K ≫
      @inv _ _ _ _ (e.completionMap l E a.ringedModels K.obj) he ≫
      r ≫ t.completionMap l E a.ringedModels K.obj := by
  have _ := hl
  let := he
  exact realize_ordinary_square (calculus l E W.left).adjunction
    ((comparison e ge).app K) ((comparison t gt).app ⟨K.obj, ht⟩)
    (e.completionMap l E a.ringedModels K.obj) (t.completionMap l E a.ringedModels K.obj)
    (e.ordinaryReduction l E o a K.obj) (t.ordinaryReduction l E o a K.obj) s r
    (ordinaryExpressionNormalization l E D o a comparison laws e ge K)
    (ordinaryExpressionNormalization l E D o a comparison laws t gt ⟨K.obj, ht⟩)
    (ordinary_basic_square l E o a K.obj h)

end WeilConjectures.IntegralSystemRealization
