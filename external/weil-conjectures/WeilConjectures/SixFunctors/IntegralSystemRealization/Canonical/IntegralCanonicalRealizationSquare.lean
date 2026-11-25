/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralBasicGeneratorSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenRealizationNaturality
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Realization squares for canonical expression pairs

Source: blueprint fix-prop-coherence, strict-system expression realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_square {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C) (F G : C ⥤ D) (ε : T ⟶ 𝟭 C) (α : T ⋙ F ⟶ G)
    {M N : C} {H J : D} (s : M ⟶ N) (r : H ⟶ J)
    (x : F.obj M ⟶ H) (y : F.obj N ⟶ J)
    (u : G.obj M ⟶ H) (v : G.obj N ⟶ J)
    [Epi (F.map (ε.app M))]
    (hx : F.map (ε.app M) ≫ x = α.app M ≫ u)
    (hy : F.map (ε.app N) ≫ y = α.app N ≫ v)
    (h : G.map s ≫ v = u ≫ r) : F.map s ≫ y = x ≫ r := by
  apply (cancel_epi (F.map (ε.app M))).1
  calc
    F.map (ε.app M) ≫ F.map s ≫ y =
        F.map (T.map s) ≫ F.map (ε.app N) ≫ y := by
      have hn : ε.app M ≫ s = T.map s ≫ ε.app N := (ε.naturality s).symm
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ F.map q ≫ y) hn
    _ = F.map (T.map s) ≫ α.app N ≫ v := by rw [hy]
    _ = α.app M ≫ G.map s ≫ v := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun q ↦ q ≫ v) (α.naturality s)
    _ = α.app M ≫ u ≫ r := by rw [h]
    _ = F.map (ε.app M) ≫ x ≫ r := by
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ r) hx.symm

private theorem natural_square {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (L : C ⥤ E) (B : E ⥤ D) (α : F ⟶ L ⋙ B)
    {M N : C} {H J : E} (s : M ⟶ N) (r : H ⟶ J)
    (u : L.obj M ⟶ H) (v : L.obj N ⟶ J)
    (h : L.map s ≫ v = u ≫ r) :
    F.map s ≫ (α.app N ≫ B.map v) = (α.app M ≫ B.map u) ≫ B.map r := by
  rw [← Category.assoc, α.naturality s]
  simp only [Functor.comp_map, Category.assoc, ← B.map_comp, h]

private theorem canonical_square (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o)
    (laws : RecursionLaws l E D o a comparison)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    (K : ∀ i, Integral l E (X i).left)
    (hK : ∀ i, sfIntegralConstructible l E (X i).left (K i) ∧
      Good l E (X i).left ((calculus l E (X i).left).reduction.obj (K i)))
    {W : Over (Spec (.of D.k))} {e t : Expression _ I X W}
    {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)}
    {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K}
    (h : CanonicalPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K) K e t s r) :
    ∀ (ge : e.geometric) (gt : t.geometric)
      (he : e.admissible l E o ((inputReduction l E X).obj K))
      (ht : t.admissible l E o ((inputReduction l E X).obj K)),
    (coefficientSequenceLimit l E W.left).map s ≫
      (comparison t gt).hom.app ⟨K, hK, ht⟩ =
    (comparison e ge).hom.app ⟨K, hK, he⟩ ≫ r := by
  induction h with
  | @basic W e t s r hb hi =>
    intro ge gt he ht
    exact integralBasicGeneratorSquare l E D hl o a comparison laws e t ge gt
      ⟨K, hK, he⟩ ⟨hK, ht⟩ s r hb hi
  | identity e =>
    intro ge gt he ht
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | @comp W e t v s₁ s₂ r₁ r₂ gm hm h₁ h₂ ih₁ ih₂ =>
    intro ge gv he hv
    rw [Functor.map_comp, Category.assoc, ih₂ gm gv hm hv,
      ← Category.assoc, ih₁ ge gm he hm, Category.assoc]
  | @pull U V f e t s r h ih =>
    intro ge gt he ht
    let L := coefficientSequenceLimit l E V.left
    let R := (calculus l E V.left).reduction
    let F := pull l E f.left ⋙ coefficientSequenceLimit l E U.left
    let B := integralDerivedPullback l E f.left
    let M := e.systemObj l E o ((inputReduction l E X).obj K)
    let N := t.systemObj l E o ((inputReduction l E X).obj K)
    have hM := e.admissibleGood l E o _ he.2
    have : IsIso ((calculus l E V.left).adjunction.counit.app M) :=
      ((purNormalizedReconstructionOfScheme l E V.left (calculus l E V.left)).1 M hM.1).2
    have hc := ih ge.2.2.2.2.2 gt.2.2.2.2.2 he.2 ht.2
    exact normalized_square (L ⋙ R) F (L ⋙ B)
      (calculus l E V.left).adjunction.counit
      (Functor.whiskerLeft L (pullbackTensorIntegralPullbackModel l E f.left).inv)
      s (B.map r) _ _ _ _
      (laws.pull f e ge.2.2.2.2.2 ge ⟨K, hK, he⟩)
      (laws.pull f t gt.2.2.2.2.2 gt ⟨K, hK, ht⟩)
      (by simpa only [Functor.comp_map, Functor.map_comp] using congrArg B.map hc)
  | @push U V f hf e t s r h ih =>
    intro ge gt he ht
    rw [laws.push f hf t gt.2.2 gt ⟨K, hK, ht⟩,
      laws.push f hf e ge.2.2 ge ⟨K, hK, he⟩]
    exact natural_square _ _ (ringedPush l E f.left)
      (a.realizationModel.push l E f.left).hom s r _ _
      (ih ge.2.2 gt.2.2 he.2 ht.2)
  | @shriek U V f hf hq e t s r h ih =>
    intro ge gt he ht
    let := hf
    rw [laws.shriek f e ge.2.2 ge ⟨K, hK, he⟩,
      laws.shriek f t gt.2.2 gt ⟨K, hK, ht⟩]
    have hn := integralOpenRealizationNaturality l E o a f.left hq
      (e.systemObj l E o ((inputReduction l E X).obj K))
      (t.systemObj l E o ((inputReduction l E X).obj K))
      (e.admissibleGood l E o _ he.2) (t.admissibleGood l E o _ ht.2)
      he.1 ht.1 s
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
      ih ge.2.2 gt.2.2 he.2 ht.2, Functor.map_comp, Category.assoc]
  | @compactSupport U V f cf e t s r h ih =>
    intro ge gt he ht
    rw [laws.supportRecursion f cf e ge.2.2.2.2.2 ge ⟨K, hK, he⟩,
      laws.supportRecursion f cf t gt.2.2.2.2.2 gt ⟨K, hK, ht⟩]
    have hn := integralOpenRealizationNaturality l E o a cf.i
      (compactOpenQuasiCompact cf ge.2.2.2.2.1)
      (e.systemObj l E o ((inputReduction l E X).obj K))
      (t.systemObj l E o ((inputReduction l E X).obj K))
      (e.admissibleGood l E o _ he.2.1) (t.admissibleGood l E o _ ht.2.1)
      he.2.2 ht.2.2 s
    have ho : (coefficientSequenceLimit l E cf.Z).map
        ((Operations.shriek l E o cf.i).map s) ≫
        ((a.openRealization cf.i (compactOpenQuasiCompact cf ge.2.2.2.2.1) _
          (t.admissibleGood l E o _ ht.2.1) ht.2.2).hom ≫
          (ringedOpen l E cf.i).map
            ((comparison t gt.2.2.2.2.2).hom.app ⟨K, hK, ht.2.1⟩)) =
      ((a.openRealization cf.i (compactOpenQuasiCompact cf ge.2.2.2.2.1) _
          (e.admissibleGood l E o _ he.2.1) he.2.2).hom ≫
          (ringedOpen l E cf.i).map
            ((comparison e ge.2.2.2.2.2).hom.app ⟨K, hK, he.2.1⟩)) ≫
        (ringedOpen l E cf.i).map r := by
      rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
        ih ge.2.2.2.2.2 gt.2.2.2.2.2 he.2.1 ht.2.1,
        Functor.map_comp, Category.assoc]
    exact natural_square _ _ (ringedPush l E cf.g)
      (a.realizationModel.push l E cf.g).hom _ _ _ _ ho
  | @tensor W e t v z s₁ s₂ r₁ r₂ h₁ h₂ ih₁ ih₂ =>
    intro ge gt he ht
    let L := coefficientSequenceLimit l E W.left
    let R := (calculus l E W.left).reduction
    let F := (calculus l E W.left).systemClosed.tensor ⋙ L
    let B := integralCompletedTensor l E W.left
    let M := e.systemObj l E o ((inputReduction l E X).obj K)
    let N := v.systemObj l E o ((inputReduction l E X).obj K)
    have hM := e.admissibleGood l E o _ he.2.1
    have hN := v.admissibleGood l E o _ he.2.2
    have : IsIso ((calculus l E W.left).adjunction.counit.app M) :=
      ((purNormalizedReconstructionOfScheme l E W.left (calculus l E W.left)).1 M hM.1).2
    have : IsIso ((calculus l E W.left).adjunction.counit.app N) :=
      ((purNormalizedReconstructionOfScheme l E W.left (calculus l E W.left)).1 N hN.1).2
    have : IsIso (((calculus l E W.left).adjunction.counit.prod
        (calculus l E W.left).adjunction.counit).app (M, N)) := by
      exact (Iso.prod (asIso ((calculus l E W.left).adjunction.counit.app M))
        (asIso ((calculus l E W.left).adjunction.counit.app N))).isIso_hom
    have hc₁ := ih₁ ge.2.2.1 gt.2.2.1 he.2.1 ht.2.1
    have hc₂ := ih₂ ge.2.2.2 gt.2.2.2 he.2.2 ht.2.2
    exact normalized_square ((L ⋙ R).prod (L ⋙ R)) F (L.prod L ⋙ B)
      ((calculus l E W.left).adjunction.counit.prod
        (calculus l E W.left).adjunction.counit)
      (Functor.whiskerLeft (L.prod L) (pullbackTensorIntegralTensorModel l E W.left).inv)
      (Prod.mkHom s₁ s₂) (B.map (Prod.mkHom r₁ r₂)) _ _ _ _
      (laws.tensor e v ge.2.2.1 ge.2.2.2 ge ⟨K, hK, he⟩)
      (laws.tensor t z gt.2.2.1 gt.2.2.2 gt ⟨K, hK, ht⟩)
      (by
        dsimp only [Functor.comp_map, Functor.prod_map]
        change B.map _ ≫ B.map _ = B.map _ ≫ B.map _
        simpa only [← B.map_comp, prod_comp] using
          congrArg B.map (show
            Prod.mkHom ((L.map s₁) ≫ (comparison t gt.2.2.1).hom.app ⟨K, hK, ht.2.1⟩)
                ((L.map s₂) ≫ (comparison z gt.2.2.2).hom.app ⟨K, hK, ht.2.2⟩) =
              Prod.mkHom ((comparison e ge.2.2.1).hom.app ⟨K, hK, he.2.1⟩ ≫ r₁)
                ((comparison v ge.2.2.2).hom.app ⟨K, hK, he.2.2⟩ ≫ r₂) from
            Prod.ext hc₁ hc₂))

/-- The independently fixed canonical arrows intertwine the recursive realizations.
This asserts the realization equation only; neither finite scalar projections nor
invertibility of the ordinary-to-completed expression map is asserted here.

Source: blueprint fix-prop-coherence, coefficient-comparison and inherited-equations
sentences; generator/context step of lem-sf-integral-expression-coefficient-squares.
(blueprint: lem-sf-integral-canonical-realization-square).

Proof: first use the primitive transpose formulas to identify the recursive coefficient
maps with reduction of inverse realization followed by the actual counit. For a basic
pair, apply generatorReductionCoherence on its finite word, using the completion
transport to pass from the ordinary ringed arrow to the completed arrow. Pullback
composition and tensor reassociation use their representative normalizations. Exchange
and projection are the displayed adjunction mates, and their composite cases follow
by the ringed exchange/tensor coherence equation. The proper/open arrow is determined
by its lambda adjunct, so the normalized bridge identifies the two independently
specified maps. Expand compact-support generators into the fixed open/proper word.
Transpose the resulting whole-system equation under reduction/limit. Induct on the
CanonicalPair derivation: identity and composition use functoriality; pull and tensor
use the recursion equations after cancelling the invertible images of the actual
counits; proper image uses naturality of the proper comparison. Open extension uses
openNormalization, counit naturality and the invertible reconstruction unit, which
make its prescribed comparison natural on the good domain. Compact support is the
composition of those open and proper steps. Tensor applies the two child squares
in their respective slots, including repeated inputs. All intermediate domains are
supplied by the derivation and the expression domains. No evaluation faithfulness
is used, and zero inputs and empty opens are handled by the same identities. -/
theorem integralCanonicalRealizationSquare (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (r : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.evaluate (integralInterpretation l E)).obj K.obj)
    (h : CanonicalPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e t s r) :
    (coefficientSequenceLimit l E W.left).map s ≫
      (comparison t gt).hom.app ⟨K.obj, ht⟩ =
    (comparison e ge).hom.app K ≫ r := by
  exact canonical_square l E D hl o a comparison laws K.obj K.property.1 h
    ge gt K.property.2 ht.2

end WeilConjectures.IntegralSystemRealization
