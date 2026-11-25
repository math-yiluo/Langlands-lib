/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingStrictTensorTowers
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorRoosNormalization

/-! # Completed tensor extension of a normalized completion comparison

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-construction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem tensorInverseGenerators
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (h : PodCompletedTensorReindex.Generators l E g D T) :
    PodCompletedTensorReindex.InverseGenerators l E g D T := by
  intro P Q n p q U x y
  rw [← h P Q n p q U x y]
  exact congrArg (fun f ↦ (((f.app (op n)).f (p + q)).val.app (op U))
    (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
      (op ((proEtaleIsoPostcompose g).obj U)) x y)) (T.tower P Q).hom_inv_id

private theorem ordinaryComparisonIsIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso ((podOrdinaryToCompleted l E g D).app K.obj) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let Δ : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ Δ.p := by change l ≠ p; omega
  have hK : IntegralOnSlice.IsComplete l E Y none K.obj :=
    ⟨Δ, hlp, (sfDerivedComplete_iff_legacy l E Y Δ hlp K.obj).mp K.property.1⟩
  have : IsIso ((podReindexCalculus l E Y).adjunction.unit.app K.obj) :=
    hD.2.2.2.2.2.1 K.obj hK
  dsimp only [podOrdinaryToCompleted, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app]
  infer_instance

private theorem ordinaryConstructible
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (M : sfIntegralConstructibleCategory l E Y) :
    sfIntegralConstructible l E X ((podOrdinaryReindex l E g).obj M.obj) := by
  let := ordinaryComparisonIsIso l E g D hD M
  exact (sfIntegralConstructible l E X).prop_of_iso
    (asIso ((podOrdinaryToCompleted l E g D).app M.obj)).symm
    ((constructibleIntegralPullback l E g).obj M).property

/-- Extend a fixed normalized completion comparison to completed tensor.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-tensor-construction).

Proof: on simultaneous flat-term K-flat P,Q, use the quotient maps in D and the
sectionwise balanced tensor comparison to relabel every (p,q) summand. The two
orders of applying a quotient transition agree on x tensor y, so these maps
assemble into an isomorphism of strict towers. The inverse relabels in reverse.
Both differentials send a generator to dx tensor y + (-1)^p x tensor dy, proving
that these are chain maps. Their naturality follows on the same generators.
Reindexing preserves the common cohomological interval and constructibility of
every finite reduction. The Roos comparison in D and its limit model transport
derived completeness, so it preserves the complete constructible domain.
Apply D.roos followed by the tower isomorphism, and descend along the two K-flat
localizations to define the tensor isomorphism. This gives Model and Naturality.
The finite generator formula is the canonical finite pullback/tensor map.
D.Unit and D.Counit compare its whole-system realization with the specified
completed pullback comparison, proving Canonical before finite evaluation.
These constructions also apply to zero complexes and empty schemes. -/
theorem podReindexingTensorConstruction
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D) :
    ∃ T : PodCompletedTensorReindex l E g D,
      PodCompletedTensorReindex.Laws l E g D T := by
  obtain ⟨τ, hgen, hnat⟩ := podReindexingStrictTensorTowers l E g D hD
  let I := (sfIntegralConstructible l E Y).ι
  let J := (sfIntegralConstructible l E X).ι
  let F := podOrdinaryReindex l E g
  let P := integralDerivedPullback l E g
  let U := constructibleIntegralTensor l E Y
  let V := integralCompletedTensor l E X
  let α : I ⋙ F ≅ I ⋙ P :=
    NatIso.ofComponents (fun M ↦ by
      let := ordinaryComparisonIsIso l E g D hD M
      exact asIso ((podOrdinaryToCompleted l E g D).app M.obj))
      (by intro M N f; exact (podOrdinaryToCompleted l E g D).naturality f.hom)
  let μ : U ⋙ I ⋙ P ≅ ((I ⋙ P).prod (I ⋙ P)) ⋙ V :=
    isoWhiskerRight (integralComparisonIso l E g) J
  let e : U ⋙ I ⋙ F ≅ ((I ⋙ F).prod (I ⋙ F)) ⋙ V :=
    isoWhiskerLeft U α ≪≫ μ ≪≫ (isoWhiskerRight (NatIso.prod α α) V).symm
  let T : PodCompletedTensorReindex l E g D :=
    { constructible := ordinaryConstructible l E g D hD
      tower := τ
      tensor := fun M N ↦ e.app (M,N) }
  have hforward : PodCompletedTensorReindex.Generators l E g D T := hgen
  have htower : PodCompletedTensorReindex.TowerNaturality l E g D T := hnat
  have hderived : PodCompletedTensorReindex.Naturality l E g D T := by
    intro M N M' N' a b
    exact e.hom.naturality (Prod.mkHom a b)
  have hcanonical : PodCompletedTensorReindex.Canonical l E g D T := by
    intro M N
    have hμ : μ.hom.app (M,N) =
        ((canonicalIntegralPullbackTensor l E g M N).hom).hom := by
      exact congrArg (fun z ↦ z.hom.hom) (integralComparisonIso_app l E g M N)
    change _ = (e.app (M,N)).hom ≫ _
    rw [← hμ]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app,
      NatIso.prod_inv, NatTrans.prod]
    change α.hom.app (U.obj (M,N)) ≫ μ.hom.app (M,N) =
      (α.hom.app (U.obj (M,N)) ≫ μ.hom.app (M,N) ≫
        V.map (Prod.mkHom (α.inv.app M) (α.inv.app N))) ≫
          V.map (Prod.mkHom (α.hom.app M) (α.hom.app N))
    have hc : Prod.mkHom (α.inv.app M) (α.inv.app N) ≫
        Prod.mkHom (α.hom.app M) (α.hom.app N) = 𝟙 _ := by
      ext <;> exact α.inv_hom_id_app _
    rw [Category.assoc, Category.assoc, ← V.map_comp, hc]
    erw [CategoryTheory.Functor.map_id]
    simpa only [Category.assoc, CategoryTheory.Functor.comp_obj] using
      (Category.comp_id (α.hom.app (U.obj (M,N)) ≫ μ.hom.app (M,N))).symm
  exact ⟨T, hforward, tensorInverseGenerators l E g D T hforward, htower, hderived,
    podReindexingTensorRoosNormalization l E g D hD T hforward htower hcanonical,
    hcanonical⟩

end WeilConjectures
