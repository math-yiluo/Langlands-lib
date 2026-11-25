/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import all WeilConjectures.SmoothPurity.Common.CommonStageTensorRightUnitorNaturality
import all WeilConjectures.SmoothPurity.Rational.RationalPullbackTensorAssociatorNaturality
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence

/-! # Tensor constraints for a normalized reindexing family

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4 and 0941
(blueprint: lem-pod-reindexing-tensor-family-tensor-constraints).

This statement isolates the strict tensor-generator calculation from the identity
and composition construction. It is used only after those two comparisons have been
fixed, so its conclusion is strictly smaller than the parent family-coherence
assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

universe u
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem completionUnitIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso ((podOrdinaryToCompleted l E g D).app K.obj) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let Δ : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card],
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ Δ.p := by change l ≠ p; omega
  have hK : IntegralOnSlice.IsComplete l E Y none K.obj :=
    ⟨Δ, hlp, (sfDerivedComplete_iff_legacy l E Y Δ hlp K.obj).mp K.property.1⟩
  have : IsIso ((podReindexCalculus l E Y).adjunction.unit.app K.obj) :=
    hD.2.2.2.2.2.1 K.obj hK
  dsimp only [podOrdinaryToCompleted, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app]
  infer_instance

private theorem transportAssociativity
    {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D) (e : F ≅ G)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : U ⋙ G ≅ G.prod G ⋙ V)
    (α : ∀ M N P, U.obj (U.obj (M, N), P) ≅ U.obj (M, U.obj (N, P)))
    (β : ∀ M N P, V.obj (V.obj (M, N), P) ≅ V.obj (M, V.obj (N, P)))
    (hn : ∀ {M N P M' N' P'} (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P'),
      V.map (Prod.mkHom (V.map (Prod.mkHom a b)) c) ≫ (β M' N' P').hom =
        (β M N P).hom ≫ V.map (Prod.mkHom a (V.map (Prod.mkHom b c))))
    (hμ : ∀ M N, (μ M N).hom ≫ V.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (U.obj (M, N)) ≫ ν.hom.app (M, N))
    (hc : ∀ M N P, G.map (α M N P).hom ≫ ν.hom.app (M, U.obj (N, P)) ≫
      V.map (Prod.mkHom (𝟙 _) (ν.hom.app (N, P))) =
      ν.hom.app (U.obj (M, N), P) ≫
        V.map (Prod.mkHom (ν.hom.app (M, N)) (𝟙 _)) ≫
          (β (G.obj M) (G.obj N) (G.obj P)).hom) (M N P : C) :
    F.map (α M N P).hom ≫ (μ M (U.obj (N, P))).hom ≫
      V.map (Prod.mkHom (𝟙 _) (μ N P).hom) =
      (μ (U.obj (M, N)) P).hom ≫ V.map (Prod.mkHom (μ M N).hom (𝟙 _)) ≫
        (β (F.obj M) (F.obj N) (F.obj P)).hom := by
  apply reduced_associativity (𝟭 C) (𝟭 D) F G U V U V
    (Iso.refl U) (Iso.refl V) e ν μ α β α β hn
  · intro A B C₀
    simp
  · intro A B C₀
    simp
  · intro A B
    simpa using hμ A B
  · exact hc

private theorem transportBraiding
    {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D) (e : F ≅ G)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, G.obj (U.obj (M, N)) ≅ V.obj (G.obj M, G.obj N))
    (α : ∀ M N, U.obj (M, N) ≅ U.obj (N, M))
    (β : ∀ M N, V.obj (M, N) ≅ V.obj (N, M))
    (hn : ∀ {M N M' N'} (a : M ⟶ M') (b : N ⟶ N'),
      V.map (Prod.mkHom a b) ≫ (β M' N').hom =
        (β M N).hom ≫ V.map (Prod.mkHom b a))
    (hμ : ∀ M N, (μ M N).hom ≫ V.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (U.obj (M, N)) ≫ (ν M N).hom)
    (hc : ∀ M N, G.map (α M N).hom ≫ (ν N M).hom =
      (ν M N).hom ≫ (β (G.obj M) (G.obj N)).hom) (M N : C) :
    F.map (α M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (β (F.obj M) (F.obj N)).hom := by
  let b : V ≅ CategoryTheory.Prod.swap D D ⋙ V :=
    NatIso.ofComponents (fun MN ↦ β MN.1 MN.2) (fun a ↦ hn a.1 a.2)
  apply reduced_braiding (𝟭 C) (𝟭 D) F G U V U V
    (fun _ _ ↦ Iso.refl _) (fun _ _ ↦ Iso.refl _) e μ ν α β α b
  · intro A B
    simp
  · intro A B
    simp [b]
  · intro A B
    simpa using hμ A B
  · exact hc

private theorem transportLeftUnitor
    {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D) (e : F ≅ G)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, G.obj (U.obj (M, N)) ≅ V.obj (G.obj M, G.obj N))
    (I : C) (J : D) (ε : G.obj I ≅ J)
    (α : ∀ M, U.obj (I, M) ≅ M) (β : ∀ M, V.obj (J, M) ≅ M)
    (hn : ∀ {M N} (a : M ⟶ N),
      V.map (Prod.mkHom (𝟙 J) a) ≫ (β N).hom = (β M).hom ≫ a)
    (hμ : ∀ M N, (μ M N).hom ≫ V.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (U.obj (M, N)) ≫ (ν M N).hom)
    (hc : ∀ M, (ν I M).hom ≫ V.map (Prod.mkHom ε.hom (𝟙 _)) ≫
      (β (G.obj M)).hom = G.map (α M).hom) (M : C) :
    (μ I M).hom ≫ V.map (Prod.mkHom ((e.app I).hom ≫ ε.hom) (𝟙 _)) ≫
      (β (F.obj M)).hom = F.map (α M).hom := by
  apply (cancel_mono (e.hom.app M)).1
  simp only [Category.assoc, Iso.app_hom]
  rw [← hn]
  have hs : V.map (Prod.mkHom (e.hom.app I ≫ ε.hom) (𝟙 (F.obj M))) ≫
      V.map (Prod.mkHom (𝟙 J) (e.hom.app M)) =
    V.map (Prod.mkHom (e.hom.app I) (e.hom.app M)) ≫
      V.map (Prod.mkHom ε.hom (𝟙 (G.obj M))) := by
    simp only [← V.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  rw [← Category.assoc (V.map _), hs]
  simp only [Category.assoc]
  rw [reassoc_of% (hμ I M)]
  rw [hc]
  exact (e.hom.naturality (α M).hom).symm

private theorem transportRightUnitor
    {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D) (e : F ≅ G)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, G.obj (U.obj (M, N)) ≅ V.obj (G.obj M, G.obj N))
    (I : C) (J : D) (ε : G.obj I ≅ J)
    (α : ∀ M, U.obj (M, I) ≅ M) (β : ∀ M, V.obj (M, J) ≅ M)
    (hn : ∀ {M N} (a : M ⟶ N),
      V.map (Prod.mkHom a (𝟙 J)) ≫ (β N).hom = (β M).hom ≫ a)
    (hμ : ∀ M N, (μ M N).hom ≫ V.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (U.obj (M, N)) ≫ (ν M N).hom)
    (hc : ∀ M, (ν M I).hom ≫ V.map (Prod.mkHom (𝟙 _) ε.hom) ≫
      (β (G.obj M)).hom = G.map (α M).hom) (M : C) :
    (μ M I).hom ≫ V.map (Prod.mkHom (𝟙 _) ((e.app I).hom ≫ ε.hom)) ≫
      (β (F.obj M)).hom = F.map (α M).hom := by
  apply (cancel_mono (e.hom.app M)).1
  simp only [Category.assoc, Iso.app_hom]
  rw [← hn]
  have hs : V.map (Prod.mkHom (𝟙 (F.obj M)) (e.hom.app I ≫ ε.hom)) ≫
      V.map (Prod.mkHom (e.hom.app M) (𝟙 J)) =
    V.map (Prod.mkHom (e.hom.app M) (e.hom.app I)) ≫
      V.map (Prod.mkHom (𝟙 (G.obj M)) ε.hom) := by
    simp only [← V.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  rw [← Category.assoc (V.map _), hs]
  simp only [Category.assoc]
  rw [reassoc_of% (hμ M I)]
  rw [hc]
  exact (e.hom.naturality (α M).hom).symm

private theorem associatorNatural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N P M' N' P' : sfIntegralConstructibleCategory l E W}
    (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P') :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralTensor l E W).map (Prod.mkHom a b)) c) ≫
        (pullbackTensorIntegralAssociator l E W M' N' P').hom =
      (pullbackTensorIntegralAssociator l E W M N P).hom ≫
        (constructibleIntegralTensor l E W).map
          (Prod.mkHom a ((constructibleIntegralTensor l E W).map (Prod.mkHom b c))) := by
  have := (coherentReduction_fullyFaithful l E W).2
  apply faithful_associator_naturality (coherentReduction l E W)
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (reduction_tensor l E W) (pullbackTensorIntegralAssociator l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.associator
  · intro M N P M' N' P' f g h
    exact @MonoidalCategory.associator_naturality _ _
      (pullbackTensorCalculus l E W).systemClosed.monoidal _ _ _ _ _ _ f g h
  · intro M N P
    exact (pullbackTensorIntegralAssociator_existsUnique l E W M N P).exists.choose_spec

private theorem leftUnitorNatural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfIntegralConstructibleCategory l E W} (a : M ⟶ N) :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom (𝟙 (pullbackTensorIntegralUnit l E W)) a) ≫
        (pullbackTensorIntegralLeftUnitor l E W N).hom =
      (pullbackTensorIntegralLeftUnitor l E W M).hom ≫ a := by
  let Q := coherentReduction l E W
  let S := (pullbackTensorCalculus l E W).systemClosed
  let b := reduction_tensor l E W
  let I := pullbackTensorIntegralUnit l E W
  let e : Q.obj I ≅ S.monoidal.tensorUnit :=
    pullbackTensorIntegralUnitReduction l E W
  have := (coherentReduction_fullyFaithful l E W).2
  have hi (M : sfIntegralConstructibleCategory l E W) :
      Q.map (pullbackTensorIntegralLeftUnitor l E W M).hom =
        b.hom.app (I, M) ≫ S.tensor.map (Prod.mkHom e.hom (𝟙 _)) ≫
          (S.monoidal.leftUnitor (Q.obj M)).hom :=
    (pullbackTensorIntegralLeftUnitor_existsUnique l E W M).exists.choose_spec
  apply Q.map_injective
  simp only [Functor.map_comp, hi, Category.assoc]
  have hb := b.hom.naturality (Prod.mkHom (𝟙 I) a)
  change Q.map ((constructibleIntegralTensor l E W).map (Prod.mkHom (𝟙 I) a)) ≫
    b.hom.app (I, N) = b.hom.app (I, M) ≫
      S.tensor.map (Prod.mkHom (Q.map (𝟙 I)) (Q.map a)) at hb
  rw [← Category.assoc, hb, Q.map_id]
  simp only [Category.assoc]
  have hs : S.tensor.map (Prod.mkHom (𝟙 (Q.obj I)) (Q.map a)) ≫
      S.tensor.map (Prod.mkHom e.hom (𝟙 (Q.obj N))) =
    S.tensor.map (Prod.mkHom e.hom (𝟙 (Q.obj M))) ≫
      S.tensor.map (Prod.mkHom (𝟙 _) (Q.map a)) := by
    simp only [← S.tensor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  erw [reassoc_of% hs]
  let := S.monoidal
  have hn := MonoidalCategory.leftUnitor_naturality (Q.map a)
  simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.id_tensorHom, Category.assoc] using
    congrArg (fun k ↦ b.hom.app (I, M) ≫
      S.tensor.map (Prod.mkHom e.hom (𝟙 (Q.obj M))) ≫ k) hn

/--
For a fixed completion/tensor family and fixed section-normalized identity and
composition comparisons, the completed tensor maps satisfy associativity, signed
braiding and both unitors. On homogeneous strict generators the two associator
paths are the same map, the two braiding paths carry the same Koszul sign, and the
coefficient unit is preserved. Tensor-model descent and naturality extend these
equalities to all constructible objects. The zero and empty-scheme cases are
included by the same generator formulas.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: lem-pod-reindexing-tensor-family-tensor-constraints).
-/
theorem podReindexingTensorFamilyTensorConstraints
    (completion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)], PodCompletionReindex l E f)
    (tensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex l E f (completion f))
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (completion f) (tensor f))
    (identity : ∀ W : Scheme.{u}, isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _)
    (composition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f], isoReductionIntegralInverse l E (h ≫ f) ≅
        isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h) :
    let A : PodReindexFamily l E := ⟨completion, tensor, identity, composition⟩
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)], A.TensorConstraints l E f := by
  intro A X Y f _ _ _
  let F := A.constructible l E f
  let G := constructibleIntegralPullback l E f
  let U := constructibleIntegralTensor l E Y
  let V := constructibleIntegralTensor l E X
  let κ := podOrdinaryToCompleted l E f (completion f)
  have hκ (M : sfIntegralConstructibleCategory l E Y) : IsIso (κ.app M.obj) :=
    completionUnitIso l E f (completion f) (hcompletion f) M
  let e : F ≅ G := NatIso.ofComponents
    (fun M ↦ by
      let c := @asIso _ _ _ _ (κ.app M.obj) (hκ M)
      exact (sfIntegralConstructible l E X).isoMk c) (by
      intro M N a
      apply ObjectProperty.hom_ext
      exact κ.naturality a.hom)
  let μ (M N : sfIntegralConstructibleCategory l E Y) :
      F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N) :=
    (sfIntegralConstructible l E X).isoMk ((tensor f).tensor M N)
  let ν : U ⋙ G ≅ G.prod G ⋙ V := NatIso.ofComponents
    (fun MN ↦ canonicalIntegralPullbackTensor l E f MN.1 MN.2) (by
      intro MN PQ a
      exact integralComparison_natural l E f a.1 a.2)
  have hμ (M N : sfIntegralConstructibleCategory l E Y) :
      (μ M N).hom ≫ V.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
        e.hom.app (U.obj (M, N)) ≫ ν.hom.app (M, N) := by
    apply ObjectProperty.hom_ext
    change ((tensor f).tensor M N).hom ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom (κ.app M.obj) (κ.app N.obj)) =
      κ.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        (canonicalIntegralPullbackTensor l E f M N).hom.hom
    exact ((htensor f).2.2.2.2.2 M N).symm
  refine ⟨?_, ?_, ?_⟩
  · intro M N P
    have h := transportAssociativity F G U V e μ ν
      (pullbackTensorIntegralAssociator l E Y) (pullbackTensorIntegralAssociator l E X)
      (fun a b c ↦ associatorNatural l E X a b c) hμ
      (canonicalIntegralPullbackTensor_associative_spec l E f) M N P
    exact congrArg (fun k ↦ k.hom) h
  · intro M N
    have h := transportBraiding F G U V e μ (fun M N ↦ ν.app (M, N))
      (pullbackTensorIntegralBraiding l E Y) (pullbackTensorIntegralBraiding l E X)
      (fun a b ↦ integralBraiding_natural l E X _ _ _ _ a b) hμ
      (canonicalIntegralPullbackTensor_braiding_spec l E f) M N
    exact congrArg (fun k ↦ k.hom) h
  · obtain ⟨ε, hε, _⟩ := pullbackTensorIntegralUnitCoherence l E f
    refine ⟨((sfIntegralConstructible l E X).ι.mapIso
      (e.app (pullbackTensorIntegralUnit l E Y) ≪≫ ε)), ?_⟩
    intro M
    constructor
    · have h := transportLeftUnitor F G U V e μ (fun M N ↦ ν.app (M, N))
        (pullbackTensorIntegralUnit l E Y) (pullbackTensorIntegralUnit l E X) ε
        (pullbackTensorIntegralLeftUnitor l E Y) (pullbackTensorIntegralLeftUnitor l E X)
        (fun a ↦ leftUnitorNatural l E X a) hμ (fun M ↦ (hε M).1) M
      exact congrArg (fun k ↦ k.hom) h
    · have h := transportRightUnitor F G U V e μ (fun M N ↦ ν.app (M, N))
        (pullbackTensorIntegralUnit l E Y) (pullbackTensorIntegralUnit l E X) ε
        (pullbackTensorIntegralRightUnitor l E Y) (pullbackTensorIntegralRightUnitor l E X)
        (fun a ↦ integral_naturality l E X a) hμ (fun M ↦ (hε M).2) M
      exact congrArg (fun k ↦ k.hom) h

end WeilConjectures
