/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensorAux2
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensorAux4

/-! # The strict reduction/reindexing tensor equation

Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03EL, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none
set_option quotPrecheck false in
set_option hygiene false in
local notation "T[" W "]" => PodReindexingCoherence.total l E W none
set_option quotPrecheck false in
set_option hygiene false in
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

/-- The inverse-image unit as a section at the pulled-back object. -/
private def inverseImageUnitSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (V : ℕ × Y.ProEt) (s : M.val.obj (op V)) :
    ((integralComparisonSequencePullback l E g).obj M).val.obj
      (op ((pullbackTensorSequenceBase g).obj V)) :=
  ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
    M).val.app (op V) s

/-- The inverse-image transpose evaluates a map on the unit section.
Source: Stacks 03D2. -/
theorem inverseImage_homEquiv_apply {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (N : coefficientSequenceModules l E X)
    (f : (integralComparisonSequencePullback l E g).obj M ⟶ N) (V : ℕ × Y.ProEt)
    (s : M.val.obj (op V)) :
    (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).homEquiv M N
      f).val.app (op V)) s =
      f.val.app (op ((pullbackTensorSequenceBase g).obj V))
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          M).val.app (op V) s) := by
  erw [Adjunction.homEquiv_unit]
  rfl

/-- Restriction along an isomorphism of the pro-etale coordinate is injective.
Source: Stacks 0941. -/
theorem sequence_restrict_injective {X : Scheme.{u}} (N : coefficientSequenceModules l E X)
    (n : ℕ) {U V : X.ProEt} (c : U ⟶ V) [IsIso c] :
    Function.Injective (N.val.map (CategoryTheory.Prod.mkHom (𝟙 n) c).op) := by
  have : IsIso (CategoryTheory.Prod.mkHom (𝟙 n) c) :=
    (isIso_prod_iff ℕ X.ProEt).2 ⟨inferInstance, inferInstance⟩
  exact (ConcreteCategory.bijective_of_isIso
    (N.val.presheaf.map (CategoryTheory.Prod.mkHom (𝟙 n) c).op)).1

set_option backward.isDefEq.respectTransparency false in
/-- The comma arrow of an isomorphism of schemes is an isomorphism.
Source: Stacks 09A5. -/
theorem proEtaleIsoCommaArrow_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (U : X.ProEt) :
    IsIso (proEtaleIsoCommaArrow g U) := by
  have : (MorphismProperty.Over.map ⊤
      (inferInstance : AlgebraicGeometry.WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  exact inferInstanceAs (IsIso ((MorphismProperty.Over.mapPullbackAdj
    @AlgebraicGeometry.WeaklyEtale ⊤ g
    (inferInstance : AlgebraicGeometry.WeaklyEtale g) trivial).unit.app U))

private theorem inverseImage_reduction_total_hom_ext {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (P Q : CochainComplex (scalarReductionSource l E Y) ℤ) (k : ℤ)
    {N : coefficientSequenceModules l E X}
    {f₁ f₂ : (integralComparisonSequencePullback l E g).obj
      ((pullbackTensorOrdinaryReduction l E Y).obj (((T[Y]).obj (P, Q)).X k)) ⟶ N}
    (h : ∀ (n : ℕ) (p q : ℤ) (hpq : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (Q.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      let V := (n, (proEtaleIsoPostcompose g).obj U)
      let s := inverseImageUnitSection l E g
        ((pullbackTensorOrdinaryReduction l E Y).obj (((T[Y]).obj (P, Q)).X k)) V
          (reducedUnitSection l E Y n _ (op V.2)
              (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
                (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq (op V.2) x y))
      N.val.map (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (f₁.val.app (op ((pullbackTensorSequenceBase g).obj V)) s) =
        N.val.map (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (f₂.val.app (op ((pullbackTensorSequenceBase g).obj V)) s)) : f₁ = f₂ := by
  apply ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).homEquiv
    _ _).injective
  apply reduction_total_hom_ext_postcompose l E g P Q k
  intro n p q hpq U x y
  have := proEtaleIsoCommaArrow_isIso g U
  refine (inverseImage_homEquiv_apply l E g _ _ _ (n, (proEtaleIsoPostcompose g).obj U) _).trans
    (Eq.trans ?_ (inverseImage_homEquiv_apply l E g _ _ _ _ _).symm)
  apply sequence_restrict_injective l E _ n (proEtaleIsoCommaArrow g U)
  exact h n p q hpq U x y

private theorem generators_unitSection {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (β : (I[g]).obj ((R[Y]).obj P) ≅ (R[X]).obj ((F[g]).obj P))
    (hβ : Generators l E g P β) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((β.hom.f i).val.app (op (n, U)))
      (((integralComparisonSequencePullback l E g).obj
          ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))).val.map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
        (inverseImageUnitSection l E g
          ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))
          (n, (proEtaleIsoPostcompose g).obj U)
          (reducedUnitSection l E Y n (P.X i)
            (op ((proEtaleIsoPostcompose g).obj U)) x))) =
      reducedUnitSection l E X n (((F[g]).obj P).X i) (op U) x := by
  exact (hβ n i U 1 x).trans (congrArg (fun a ↦
    ((pullbackTensorReductionEvaluation l E X n).hom.app (((F[g]).obj P).X i)).val.app (op U)
      (unrestrictedIntegralTensorSection l E X n _ (op U) a x)) (map_one _))

private theorem reducedUnitSection_map (W : Scheme.{u}) (n : ℕ)
    {M M' : integralTowerModules l E W} (φ : M ⟶ M') (V : W.ProEt) (z : M.val.obj (op V)) :
    ((pullbackTensorOrdinaryReduction l E W).map φ).val.app (op (n, V))
      (reducedUnitSection l E W n M (op V) z) =
      reducedUnitSection l E W n M' (op V) (φ.val.app (op V) z) :=
  reduction_map_unitSection l E W n φ V z

-- The generator calculation passes through several transported comparison maps.
/-- Scalar-generator normalization implies the tensor equation before localization.
There are no derived-category maps, adjunction mates, or completion data in this
assertion. The three beta maps are tested independently by their unary formulas.
Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03EL, 07A4, 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).

Proof: apply the sequence inverse-image adjunction to the proposed equality.
Check each degree and each total summand on scalar pure tensors. The finite
component formula for tensorReductionStrictMap sends b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The systemChain unit formula sends a tensor
to the tensor of its two inverse-image units. The three Generators hypotheses
send the scalar to its reindexed scalar and leave x and y as the same sections
at the postcomposed object. Finally hPure sends x tensor y to that same tensor
at the reindexed object. Both composites therefore give the same two reduced
factors, with reindex(b) on the first and 1 on the second. The scalar balancing
relations, sheafification universal property and total-summand injections extend
the equality to every section and every degree. These are equalities of maps on
the sequence site, so they already contain every horizontal quotient transition.
No faithfulness of finite derived evaluations is invoked. The equations still
hold for zero factors and the empty site. -/
theorem strict_tensor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P Q : CochainComplex (scalarReductionSource l E Y) ℤ)
    (t : (F[g]).obj ((T[Y]).obj (P, Q)) ≅
      (T[X]).obj ((F[g]).obj P, (F[g]).obj Q))
    (hPure : ∀ (p q k : ℤ) (hk : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (Q.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((t.hom.f k).val.app (op U))
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
          (podReindexingRing l E Y none) P Q p q k hk
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X none) ((F[g]).obj P) ((F[g]).obj Q)
        p q k hk (op U) x y)
    (βP : (I[g]).obj ((R[Y]).obj P) ≅ (R[X]).obj ((F[g]).obj P))
    (βQ : (I[g]).obj ((R[Y]).obj Q) ≅ (R[X]).obj ((F[g]).obj Q))
    (βT : (I[g]).obj ((R[Y]).obj ((T[Y]).obj (P, Q))) ≅
      (R[X]).obj ((F[g]).obj ((T[Y]).obj (P, Q))))
    (hβP : Generators l E g P βP) (hβQ : Generators l E g Q βQ)
    (hβT : Generators l E g ((T[Y]).obj (P, Q)) βT) :
    (I[g]).map (tensorReductionStrictMap l E Y P Q) ≫
        (systemChain l E g).hom.app ((R[Y]).obj P, (R[Y]).obj Q) ≫
        (S[X]).map (Prod.mkHom βP.hom βQ.hom) =
      βT.hom ≫ (R[X]).map t.hom ≫
        tensorReductionStrictMap l E X ((F[g]).obj P) ((F[g]).obj Q) := by
  apply HomologicalComplex.hom_ext
  intro k
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  apply inverseImage_reduction_total_hom_ext l E g P Q k
  intro n p q hpq U x y
  simp only [sheafOfModules_comp_apply]
  let V := (n, (proEtaleIsoPostcompose g).obj U)
  let V' := (pullbackTensorSequenceBase g).obj V
  let c := (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
  let res := (((S[X]).obj ((R[X]).obj ((F[g]).obj P),
    (R[X]).obj ((F[g]).obj Q))).X k).val.map c
  let m := (((S[X]).map (Prod.mkHom βP.hom βQ.hom)).f k).val.app (op V')
  let a := (((systemChain l E g).hom.app ((R[Y]).obj P, (R[Y]).obj Q)).f k).val.app (op V')
  let x₀ := reducedUnitSection l E Y n (P.X p) (op V.2) x
  let y₀ := reducedUnitSection l E Y n (Q.X q) (op V.2) y
  let uP := inverseImageUnitSection l E g (((R[Y]).obj P).X p) V x₀
  let uQ := inverseImageUnitSection l E g (((R[Y]).obj Q).X q) V y₀
  have e1 := inverseImage_map_unit l E g ((tensorReductionStrictMap l E Y P Q).f k) V
    (reducedUnitSection l E Y n _ (op V.2)
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
        (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq (op V.2) x y))
  have e2 := strictMap_reducedUnit_generator l E Y P Q n p q k hpq V.2 x y
  have e12 := e1.trans (congrArg
    (inverseImageUnitSection l E g (((S[Y]).obj ((R[Y]).obj P, (R[Y]).obj Q)).X k) V) e2)
  have hL1 := congrArg (fun z ↦ res (m (a z))) e12
  have e3 := systemChain_generator l E g ((R[Y]).obj P) ((R[Y]).obj Q)
    p q k hpq V x₀ y₀
  have hL2 := congrArg (fun z ↦ res (m z)) e3
  have e4 := coefficientTotalTensor_map_tensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    βP.hom βQ.hom p q k hpq (op V') uP uQ
  have hL3 := congrArg res e4
  have hL4 := coefficientTensorGenerator_restrict (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) ((R[X]).obj ((F[g]).obj P))
    ((R[X]).obj ((F[g]).obj Q)) p q k hpq c
    ((βP.hom.f p).val.app (op V') uP) ((βQ.hom.f q).val.app (op V') uQ)
  have rP := (PresheafOfModules.naturality_apply (βP.hom.f p).val c uP).symm.trans
    (generators_unitSection l E g P βP hβP n p U x)
  have rQ := (PresheafOfModules.naturality_apply (βQ.hom.f q).val c uQ).symm.trans
    (generators_unitSection l E g Q βQ hβQ n q U y)
  have hL5 := congrArg₂ (coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    ((R[X]).obj ((F[g]).obj P)) ((R[X]).obj ((F[g]).obj Q)) p q k hpq (op (n, U)))
    rP rQ
  -- Normalize the unit before composing the pointwise equations from left to right.
  dsimp only [a, V', inverseImageUnitSection] at hL1 hL2
  have hL12 := hL1.trans hL2
  have hL123 := hL12.trans hL3
  have hL1234 := hL123.trans hL4
  have hL := hL1234.trans hL5
  have rT := generators_unitSection l E g ((T[Y]).obj (P, Q)) βT hβT n k U
    (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq (op V.2) x y)
  let z := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq (op V.2) x y
  let s := inverseImageUnitSection l E g ((pullbackTensorOrdinaryReduction l E Y).obj
    (((T[Y]).obj (P, Q)).X k)) V (reducedUnitSection l E Y n _ (op V.2) z)
  have hNat := PresheafOfModules.naturality_apply
    (βT.hom.f k ≫ ((R[X]).map t.hom).f k ≫
      (tensorReductionStrictMap l E X ((F[g]).obj P) ((F[g]).obj Q)).f k).val c s
  have r3 := reducedUnitSection_map l E X n (t.hom.f k) U z
  have r4 := hPure p q k hpq U x y
  have r5 := strictMap_reducedUnit_generator l E X ((F[g]).obj P) ((F[g]).obj Q)
    n p q k hpq U x y
  have hR1 := congrArg (fun z ↦
    ((tensorReductionStrictMap l E X ((F[g]).obj P) ((F[g]).obj Q)).f k).val.app (op (n, U))
      ((((R[X]).map t.hom).f k).val.app (op (n, U)) z)) rT
  have hR2 := congrArg
    (((tensorReductionStrictMap l E X ((F[g]).obj P) ((F[g]).obj Q)).f k).val.app (op (n, U))) r3
  have hR3 := congrArg (fun z ↦
    ((tensorReductionStrictMap l E X ((F[g]).obj P) ((F[g]).obj Q)).f k).val.app (op (n, U))
      (reducedUnitSection l E X n _ (op U) z)) r4
  have hR01 := hNat.symm.trans hR1
  have hR012 := hR01.trans hR2
  have hR0123 := hR012.trans hR3
  have hR := hR0123.trans r5
  -- Compare the formulas in the same presentation as the expanded composites.
  dsimp only [res, m, a, V, V', c, s, z, inverseImageUnitSection] at hL hR ⊢
  simp only [sheafOfModules_comp_apply, Functor.mapHomologicalComplex_map_f] at hR
  exact hL.trans hR.symm

end WeilConjectures.PodReductionRepresentatives
