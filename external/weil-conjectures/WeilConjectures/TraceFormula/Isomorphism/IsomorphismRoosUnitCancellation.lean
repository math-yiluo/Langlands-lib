/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismMultiplicationConeDescent
public import WeilConjectures.TraceFormula.Supporting.StrictQuotientConeAugmentation
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Cancellation of the specified comparison on a strict quotient cone

Source: blueprint main-20261015, rational Frobenius integral model, proof (2)--(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit scalarReductionDerivedExistence
  unrestrictedTowerUnit
  unrestrictedIntegralTransition inverseImageReductionProduct

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose integralOperationsRoosFunctor integralOperationsRoos
  integralOperationsPullbackComplexFunctor integralOperationsPullbackTowerFunctor
  trfQuotientTowerFunctor unrestrictedIntegralComplexFunctor
  unrestrictedIntegralReductionFunctor scalarReductionExtension scalarReductionExistence
  unrestrictedIntegralReductionExistence

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem lift_map_eq
    {C : Type*} [Category C] {I : Type*} {A B : I → C}
    [HasProduct A] [HasProduct B] {P : C}
    (γ : ∀ i : I, P ⟶ A i) (f : ∀ i : I, A i ⟶ B i)
    (δ : ∀ i : I, P ⟶ B i) (h : ∀ i : I, γ i ≫ f i = δ i) :
    Limits.Pi.lift γ ≫ Limits.Pi.map f = Limits.Pi.lift δ := by
  apply Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc]
  exact h i

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem cone_hom_ext
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    {X Y P : CochainComplex A ℤ} (δ : X ⟶ Y)
    (f g : P ⟶ CochainComplex.mappingCocone δ)
    (hf : f ≫ CochainComplex.mappingCocone.fst δ =
      g ≫ CochainComplex.mappingCocone.fst δ)
    (hs : ∀ p : ℤ, f.f (p + 1) ≫ (CochainComplex.mappingCocone.snd δ).v
      (p + 1) p (add_neg_cancel_right p 1) = 0)
    (hs' : ∀ p : ℤ, g.f (p + 1) ≫ (CochainComplex.mappingCocone.snd δ).v
      (p + 1) p (add_neg_cancel_right p 1) = 0) : f = g := by
  ext i : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective i
  change f.f (p + 1) = g.f (p + 1)
  have hfi := congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1)) hf
  dsimp only [HomologicalComplex.comp_f] at hfi
  calc
    _ = _ ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ ≫ ((CochainComplex.mappingCocone.fst δ).f (p + 1) ≫
        (CochainComplex.mappingCocone.inl δ).v (p + 1) (p + 1) (add_zero _) +
        (CochainComplex.mappingCocone.snd δ).v (p + 1) p
          (add_neg_cancel_right p 1) ≫
        (CochainComplex.mappingCocone.inr δ).1.v p (p + 1) (by omega)) := by
      rw [CochainComplex.mappingCocone.id_X]
    _ = _ := by
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        hs p, zero_comp, add_zero, hfi]
      conv_rhs => rw [← Category.comp_id (g.f (p + 1)),
        ← CochainComplex.mappingCocone.id_X δ (p + 1) p
          (add_neg_cancel_right p 1)]
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        hs' p, zero_comp, add_zero]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem roos_map_fst
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') :
    integralOperationsRoosFunctor.map a ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary C') =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) := by
  dsimp only [integralOperationsRoosFunctor]
  exact (IntegralAmbient.roosMap_coordinates a).1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem roos_map_shift_zero
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C')
    {P : CochainComplex A ℤ} (f : P ⟶ integralOperationsRoos C)
    (hf : ∀ p : ℤ, f.f (p + 1) ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v
        (p + 1) p (add_neg_cancel_right p 1) = 0) (p : ℤ) :
    (f ≫ integralOperationsRoosFunctor.map a).f (p + 1) ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C')).v
        (p + 1) p (add_neg_cancel_right p 1) = 0 := by
  dsimp only [integralOperationsRoosFunctor]
  rw [HomologicalComplex.comp_f, Category.assoc,
    (IntegralAmbient.roosMap_coordinates a).2
      (p + 1) p (add_neg_cancel_right p 1), ← Category.assoc, hf p, zero_comp]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem image_shift_zero
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    {U V P : CochainComplex A ℤ} {U' V' : CochainComplex B ℤ}
    (δ : U ⟶ V) (δ' : U' ⟶ V') (v : P ⟶ CochainComplex.mappingCocone δ)
    (e : (F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCocone δ) ⟶ CochainComplex.mappingCocone δ')
    (p : ℤ) (b : F.obj (V.X p) ⟶ V'.X p)
    (he : e.f (p + 1) ≫ (CochainComplex.mappingCocone.snd δ').v
        (p + 1) p (add_neg_cancel_right p 1) =
      F.map ((CochainComplex.mappingCocone.snd δ).v
        (p + 1) p (add_neg_cancel_right p 1)) ≫ b)
    (hv : v.f (p + 1) ≫ (CochainComplex.mappingCocone.snd δ).v
        (p + 1) p (add_neg_cancel_right p 1) = 0) :
    ((F.mapHomologicalComplex (.up ℤ)).map v ≫ e).f (p + 1) ≫
      (CochainComplex.mappingCocone.snd δ').v
        (p + 1) p (add_neg_cancel_right p 1) = 0 := by
  change (F.map (v.f (p + 1)) ≫ e.f (p + 1)) ≫ _ = 0
  rw [Category.assoc, he, ← F.map_comp_assoc, hv, F.map_zero, zero_comp]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Multiplication fixes every actual finite pullback unit generator.
Source: Stacks 03D6; blueprint rational Frobenius integral model (2).
(blueprint: def-trf-multiplication-generator-normalized). -/
def TrfMultiplicationGeneratorNormalized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (a : (integralOperationsPullbackTowerFunctor l E g).obj P ⟶
      (trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj P)) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    ((a.app (op n)).f i).val.app (op U)
        ((((integralOperationsPullbackLevel l E g n).obj P).X i).val.map
          (proEtaleIsoCommaArrow g U).op
          (integralOperationsPullbackGenerator l E g n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)
            ((proEtaleIsoPostcompose g).obj U) x)) = x

set_option maxHeartbeats 100000 in
-- Elaborate both product-cone coordinate identities in the same generic argument.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem lift_roos_cancel
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ)
    (Q : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (γ : ∀ n : ℕ, P ⟶ Q.obj (op n))
    (θ : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ C.obj (op n))
    (hγ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ Q.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Limits.Pi.lift γ ≫ scalarRoosBoundary Q) = 0)
    (hθ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          (∏ᶜ fun n : ℕ ↦ C.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Limits.Pi.lift θ ≫ scalarRoosBoundary C) = 0)
    (a : C ⟶ Q ⋙ F.mapHomologicalComplex (.up ℤ))
    (e : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos Q) ≅
      integralOperationsRoos (Q ⋙ F.mapHomologicalComplex (.up ℤ)))
    (ha : ∀ n : ℕ, θ n ≫ a.app (op n) =
      (F.mapHomologicalComplex (.up ℤ)).map (γ n))
    (hef : e.hom ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary (Q ⋙ F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary Q)) ≫
      piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ Q.obj (op n)))
    (hes : ∀ p : ℤ, e.hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary (Q ⋙ F.mapHomologicalComplex (.up ℤ)))).v
            (p + 1) p (add_neg_cancel_right p 1) =
      F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary Q)).v
        (p + 1) p (add_neg_cancel_right p 1)) ≫
      (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ Q.obj (op n))).f p) :
    CochainComplex.mappingCocone.lift (scalarRoosBoundary C) (Limits.Pi.lift θ) 0 hθ ≫
        integralOperationsRoosFunctor.map a ≫ e.inv =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.lift (scalarRoosBoundary Q)
          (Limits.Pi.lift γ) 0 hγ) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let v := CochainComplex.mappingCocone.lift (scalarRoosBoundary Q)
    (Limits.Pi.lift γ) 0 hγ
  let c := CochainComplex.mappingCocone.lift (scalarRoosBoundary C)
    (Limits.Pi.lift θ) 0 hθ
  change c ≫ integralOperationsRoosFunctor.map a ≫ e.inv = G.map v
  have hcf : c ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) =
      Limits.Pi.lift θ := CochainComplex.mappingCocone.lift_fst _ _ _ _
  have hvf : v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary Q) =
      Limits.Pi.lift γ := CochainComplex.mappingCocone.lift_fst _ _ _ _
  have hh : c ≫ integralOperationsRoosFunctor.map a = G.map v ≫ e.hom := by
    apply cone_hom_ext (scalarRoosBoundary (Q ⋙ G))
    · rw [Category.assoc, roos_map_fst a, ← Category.assoc, hcf,
        Category.assoc, hef, ← Category.assoc, ← G.map_comp, hvf,
        map_lift_piComparison]
      exact lift_map_eq θ (fun n : ℕ ↦ a.app (op n))
        (fun n : ℕ ↦ G.map (γ n)) ha
    · intro p
      apply roos_map_shift_zero a
      intro q
      exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ hθ
        (q + 1) q (add_neg_cancel_right q 1)
    · intro p
      exact image_shift_zero F (scalarRoosBoundary Q)
        (scalarRoosBoundary (Q ⋙ G)) v e.hom p
        ((piComparison G (fun n : ℕ ↦ Q.obj (op n))).f p) (hes p)
        (CochainComplex.mappingCocone.lift_f_snd_v _ _ _ hγ _ _ _)
  rw [← Category.assoc, hh, Category.assoc, e.hom_inv_id]
  exact Category.comp_id _

-- Normalize scalar-extension presentations before the generic cone calculation.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Multiplication and the product comparison identify the specified comparison
with inverse image of the actual strict quotient augmentation.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md (2)--(3), step 3 of
lem-weil-isomorphism-derived-pullback-comparison-normalization; Stacks 03D6,
08TC, and 0941.
(blueprint: lem-trf-isomorphism-roos-unit-cancellation).

Proof: let v be the actual strict quotient augmentation. Its first coordinate
is the tuple of actual quotient units and its shifted coordinate is zero.
The specified comparison has first coordinate the finite comparison tuple and
shifted coordinate zero. Multiplication j cancels each finite generator, so the
first coordinate of the specified comparison followed by H(j) agrees with that
of G(v) followed by eta. The shifted coordinate of the former vanishes by the
Roos-map coordinate formula. The latter vanishes by the shifted coordinate
formula for eta and additivity of exact inverse image. The mapping-cocone
identity decomposition gives equality of the two whole chain maps. Cancel eta
to obtain the asserted identity. This calculation uses no completion calculus
or completedness assumption. -/
theorem isomorphismRoosUnitCancellation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (a : (integralOperationsPullbackTowerFunctor l E g).obj P ⟶
      (trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj P))
    (e : (trfInverseImageComplex l E g).obj
        (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P)) ≅
      integralOperationsRoos ((trfInverseImageTower l E g).obj
        ((trfQuotientTowerFunctor l E Y).obj P)))
    (hj : TrfMultiplicationGeneratorNormalized l E g P a)
    (heta_fst : e.hom ≫ CochainComplex.mappingCocone.fst
        (trfInverseQuotientDifference l E g P) =
      (trfInverseImageComplex l E g).map
        (CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y P)) ≫
      trfQuotientProductComparison l E g P)
    (heta_snd : ∀ p : ℤ, e.hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (trfInverseQuotientDifference l E g P)).v
          (p + 1) p (add_neg_cancel_right p 1) =
      (inverseImageIntegralModules l E g).map
        ((CochainComplex.mappingCocone.snd (trfQuotientDifference l E Y P)).v
          (p + 1) p (add_neg_cancel_right p 1)) ≫
      (trfQuotientProductComparison l E g P).f p) :
    inverseImageRoosComparisonComplex l E g P ≫ integralOperationsRoosFunctor.map a ≫
        e.inv =
      (trfInverseImageComplex l E g).map (trfStrictQuotientConeAugmentation l E Y P) := by
  let F : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
    inverseImageIntegralModules l E g
  let G := F.mapHomologicalComplex (.up ℤ)
  let Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E Y) ℤ :=
    (trfQuotientTowerFunctor l E Y).obj P
  let C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ :=
    (integralOperationsPullbackTowerFunctor l E g).obj P
  -- The two published quotient presentations use definitionally equal scalar extensions.
  let γ : ∀ n : ℕ, P ⟶ Q.obj (op n) := fun n ↦ by
    change P ⟶ (unrestrictedIntegralComplexFunctor l E Y n).obj P
    dsimp only [unrestrictedIntegralComplexFunctor, Functor.comp_obj,
      unrestrictedIntegralFiniteComplex, unrestrictedIntegralReductionFunctor,
      unrestrictedIntegralReductionExistence]
    exact unrestrictedTowerUnit l E Y P n
  let θ : ∀ n : ℕ, G.obj P ⟶ C.obj (op n) :=
    fun n ↦ inverseImageReductionTheta l E g n P
  have ha : ∀ n : ℕ, θ n ≫ a.app (op n) = G.map (γ n) := by
    intro n
    have ht := (inverseImageReductionTheta_existsUnique l E g n P).exists.choose_spec
    dsimp only [θ, γ, G, F]
    ext i U x
    change ((a.app (op n)).f i).val.app U
      (((inverseImageReductionTheta l E g n P).f i).val.app U x) = _
    dsimp only [inverseImageReductionTheta]
    erw [ht i U.unop x, hj n i U.unop]
    exact (unrestrictedTowerUnit_condition l E Y P n i
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x).symm
  with_unfolding_all
    exact lift_roos_cancel F P Q C γ θ (trfStrictQuotientUnit_condition l E Y P)
      (inverseImageReductionProduct_lift_condition l E g P) a e ha heta_fst heta_snd

end WeilConjectures
