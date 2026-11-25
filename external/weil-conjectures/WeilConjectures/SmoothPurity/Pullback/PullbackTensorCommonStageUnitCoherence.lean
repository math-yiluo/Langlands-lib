/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Common.CommonStageTensorRightUnitorNaturality
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalUnitCoherence
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality

/-! Common-stage unit coherence for the completed pullback tensor comparison.

Source: Stacks Project, Tags 07A4 and 0941; the common-stage part of
`lem-pur-pullback-tensor-unit-coherence`.
(blueprint: lem-pur-pullback-tensor-common-stage-unit-coherence)

The proof represents source and target units at a common finite coefficient
field, transports the rational unit equations, and proves independence of the
field by scalar compatibility. Uniqueness is obtained by unit cancellation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open scoped TensorProduct
namespace WeilConjectures

-- Fix the category wrappers before comparing normalized representatives.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  commonStageTensorComparison commonStagePullbackComparison operationStageTransitionIso
  commonStageDerivedTensor commonStageDerivedPullback pullbackTensorCommonUnit
  pullbackTensorCommonUnitStage rationalDerivedPullback
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

private theorem unit_map_injective
    {C : Type*} [Category* C] (T : C × C ⥤ C) (U V : C)
    (e : V ≅ U) (r : ∀ A, T.obj (A, U) ≅ A)
    (hr : ∀ {A B} (f : A ⟶ B),
      T.map (Prod.mkHom f (𝟙 U)) ≫ (r B).hom = (r A).hom ≫ f)
    {A B : C} (f g : A ⟶ B)
    (h : T.map (Prod.mkHom f (𝟙 V)) = T.map (Prod.mkHom g (𝟙 V))) : f = g := by
  have ht : T.map (Prod.mkHom f (𝟙 U)) = T.map (Prod.mkHom g (𝟙 U)) := by
    apply (cancel_epi (T.mapIso (Iso.prod (Iso.refl A) e)).hom).1
    change T.map (Prod.mkHom (𝟙 A) e.hom) ≫ T.map (Prod.mkHom f (𝟙 U)) =
      T.map (Prod.mkHom (𝟙 A) e.hom) ≫ T.map (Prod.mkHom g (𝟙 U))
    rw [← T.map_comp, ← T.map_comp]
    have hf : Prod.mkHom (𝟙 A) e.hom ≫ Prod.mkHom f (𝟙 U) =
        Prod.mkHom f (𝟙 V) ≫ Prod.mkHom (𝟙 B) e.hom := by ext <;> simp
    have hg : Prod.mkHom (𝟙 A) e.hom ≫ Prod.mkHom g (𝟙 U) =
        Prod.mkHom g (𝟙 V) ≫ Prod.mkHom (𝟙 B) e.hom := by ext <;> simp
    rw [hf, hg, T.map_comp, T.map_comp, h]
  apply (cancel_epi (r A).hom).1
  rw [← hr f, ← hr g, ht]

private theorem unit_comparison_unique
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : D × D ⥤ D) (U : C) (V : D)
    (B : C) (μ : F.obj B ≅ T.obj (F.obj U, F.obj U))
    (lu : T.obj (V, F.obj U) ≅ F.obj U)
    (r : ∀ A, T.obj (A, V) ≅ A)
    (hr : ∀ {A B} (f : A ⟶ B),
      T.map (Prod.mkHom f (𝟙 V)) ≫ (r B).hom = (r A).hom ≫ f)
    (e d : F.obj U ≅ V)
    (h : μ.hom ≫ T.map (Prod.mkHom e.hom (𝟙 _)) ≫ lu.hom =
      μ.hom ≫ T.map (Prod.mkHom d.hom (𝟙 _)) ≫ lu.hom) : e = d := by
  apply Iso.ext
  apply unit_map_injective T V (F.obj U) e r hr
  exact (cancel_mono lu.hom).1 ((cancel_epi μ.hom).1 h)

private theorem left_tensor_unit_square {C : Type*} [Category* C]
    (T : C × C ⥤ C) {U V : C} (e : V ⟶ U)
    (r : ∀ M, T.obj (U, M) ⟶ M)
    (hr : ∀ {M N} (f : M ⟶ N), T.map (Prod.mkHom (𝟙 U) f) ≫ r N = r M ≫ f)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 V) f) ≫ T.map (Prod.mkHom e (𝟙 N)) ≫ r N =
      T.map (Prod.mkHom e (𝟙 M)) ≫ r M ≫ f := by
  have h : Prod.mkHom (𝟙 V) f ≫ Prod.mkHom e (𝟙 N) =
      Prod.mkHom e (𝟙 M) ≫ Prod.mkHom (𝟙 U) f := by
    ext <;> simp
  rw [← T.map_comp_assoc, h, T.map_comp, Category.assoc, hr]

private theorem left_naturality_of_reduction
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (T : C × C ⥤ C) (R : C ⥤ D) [R.Faithful]
    (a : T ⋙ R ≅ R.prod R ⋙ MonoidalCategory.tensor D)
    (U : C) (e : R.obj U ≅ MonoidalCategoryStruct.tensorUnit D)
    (r : ∀ M, T.obj (U, M) ≅ M)
    (h : ∀ M, R.map (r M).hom = a.hom.app (U, M) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom e.hom (𝟙 _)) ≫
      (MonoidalCategoryStruct.leftUnitor (R.obj M)).hom)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 U) f) ≫ (r N).hom = (r M).hom ≫ f := by
  apply R.map_injective
  rw [Functor.map_comp, Functor.map_comp, h, h]
  have hn := a.hom.naturality (Prod.mkHom (𝟙 U) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  apply congrArg (fun z ↦ a.hom.app (U, M) ≫ z)
  rw [R.map_id]
  apply left_tensor_unit_square (MonoidalCategory.tensor D) e.hom
    (fun M ↦ (MonoidalCategoryStruct.leftUnitor M).hom)
  intro M N g
  simpa only [MonoidalCategory.tensor_map, MonoidalCategory.id_tensorHom] using
    MonoidalCategory.leftUnitor_naturality g

section LeftNaturality
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

private theorem left_integral_naturality {M N : sfIntegralConstructibleCategory l E X}
    (f : M ⟶ N) :
    (constructibleIntegralTensor l E X).map (Prod.mkHom (𝟙 _) f) ≫
        (pullbackTensorIntegralLeftUnitor l E X N).hom =
      (pullbackTensorIntegralLeftUnitor l E X M).hom ≫ f := by
  have : (coherentReduction l E X).Faithful := by
    have h := (integralSystemReduction_fullyFaithful l E X).2
    change (coherentReduction l E X).Faithful at h
    exact h
  let S := (pullbackTensorCalculus l E X).systemClosed
  let := S.monoidal
  exact left_naturality_of_reduction (constructibleIntegralTensor l E X)
    (coherentReduction l E X) (reductionTensor l E X)
    (pullbackTensorIntegralUnit l E X) (pullbackTensorIntegralUnitReduction l E X)
    (fun M ↦ pullbackTensorIntegralLeftUnitor l E X M)
    (fun M ↦ (pullbackTensorIntegralLeftUnitor_existsUnique l E X M).exists.choose_spec) f

private theorem left_rational_naturality {M N : sfRationalConstructibleCategory l E X}
    (f : M ⟶ N) :
    (rationalDerivedTensor l E X).map (Prod.mkHom (𝟙 _) f) ≫
        (pullbackTensorRationalLeftUnitor l E X N).hom =
      (pullbackTensorRationalLeftUnitor l E X M).hom ≫ f := by
  let U := pullbackTensorRationalUnit l E X
  let T := rationalDerivedTensor l E X
  have hT := chosen_spec (rationalDerivedTensor_existsUnique l E X) T
    (by unfold T rationalDerivedTensor; rfl)
  obtain ⟨b, hb, hpure⟩ := hT.2 U U M N
  have hM := chosen_spec (pullbackTensorRationalLeftUnitor_existsUnique l E X M)
    (pullbackTensorRationalLeftUnitor l E X M)
    (by unfold pullbackTensorRationalLeftUnitor; rfl)
  have hN := chosen_spec (pullbackTensorRationalLeftUnitor_existsUnique l E X N)
    (pullbackTensorRationalLeftUnitor l E X N)
    (by unfold pullbackTensorRationalLeftUnitor; rfl)
  change T.map (Prod.mkHom (𝟙 U) f) ≫ _ = _
  induction f using TensorProduct.inductionOn with
  | tmul c f =>
    have hm : HEq (T.map (Prod.mkHom
        (𝟙 U) (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralTensor l E X).map (Prod.mkHom (𝟙 U.obj) f)) := by
      rw [hb]
      change HEq (b (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] 𝟙 U.obj)
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)) _
      simpa only [one_mul] using hpure (𝟙 U.obj) f 1 c
    have hleft := heq_comp (hT.1 (U, M)) (hT.1 (U, N)) rfl hm hN
    have hright := heq_comp (hT.1 (U, M)) rfl rfl hM
      (HEq.rfl : HEq (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[_] (pullbackTensorIntegralLeftUnitor l E X N.obj).hom)
        (c ⊗ₜ[_] (constructibleIntegralTensor l E X).map (Prod.mkHom (𝟙 U.obj) f)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ[_] f) (1 ⊗ₜ[_] (pullbackTensorIntegralLeftUnitor l E X M.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun z ↦ c ⊗ₜ[Padic.coefficientExtensionIntegers l E] z)
      (left_integral_naturality l E X f)
  | add f g hf hg =>
    simp only [hb, map_add, Preadditive.add_comp] at hf hg ⊢
    rw [hf, hg]
    exact (Preadditive.comp_add (C := sfRationalConstructibleCategory l E X) _ _ _
      (pullbackTensorRationalLeftUnitor l E X M).hom (f : M ⟶ N) (g : M ⟶ N)).symm

end LeftNaturality

attribute [local irreducible] rationalDerivedTensor pullbackTensorRationalUnit
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
  Linear.homModule Preadditive.homGroup

private theorem representative_left_unit
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (S : C × C ⥤ C) (T : D × D ⥤ D)
    (U : C) (V : D)
    (μ : ∀ M N, F.obj (S.obj (M, N)) ≅ T.obj (F.obj M, F.obj N))
    (hn : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (S.map (Prod.mkHom a b)) ≫ (μ M' N').hom =
        (μ M N).hom ≫ T.map (Prod.mkHom (F.map a) (F.map b)))
    (lamY : ∀ M, S.obj (U, M) ≅ M) (lamX : ∀ M, T.obj (V, M) ≅ M)
    (hlam : ∀ {M N} (f : M ⟶ N),
      T.map (Prod.mkHom (𝟙 V) f) ≫ (lamX N).hom = (lamX M).hom ≫ f)
    (e : F.obj U ≅ V)
    (he : ∀ M, (μ U M).hom ≫ T.map (Prod.mkHom e.hom (𝟙 _)) ≫
      (lamX (F.obj M)).hom = F.map (lamY M).hom)
    {P Q K : C} {A B V' J H H' : D}
    (a : P ≅ U) (b : V' ≅ V) (p : A ≅ F.obj P) (q : B ≅ F.obj Q)
    (s : K ≅ S.obj (P, Q)) (w : J ≅ F.obj K)
    (t : H ≅ T.obj (A, B)) (t' : H' ≅ T.obj (V', B)) :
    ((w.hom ≫ F.map s.hom ≫ (μ P Q).hom ≫
      T.map (Prod.mkHom p.inv q.inv) ≫ t.inv) ≫
      (t.hom ≫ T.map (Prod.mkHom
        (p.hom ≫ F.map a.hom ≫ e.hom ≫ b.inv) (𝟙 B)) ≫ t'.inv)) ≫
      (t'.hom ≫ T.map (Prod.mkHom b.hom (𝟙 B)) ≫ (lamX B).hom) =
    w.hom ≫ F.map (s.hom ≫ S.map (Prod.mkHom a.hom (𝟙 Q)) ≫
      (lamY Q).hom) ≫ q.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [← T.map_comp_assoc, ← T.map_comp_assoc]
  simp only [prod_comp, Category.assoc, Category.comp_id, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id]
  have ht : Prod.mkHom (F.map a.hom ≫ e.hom) q.inv =
      Prod.mkHom (F.map a.hom) (𝟙 _) ≫
        Prod.mkHom e.hom (𝟙 _) ≫ Prod.mkHom (𝟙 V) q.inv := by ext <;> simp
  rw [ht, T.map_comp, T.map_comp]
  simp only [Category.assoc]
  rw [hlam]
  have hμ := hn a.hom (𝟙 Q)
  rw [F.map_id] at hμ
  rw [← reassoc_of% hμ, reassoc_of% he Q]

private theorem representative_right_unit
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (S : C × C ⥤ C) (T : D × D ⥤ D)
    (U : C) (V : D)
    (μ : ∀ M N, F.obj (S.obj (M, N)) ≅ T.obj (F.obj M, F.obj N))
    (hn : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (S.map (Prod.mkHom a b)) ≫ (μ M' N').hom =
        (μ M N).hom ≫ T.map (Prod.mkHom (F.map a) (F.map b)))
    (ρY : ∀ M, S.obj (M, U) ≅ M) (ρX : ∀ M, T.obj (M, V) ≅ M)
    (hρ : ∀ {M N} (f : M ⟶ N),
      T.map (Prod.mkHom f (𝟙 V)) ≫ (ρX N).hom = (ρX M).hom ≫ f)
    (e : F.obj U ≅ V)
    (he : ∀ M, (μ M U).hom ≫ T.map (Prod.mkHom (𝟙 _) e.hom) ≫
      (ρX (F.obj M)).hom = F.map (ρY M).hom)
    {P Q K : C} {A B V' J H H' : D}
    (a : P ≅ U) (b : V' ≅ V) (p : A ≅ F.obj P) (q : B ≅ F.obj Q)
    (s : K ≅ S.obj (Q, P)) (w : J ≅ F.obj K)
    (t : H ≅ T.obj (B, A)) (t' : H' ≅ T.obj (B, V')) :
    ((w.hom ≫ F.map s.hom ≫ (μ Q P).hom ≫
      T.map (Prod.mkHom q.inv p.inv) ≫ t.inv) ≫
      (t.hom ≫ T.map (Prod.mkHom (𝟙 B)
        (p.hom ≫ F.map a.hom ≫ e.hom ≫ b.inv)) ≫ t'.inv)) ≫
      (t'.hom ≫ T.map (Prod.mkHom (𝟙 B) b.hom) ≫ (ρX B).hom) =
    w.hom ≫ F.map (s.hom ≫ S.map (Prod.mkHom (𝟙 Q) a.hom) ≫
      (ρY Q).hom) ≫ q.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [← T.map_comp_assoc, ← T.map_comp_assoc]
  simp only [prod_comp, Category.assoc, Category.comp_id, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id]
  have ht : Prod.mkHom q.inv (F.map a.hom ≫ e.hom) =
      Prod.mkHom (𝟙 _) (F.map a.hom) ≫
        Prod.mkHom (𝟙 _) e.hom ≫ Prod.mkHom q.inv (𝟙 V) := by ext <;> simp
  rw [ht, T.map_comp, T.map_comp]
  simp only [Category.assoc]
  rw [hρ]
  have hμ := hn (𝟙 Q) a.hom
  rw [F.map_id] at hμ
  rw [← reassoc_of% hμ, reassoc_of% he Q]

private def atStageIso {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category* (C i)] (S : StageSystem C)
    (A B : S.PairCategory) (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (e : A.toStage hA ≅ B.toStage hB) : A ≅ B :=
  S.isoToStage A hA ≪≫ (S.ι L).mapIso e ≪≫ (S.isoToStage B hB).symm

private theorem atStageIso_hom {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category* (C i)] (S : StageSystem C)
    (A B : S.PairCategory) (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (e : A.toStage hA ≅ B.toStage hB) :
    (atStageIso S A B L hA hB e).hom =
      StageSystem.PairCategory.mkHom L hA hB e.hom :=
  (StageSystem.mkHom_eq_isoToStage hA hB e.hom).symm

private def withSource {C : Type*} [Category* C] {A A' B : C}
    (h : A = A') (e : A' ≅ B) : A ≅ B := eqToIso h ≪≫ e

private theorem withSource_hom {C : Type*} [Category* C] {A A' B : C}
    (h : A = A') (e : A' ≅ B) : HEq (withSource h e).hom e.hom := by
  subst A'
  simp only [withSource, eqToIso_refl, Iso.refl_trans]
  rfl

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The prescribed common-stage comparison preserves the coefficient-ring unit uniquely.

Source: Stacks 07A4 and 0941, and the coefficient descent in the parent unit-coherence proof.
(blueprint: lem-pur-pullback-tensor-common-stage-unit-coherence).

Proof: At any finite stage conjugate the uniquely normalized rational unit comparison by
its unit and pullback stage isomorphisms, and include it in the pair category. Substitution
of the tensor, pullback, comparison and unitor representative formulas reduces both unit
squares to rational unit coherence, using rational comparison and unitor naturality.
Fix this map at a stage containing the source unit tensor square. Its left square at the
source unit determines it: cancel the comparison and left unitor; identify the pulled-back
source unit with the target unit; cancel tensoring using naturality of the right unitor.
For an arbitrary object enlarge the stage to include all four left and right tensor
objects. The map there satisfies both squares and agrees with the fixed map by the same
unit-square cancellation. Thus both equations hold for every object, and the comparison
is unique. No separate scalar compatibility choice is required. -/
theorem pullbackTensorCommonStageUnitCoherence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    canonicalCommonStagePullbackTensor_unit l Ω f := by
  classical
  let F := commonStageDerivedPullback l Ω f
  let TY := commonStageDerivedTensor l Ω Y
  let TX := commonStageDerivedTensor l Ω X
  let OY := commonStageTensorObject l Ω Y
  let OX := commonStageTensorObject l Ω X
  let PB := commonStagePullbackObject l Ω f
  let UY := pullbackTensorCommonUnit l Ω Y
  let UX := pullbackTensorCommonUnit l Ω X
  have hoY (A B) : TY.obj (A, B) = OY A B := by
    unfold TY commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 A B
  have hoX (A B) : TX.obj (A, B) = OX A B := by
    unfold TX commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 A B
  have hoF (A) : F.obj A = PB A := by
    unfold F commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A
  let E (L : AlgebraicallyClosedCoefficients.Index l Ω) :=
    AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  let eR (L : AlgebraicallyClosedCoefficients.Index l Ω) :=
    (pullbackTensorRationalUnitCoherence l (E L) f).exists.choose
  have heR (L : AlgebraicallyClosedCoefficients.Index l Ω) :=
    (pullbackTensorRationalUnitCoherence l (E L) f).exists.choose_spec
  let er (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hy : UY.stage ≤ L) (hx : UX.stage ≤ L) :=
    commonStagePullbackComparison l Ω f UY L hy ≪≫
      (rationalDerivedPullback l (E L) f).mapIso
        (pullbackTensorCommonUnitStage l Ω Y L hy) ≪≫
      eR L ≪≫ (pullbackTensorCommonUnitStage l Ω X L hx).symm
  let eAt (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hy : UY.stage ≤ L) (hx : UX.stage ≤ L) : F.obj UY ≅ UX :=
    withSource (hoF UY) (atStageIso (stageSystem l Ω X) (PB UY) UX L hy hx (er L hy hx))
  have heAt (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hy : UY.stage ≤ L) (hx : UX.stage ≤ L) :
      HEq (eAt L hy hx).hom (ofHom (PB UY) UX L hy hx (er L hy hx).hom) :=
    (withSource_hom (hoF UY) _).trans (heq_of_eq (atStageIso_hom _ _ _ _ _ _ _))
  have hmap {L : AlgebraicallyClosedCoefficients.Index l Ω}
      {A B A' B' : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
      (hA : A = A') (hB : B = B') (hA' : A'.stage ≤ L) (hB' : B'.stage ≤ L)
      (c : A ⟶ B) (d : A'.toStage hA' ⟶ B'.toStage hB')
      (hc : HEq c (ofHom A' B' L hA' hB' d)) :
      HEq (F.map c) (ofHom (PB A') (PB B') L hA' hB'
        ((commonStagePullbackComparison l Ω f A' L hA').hom ≫
          (rationalDerivedPullback l (E L) f).map d ≫
          (commonStagePullbackComparison l Ω f B' L hB').inv)) := by
    refine (cached_map_heq F hA hB hc).trans ?_
    dsimp only [F, PB, E]
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
      A' B' L hA' hB' d
  have hTX := chosen_spec (commonStageDerivedTensor_existsUnique l Ω X) TX
    (by unfold TX commonStageDerivedTensor; rfl)
  have hthree {L : AlgebraicallyClosedCoefficients.Index l Ω}
      {A B C D : generalAlgebraicallyClosedConstructibleCategory l Ω X}
      (hA : A.stage ≤ L) (hB : B.stage ≤ L) (hC : C.stage ≤ L) (hD : D.stage ≤ L)
      (a : A.toStage hA ⟶ B.toStage hB) (b : B.toStage hB ⟶ C.toStage hC)
      (c : C.toStage hC ⟶ D.toStage hD) :
      (ofHom A B L hA hB a ≫ ofHom B C L hB hC b) ≫ ofHom C D L hC hD c =
        ofHom A D L hA hD ((a ≫ b) ≫ c) := by
    exact (congrArg (fun t ↦ t ≫ ofHom C D L hC hD c)
      (StageSystem.PairCategory.mkHom_comp_mkHom a b)).trans
      (StageSystem.PairCategory.mkHom_comp_mkHom (a ≫ b) c)
  have hleft (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hs : (OY UY M).stage ≤ L) (ht : (OX UX (PB M)).stage ≤ L) :
      (canonicalCommonStagePullbackTensor l Ω f UY M).hom ≫
        TX.map (Prod.mkHom (eAt L
          (((Padic.finiteCoefficientFields_properties l Ω).1 UY.stage M.stage).1.trans hs)
          (((Padic.finiteCoefficientFields_properties l Ω).1 UX.stage (PB M).stage).1.trans ht)
          ).hom (𝟙 _)) ≫
        (pullbackTensorCommonLeftUnitor l Ω X (F.obj M)).hom =
      F.map (pullbackTensorCommonLeftUnitor l Ω Y M).hom := by
    let hy := ((Padic.finiteCoefficientFields_properties l Ω).1 UY.stage M.stage).1.trans hs
    let hx := ((Padic.finiteCoefficientFields_properties l Ω).1 UX.stage (PB M).stage).1.trans ht
    let hm := ((Padic.finiteCoefficientFields_properties l Ω).1 UY.stage M.stage).2.trans hs
    have hμ := (canonicalCommonStagePullbackTensor_existsUnique l Ω f UY M).exists.choose_spec L hs
    change HEq (canonicalCommonStagePullbackTensor l Ω f UY M).hom _ at hμ
    have hylam := (pullbackTensorCommonLeftUnitor_existsUnique l Ω Y M).exists.choose_spec L hs
    change HEq (pullbackTensorCommonLeftUnitor l Ω Y M).hom _ at hylam
    have hyF := hmap (hoY UY M) rfl hs hm _ _ hylam
    have hxlam := (pullbackTensorCommonLeftUnitor_existsUnique l Ω X (PB M)).exists.choose_spec L ht
    change HEq (pullbackTensorCommonLeftUnitor l Ω X (PB M)).hom _ at hxlam
    have hxcongr : HEq (pullbackTensorCommonLeftUnitor l Ω X (F.obj M)).hom
        (pullbackTensorCommonLeftUnitor l Ω X (PB M)).hom := by
      have h (A B : generalAlgebraicallyClosedConstructibleCategory l Ω X) (hab : A = B) :
          HEq (pullbackTensorCommonLeftUnitor l Ω X A).hom
            (pullbackTensorCommonLeftUnitor l Ω X B).hom := by subst B; rfl
      exact h _ _ (hoF M)
    have hid : HEq (𝟙 (F.obj M)) (ofHom (PB M) (PB M) L hm hm (𝟙 _)) :=
      (cached_id_heq (hoF M)).trans (heq_of_eq (StageSystem.PairCategory.id_eq_mkHom (PB M) hm))
    have htmap := (cached_bimap_heq TX (hoF UY) rfl (hoF M) (hoF M)
      (heAt L hy hx) hid).trans
      (hTX.2 (PB UY) (PB M) UX (PB M) L hs ht (er L hy hx).hom (𝟙 _))
    have hsrc := (congrArg F.obj (hoY UY M)).trans (hoF (OY UY M))
    have hmid := (hoX (F.obj UY) (F.obj M)).trans (congrArg₂ OX (hoF UY) (hoF M))
    have hend := (hoX UX (F.obj M)).trans (congrArg (OX UX) (hoF M))
    have hl := heq_comp hsrc hmid hend hμ htmap
    have hl := heq_comp hsrc hend (hoF M) hl (hxcongr.trans hxlam)
    simp only [← Category.assoc]
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hyF.symm)
    change (ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _) ≫ ofHom _ _ L _ _ _ =
      ofHom _ _ L _ _ _
    refine (hthree _ _ _ _ _ _ _).trans (congrArg (ofHom _ _ L _ _) ?_)
    dsimp only [pullbackTensorAtCommonStage, er, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.prod_hom]
    exact representative_left_unit
      (rationalDerivedPullback l (E L) f) (rationalDerivedTensor l (E L) Y)
      (rationalDerivedTensor l (E L) X) (pullbackTensorRationalUnit l (E L) Y)
      (pullbackTensorRationalUnit l (E L) X)
      (canonicalRationalPullbackTensor l (E L) f)
      (fun a b ↦ canonicalRationalPullbackTensor_naturality l (E L) f a b)
      (pullbackTensorRationalLeftUnitor l (E L) Y)
      (pullbackTensorRationalLeftUnitor l (E L) X)
      (fun a ↦ left_rational_naturality l (E L) X a)
      (eR L) (fun N ↦ (heR L N).1)
      (pullbackTensorCommonUnitStage l Ω Y L hy)
      (pullbackTensorCommonUnitStage l Ω X L hx)
      (commonStagePullbackComparison l Ω f UY L hy)
      (commonStagePullbackComparison l Ω f M L hm)
      (commonStageTensorComparison l Ω Y UY M L hs)
      (commonStagePullbackComparison l Ω f (OY UY M) L hs)
      (commonStageTensorComparison l Ω X (PB UY) (PB M) L hs)
      (commonStageTensorComparison l Ω X UX (PB M) L ht)
  have hright (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hs : (OY M UY).stage ≤ L) (ht : (OX (PB M) UX).stage ≤ L) :
      (canonicalCommonStagePullbackTensor l Ω f M UY).hom ≫
        TX.map (Prod.mkHom (𝟙 _) (eAt L
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage UY.stage).2.trans hs)
          (((Padic.finiteCoefficientFields_properties l Ω).1 (PB M).stage UX.stage).2.trans ht)
          ).hom) ≫
        (pullbackTensorCommonRightUnitor l Ω X (F.obj M)).hom =
      F.map (pullbackTensorCommonRightUnitor l Ω Y M).hom := by
    let hy := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage UY.stage).2.trans hs
    let hx := ((Padic.finiteCoefficientFields_properties l Ω).1 (PB M).stage UX.stage).2.trans ht
    let hm := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage UY.stage).1.trans hs
    have hμ := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M UY).exists.choose_spec L hs
    change HEq (canonicalCommonStagePullbackTensor l Ω f M UY).hom _ at hμ
    have hyρ := (pullbackTensorCommonRightUnitor_existsUnique l Ω Y M).exists.choose_spec L hs
    change HEq (pullbackTensorCommonRightUnitor l Ω Y M).hom _ at hyρ
    have hyF := hmap (hoY M UY) rfl hs hm _ _ hyρ
    have hxρ := (pullbackTensorCommonRightUnitor_existsUnique l Ω X (PB M)).exists.choose_spec L ht
    change HEq (pullbackTensorCommonRightUnitor l Ω X (PB M)).hom _ at hxρ
    have hxcongr : HEq (pullbackTensorCommonRightUnitor l Ω X (F.obj M)).hom
        (pullbackTensorCommonRightUnitor l Ω X (PB M)).hom := by
      have h (A B : generalAlgebraicallyClosedConstructibleCategory l Ω X) (hab : A = B) :
          HEq (pullbackTensorCommonRightUnitor l Ω X A).hom
            (pullbackTensorCommonRightUnitor l Ω X B).hom := by subst B; rfl
      exact h _ _ (hoF M)
    have hid : HEq (𝟙 (F.obj M)) (ofHom (PB M) (PB M) L hm hm (𝟙 _)) :=
      (cached_id_heq (hoF M)).trans (heq_of_eq (StageSystem.PairCategory.id_eq_mkHom (PB M) hm))
    have htmap := (cached_bimap_heq TX (hoF M) (hoF M) (hoF UY) rfl
      hid (heAt L hy hx)).trans
      (hTX.2 (PB M) (PB UY) (PB M) UX L hs ht (𝟙 _) (er L hy hx).hom)
    have hsrc := (congrArg F.obj (hoY M UY)).trans (hoF (OY M UY))
    have hmid := (hoX (F.obj M) (F.obj UY)).trans (congrArg₂ OX (hoF M) (hoF UY))
    have hend := (hoX (F.obj M) UX).trans (congrArg (fun A ↦ OX A UX) (hoF M))
    have hl := heq_comp hsrc hmid hend hμ htmap
    have hl := heq_comp hsrc hend (hoF M) hl (hxcongr.trans hxρ)
    simp only [← Category.assoc]
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hyF.symm)
    change (ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _) ≫ ofHom _ _ L _ _ _ =
      ofHom _ _ L _ _ _
    refine (hthree _ _ _ _ _ _ _).trans (congrArg (ofHom _ _ L _ _) ?_)
    dsimp only [pullbackTensorAtCommonStage, er, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.prod_hom]
    exact representative_right_unit
      (rationalDerivedPullback l (E L) f) (rationalDerivedTensor l (E L) Y)
      (rationalDerivedTensor l (E L) X) (pullbackTensorRationalUnit l (E L) Y)
      (pullbackTensorRationalUnit l (E L) X)
      (canonicalRationalPullbackTensor l (E L) f)
      (fun a b ↦ canonicalRationalPullbackTensor_naturality l (E L) f a b)
      (pullbackTensorRationalRightUnitor l (E L) Y)
      (pullbackTensorRationalRightUnitor l (E L) X)
      (fun a ↦ rational_naturality l (E L) X a)
      (eR L) (fun N ↦ (heR L N).2)
      (pullbackTensorCommonUnitStage l Ω Y L hy)
      (pullbackTensorCommonUnitStage l Ω X L hx)
      (commonStagePullbackComparison l Ω f UY L hy)
      (commonStagePullbackComparison l Ω f M L hm)
      (commonStageTensorComparison l Ω Y M UY L hs)
      (commonStagePullbackComparison l Ω f (OY M UY) L hs)
      (commonStageTensorComparison l Ω X (PB M) (PB UY) L hs)
      (commonStageTensorComparison l Ω X (PB M) UX L ht)
  -- First normalize at the source unit. This single equation determines the map.
  obtain ⟨L₀, hy₀, hx₀⟩ := exists_ge_ge (OY UY UY).stage (OX UX (PB UY)).stage
  let hy := ((Padic.finiteCoefficientFields_properties l Ω).1 UY.stage UY.stage).1.trans hy₀
  let hx := ((Padic.finiteCoefficientFields_properties l Ω).1 UX.stage (PB UY).stage).1.trans hx₀
  let e := eAt L₀ hy hx
  have he := hleft UY L₀ hy₀ hx₀
  have hunique (d : F.obj UY ≅ UX)
      (hd : (canonicalCommonStagePullbackTensor l Ω f UY UY).hom ≫
        TX.map (Prod.mkHom d.hom (𝟙 _)) ≫
        (pullbackTensorCommonLeftUnitor l Ω X (F.obj UY)).hom =
        F.map (pullbackTensorCommonLeftUnitor l Ω Y UY).hom) : d = e := by
    exact unit_comparison_unique F TX UY UX (TY.obj (UY, UY))
      (canonicalCommonStagePullbackTensor l Ω f UY UY)
      (pullbackTensorCommonLeftUnitor l Ω X (F.obj UY))
      (pullbackTensorCommonRightUnitor l Ω X)
      (fun a ↦ commonStageTensorRightUnitor_naturality l X Ω a) d e (hd.trans he.symm)
  refine ⟨e, ?_, ?_⟩
  · intro M
    obtain ⟨L₁, h₀, hl⟩ := exists_ge_ge L₀ (OY UY M).stage
    obtain ⟨L₂, h₁, hlt⟩ := exists_ge_ge L₁ (OX UX (PB M)).stage
    obtain ⟨L₃, h₂, hr⟩ := exists_ge_ge L₂ (OY M UY).stage
    obtain ⟨L, h₃, hrt⟩ := exists_ge_ge L₃ (OX (PB M) UX).stage
    have hbase := h₀.trans (h₁.trans (h₂.trans h₃))
    have hl := hl.trans (h₁.trans (h₂.trans h₃))
    have hlt := hlt.trans (h₂.trans h₃)
    have hr := hr.trans h₃
    have hnorm := hleft UY L (hy₀.trans hbase) (hx₀.trans hbase)
    have hchange := hunique _ hnorm
    constructor
    · have h := hleft M L hl hlt
      rw [hchange] at h
      exact h
    · have h := hright M L hr hrt
      rw [hchange] at h
      exact h
  · intro d hd
    exact hunique d (hd UY).1

end WeilConjectures
