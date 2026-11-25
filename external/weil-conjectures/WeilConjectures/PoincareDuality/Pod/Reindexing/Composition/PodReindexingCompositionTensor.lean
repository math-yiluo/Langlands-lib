/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import Mathlib.Tactic.CategoryTheory.Slice
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionTensorRoos
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorDerivedCompositionProof
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorCompositionOnGood
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Completed-tensor composition for section-normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
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
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor
  integralOperationsTensorOnGood integralOperationsGoodLocalization
  PodReindexFamily.constructible podOrdinaryReindex integralOperationsRoosFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section RepresentativeTransport

private theorem tensor_composition_transport
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂) (κ : H ≅ F ⋙ G)
    (B₀ : C₀ × C₀ ⥤ C₀) (B₁ : C₁ × C₁ ⥤ C₁) (B₂ : C₂ × C₂ ⥤ C₂)
    {M₀ N₀ M N : C₀} (p : M₀ ≅ M) (q : N₀ ≅ N)
    (μF₀ : F.obj (B₀.obj (M₀, N₀)) ⟶ B₁.obj (F.obj M₀, F.obj N₀))
    (μF : F.obj (B₀.obj (M, N)) ⟶ B₁.obj (F.obj M, F.obj N))
    (μG₀ : G.obj (B₁.obj (F.obj M₀, F.obj N₀)) ⟶
      B₂.obj (G.obj (F.obj M₀), G.obj (F.obj N₀)))
    (μG : G.obj (B₁.obj (F.obj M, F.obj N)) ⟶
      B₂.obj (G.obj (F.obj M), G.obj (F.obj N)))
    (μH₀ : H.obj (B₀.obj (M₀, N₀)) ⟶ B₂.obj (H.obj M₀, H.obj N₀))
    (μH : H.obj (B₀.obj (M, N)) ⟶ B₂.obj (H.obj M, H.obj N))
    (hgood : κ.hom.app (B₀.obj (M₀, N₀)) ≫ G.map μF₀ ≫ μG₀ =
      μH₀ ≫ B₂.map (Prod.mkHom (κ.hom.app M₀) (κ.hom.app N₀)))
    (hf : F.map (B₀.map (Prod.mkHom p.hom q.hom)) ≫ μF =
      μF₀ ≫ B₁.map (Prod.mkHom (F.map p.hom) (F.map q.hom)))
    (hh : G.map (B₁.map (Prod.mkHom (F.map p.hom) (F.map q.hom))) ≫ μG =
      μG₀ ≫ B₂.map (Prod.mkHom (G.map (F.map p.hom)) (G.map (F.map q.hom))))
    (hc : H.map (B₀.map (Prod.mkHom p.hom q.hom)) ≫ μH =
      μH₀ ≫ B₂.map (Prod.mkHom (H.map p.hom) (H.map q.hom))) :
    κ.hom.app (B₀.obj (M, N)) ≫ G.map μF ≫ μG =
      μH ≫ B₂.map (Prod.mkHom (κ.hom.app M) (κ.hom.app N)) := by
  have hp := κ.hom.naturality p.hom
  have hq := κ.hom.naturality q.hom
  have hκ := κ.hom.naturality (B₀.map (Prod.mkHom p.hom q.hom))
  change H.map p.hom ≫ κ.hom.app M = κ.hom.app M₀ ≫ G.map (F.map p.hom) at hp
  change H.map q.hom ≫ κ.hom.app N = κ.hom.app N₀ ≫ G.map (F.map q.hom) at hq
  change H.map (B₀.map (Prod.mkHom p.hom q.hom)) ≫ κ.hom.app (B₀.obj (M, N)) =
    κ.hom.app (B₀.obj (M₀, N₀)) ≫ G.map (F.map (B₀.map (Prod.mkHom p.hom q.hom))) at hκ
  apply (cancel_epi (H.map (B₀.mapIso (p.prod q)).hom)).1
  change H.map (B₀.map (Prod.mkHom p.hom q.hom)) ≫
    (κ.hom.app (B₀.obj (M, N)) ≫ G.map μF ≫ μG) = _
  slice_lhs 1 2 => rw [hκ]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← G.map_comp, hf, G.map_comp]
  simp only [Category.assoc]
  rw [hh]
  slice_lhs 1 3 => exact hgood
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [← B₂.map_comp]
    change B₂.map (Prod.mkHom
      (κ.hom.app M₀ ≫ G.map (F.map p.hom))
      (κ.hom.app N₀ ≫ G.map (F.map q.hom)))
    rw [← hp, ← hq]
    rw [show Prod.mkHom (_ ≫ _) (_ ≫ _) =
      Prod.mkHom _ _ ≫ Prod.mkHom _ _ from rfl, B₂.map_comp]
  slice_lhs 1 2 => rw [← hc]
  simp only [CategoryTheory.Functor.mapIso_hom, Iso.prod_hom, Category.assoc]

end RepresentativeTransport

-- The representative transport involves three derived reindexing functors.
/-- The completed-tensor equation on complete constructible inputs.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: lem-pod-reindexing-composition-tensor-equation).

Proof: choose flat-term K-flat representatives P,Q of the two inputs. Their
reindexed complexes are good by each completion datum's good field. For each
positive quotient and each homogeneous summand of the total tensor, Generators
identifies T.tower with the tensor of the two quotient comparisons. Applying the
two reindexings successively to a pure tensor gives the same restrictions of
both factors as applying their composite, because hcomposition is Over.mapComp
on every original section. QuotientGenerators fixes the coefficient action as
well. Pure tensors generate each tensor module before sheafification, and the
maps respect the sheafification units; the generator equalities therefore give
whole degreewise maps. QuotientTransition shows these equalities commute with
the strict tower transitions. Apply all product projections and then RoosFst
and RoosSnd to obtain equality of the entire Roos chain maps, retaining the cone
shift. Localize this equality and substitute Model for the three tensor maps.
The representative comparisons and the factors for the intermediate reindexing
cancel by their inverse equations and naturality. This proves the displayed
equation on the represented inputs. The Naturality law transports it along the
two chosen representative isomorphisms to M and N. Neither faithfulness of
finite evaluations nor perfection of the inputs is used. Zero inputs and empty
schemes use the same generator argument. This statement does not assert the
ambient reduction or total-limit composition equation. -/
theorem podReindexingCompositionTensor
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f))
    (hcomposition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f] (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x) :
    ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)],
      ∀ M N : sfIntegralConstructibleCategory l E V,
        (A.compositionDerived l E h f).hom.app
            ((integralCompletedTensor l E V).obj (M.obj,N.obj)) ≫
          (podOrdinaryReindex l E h).map ((A.tensor f).tensor M N).hom ≫
          ((A.tensor h).tensor ((A.constructible l E f).obj M)
            ((A.constructible l E f).obj N)).hom =
        ((A.tensor (h ≫ f)).tensor M N).hom ≫ (integralCompletedTensor l E Z).map
          (Prod.mkHom ((A.compositionDerived l E h f).hom.app M.obj)
            ((A.compositionDerived l E h f).hom.app N.obj)) := by
  intro V W Z h f _ _ _ _ _ M N
  let _ : (isoReductionIntegralInverse l E f).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} f (isoReductionCompletedMap l E f).hom
  let _ : PreservesFiniteLimits (isoReductionIntegralInverse l E f) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} f (isoReductionCompletedMap l E f).hom
  let _ : PreservesFiniteColimits (isoReductionIntegralInverse l E f) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} f (isoReductionCompletedMap l E f).hom
  let _ : (isoReductionIntegralInverse l E h).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} h (isoReductionCompletedMap l E h).hom
  let _ : PreservesFiniteLimits (isoReductionIntegralInverse l E h) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} h (isoReductionCompletedMap l E h).hom
  let _ : PreservesFiniteColimits (isoReductionIntegralInverse l E h) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} h (isoReductionCompletedMap l E h).hom
  let _ : (isoReductionIntegralInverse l E (h ≫ f)).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} (h ≫ f)
      (isoReductionCompletedMap l E (h ≫ f)).hom
  let _ : PreservesFiniteLimits (isoReductionIntegralInverse l E (h ≫ f)) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} (h ≫ f)
      (isoReductionCompletedMap l E (h ≫ f)).hom
  let _ : PreservesFiniteColimits (isoReductionIntegralInverse l E (h ≫ f)) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} (h ≫ f)
      (isoReductionCompletedMap l E (h ≫ f)).hom
  let L := integralOperationsGoodLocalization l E V
  let S := (HomologicalComplex.quasiIso (scalarReductionSource l E V) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E V).ι
  let : L.IsLocalization S := integralOperationsGoodLocalization_isLocalization l E V
  have : L.EssSurj := Localization.essSurj L S
  let P := L.objPreimage M.obj
  let Q := L.objPreimage N.obj
  let eP : DerivedCategory.Q.obj P.obj ≅ M.obj := L.objObjPreimageIso M.obj
  let eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj := L.objObjPreimageIso N.obj
  let : (sfIntegralConstructible l E V).IsClosedUnderIsomorphisms :=
    sfIntegralConstructible_isClosedUnderIsomorphisms l E V
  let M₀ : sfIntegralConstructibleCategory l E V :=
    ⟨_, (sfIntegralConstructible l E V).prop_of_iso eP.symm M.property⟩
  let N₀ : sfIntegralConstructibleCategory l E V :=
    ⟨_, (sfIntegralConstructible l E V).prop_of_iso eQ.symm N.property⟩
  let p : M₀ ⟶ M := ObjectProperty.homMk eP.hom
  let q : N₀ ⟶ N := ObjectProperty.homMk eQ.hom
  let F := podOrdinaryReindex l E f
  let G := podOrdinaryReindex l E h
  let H := podOrdinaryReindex l E (h ≫ f)
  let B₀ := integralCompletedTensor l E V
  let B₁ := integralCompletedTensor l E W
  let B₂ := integralCompletedTensor l E Z
  let κ := A.compositionDerived l E h f
  have hroos := podCompositionTensorRoos l E A h f (hcompletion f) (hcompletion h)
    (hcompletion (h ≫ f)) (htensor f).1 (htensor h).1 (htensor (h ≫ f)).1
    (hcomposition h f) P Q
  have hd := podTensorDerivedComposition l E A h f P Q hroos
  have hgood := podTensorCompositionOnGood l E A h f
    (htensor f) (htensor h) (htensor (h ≫ f)) P Q M₀.property N₀.property hd
  have hf := (htensor f).2.2.2.1 M₀ N₀ M N p q
  have hh := (htensor h).2.2.2.1
    ((A.constructible l E f).obj M₀) ((A.constructible l E f).obj N₀)
    ((A.constructible l E f).obj M) ((A.constructible l E f).obj N)
    ((A.constructible l E f).map p) ((A.constructible l E f).map q)
  have hc := (htensor (h ≫ f)).2.2.2.1 M₀ N₀ M N p q
  exact tensor_composition_transport F G H κ B₀ B₁ B₂ eP eQ
    ((A.tensor f).tensor M₀ N₀).hom ((A.tensor f).tensor M N).hom
    ((A.tensor h).tensor ((A.constructible l E f).obj M₀)
      ((A.constructible l E f).obj N₀)).hom
    ((A.tensor h).tensor ((A.constructible l E f).obj M)
      ((A.constructible l E f).obj N)).hom
    ((A.tensor (h ≫ f)).tensor M₀ N₀).hom ((A.tensor (h ≫ f)).tensor M N).hom
    hgood hf hh hc

end WeilConjectures
