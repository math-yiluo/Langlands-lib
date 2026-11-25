/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityLimit
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityDerivedFactors
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityTensorRoos
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

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
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus WeilConjectures.coefficientSequenceRestriction

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem reduction_identity_of_limit
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (F : C ⥤ C) (S : D ⥤ D) (a : F ≅ 𝟭 C) (b : S ≅ 𝟭 D)
    (d : L ⋙ S ≅ F ⋙ L) (e : R ⋙ F ≅ S ⋙ R)
    (hu : ∀ K, F.map (adj.unit.app K) ≫ e.hom.app (L.obj K) ≫
      R.map (d.hom.app K) = adj.unit.app (F.obj K))
    (he : ∀ N, e.hom.app N ≫ R.map (b.hom.app N) = a.hom.app (R.obj N))
    (K : C) : d.hom.app K ≫ L.map (a.hom.app K) = b.hom.app (L.obj K) := by
  have hi : d.inv.app K ≫ b.hom.app (L.obj K) = L.map (a.hom.app K) := by
    apply (adj.homEquiv _ _).injective
    simp only [adj.homEquiv_unit, R.map_comp]
    have hu' : adj.unit.app (F.obj K) ≫ R.map (d.inv.app K) =
        F.map (adj.unit.app K) ≫ e.hom.app (L.obj K) := by
      rw [← hu K]
      simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← Category.assoc, hu', Category.assoc, he]
    calc
      _ = a.hom.app K ≫ adj.unit.app K := a.hom.naturality (adj.unit.app K)
      _ = _ := adj.unit.naturality (a.hom.app K)
  calc
    d.hom.app K ≫ L.map (a.hom.app K) =
        d.hom.app K ≫ (d.inv.app K ≫ b.hom.app (L.obj K)) := by rw [hi]
    _ = b.hom.app (L.obj K) := by simp

private abbrev identity_section_formula
    (W : Scheme.{u}) (a : isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _) : Prop :=
  ∀ (M : scalarReductionSource l E W) (U : W.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
    (a.hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
        (𝟙 W) rfl).hom.app U).op x

section TensorIdentityProof

attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos
  integralCompletedTensorComparison isoSectionwiseModuleInverseImage
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsTensorOnGood integralOperationsGoodLocalization

private theorem tensor_identity_of_model
    {C : Type*} [Category C] (F : C ⥤ C) (B : C × C ⥤ C) (a : F ≅ 𝟭 C)
    {M N P Q K L : C} (e : B.obj (M, N) ≅ K) (e' : B.obj (P, Q) ≅ L)
    (cM : F.obj M ⟶ P) (cN : F.obj N ⟶ Q) (cK : F.obj K ⟶ L)
    (p : P ⟶ M) (q : Q ⟶ N) (h : L ⟶ K)
    (t : F.obj (B.obj (M, N)) ⟶ B.obj (F.obj M, F.obj N))
    (hm : F.map e.hom ≫ cK = t ≫ B.map (Prod.mkHom cM cN) ≫ e'.hom)
    (hn : B.map (Prod.mkHom p q) ≫ e.hom = e'.hom ≫ h)
    (hp : a.hom.app M = cM ≫ p) (hq : a.hom.app N = cN ≫ q)
    (hk : cK ≫ h = a.hom.app K) :
    t ≫ B.map (Prod.mkHom (a.hom.app M) (a.hom.app N)) =
      a.hom.app (B.obj (M, N)) := by
  apply (cancel_mono e.hom).1
  calc
    _ = t ≫ B.map (Prod.mkHom cM cN) ≫ e'.hom ≫ h := by
      rw [hp, hq]
      rw [show Prod.mkHom (_ ≫ _) (_ ≫ _) =
        Prod.mkHom _ _ ≫ Prod.mkHom _ _ from rfl, B.map_comp]
      simp only [Category.assoc]
      rw [hn]
    _ = F.map e.hom ≫ cK ≫ h := by rw [← reassoc_of% hm]
    _ = F.map e.hom ≫ a.hom.app K := by rw [hk]
    _ = _ := a.hom.naturality e.hom

private theorem tensor_identity_on_good (A : PodReindexFamily l E)
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (hD : PodCompletionReindex.Laws l E (𝟙 W) (A.completion (𝟙 W)))
    (hT : PodCompletedTensorReindex.Laws l E (𝟙 W) (A.completion (𝟙 W)) (A.tensor (𝟙 W)))
    (ha : identity_section_formula l E W (A.identity W))
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (hP : sfIntegralConstructible l E W (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E W (DerivedCategory.Q.obj Q.obj)) :
    ((A.tensor (𝟙 W)).tensor ⟨_, hP⟩ ⟨_, hQ⟩).hom ≫
        (integralCompletedTensor l E W).map
          (Prod.mkHom ((A.identityDerived l E W).hom.app (DerivedCategory.Q.obj P.obj))
            ((A.identityDerived l E W).hom.app (DerivedCategory.Q.obj Q.obj))) =
      (A.identityDerived l E W).hom.app
        ((integralCompletedTensor l E W).obj (DerivedCategory.Q.obj P.obj,
          DerivedCategory.Q.obj Q.obj)) := by
  let D := A.completion (𝟙 W)
  let T := A.tensor (𝟙 W)
  let F := podOrdinaryReindex l E (𝟙 W)
  let B := integralCompletedTensor l E W
  let H := integralOperationsTensorComplexFunctor l E W
  let β := integralCompletedTensorComparison l E W
  let a := A.identityDerived l E W
  let α := NatIso.mapHomologicalComplex (A.identity W) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let FP := (podGoodReindex l E (𝟙 W) D).obj P
  let FQ := (podGoodReindex l E (𝟙 W) D).obj Q
  let p : FP ⟶ P := ObjectProperty.homMk (α.hom.app P.obj)
  let q : FQ ⟶ Q := ObjectProperty.homMk (α.hom.app Q.obj)
  have hm : PodCompletedTensorReindex.Model l E (𝟙 W) D T := hT.2.2.2.2.1
  have hmPQ := eq_of_heq (hm P Q hP hQ)
  change F.map (β.hom.app (P, Q)) ≫
      (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((D.roos
        ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))).hom ≫
          integralOperationsRoosFunctor.map (T.tower P Q).hom) =
    (T.tensor ⟨_, hP⟩ ⟨_, hQ⟩).hom ≫ B.map
      (Prod.mkHom
        ((isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app P.obj)
        ((isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
      β.hom.app (FP, FQ) at hmPQ
  have hg : PodCompletionReindex.QuotientGenerators l E (𝟙 W) D := by
    obtain ⟨_, _, _, _, _, _, hg, _⟩ := hD
    exact hg
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hf, hs, _⟩ := hD
  have hc := podIdentityTensorRoos l E W D hg T hT.1 hf hs (A.identity W) ha P Q
  change (D.roos ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))).hom ≫
    integralOperationsRoosFunctor.map (T.tower P Q).hom ≫
      H.map (Prod.mkHom p.hom q.hom) = α.hom.app (H.obj (P.obj, Q.obj)) at hc
  have hβ := β.hom.naturality (Prod.mkHom p q)
  change B.map (Prod.mkHom (DerivedCategory.Q.map p.hom) (DerivedCategory.Q.map q.hom)) ≫
    β.hom.app (P, Q) = β.hom.app (FP, FQ) ≫
      DerivedCategory.Q.map (H.map (Prod.mkHom p.hom q.hom)) at hβ
  have hp := podIdentityDerivedFactors (isoReductionIntegralInverse l E (𝟙 W))
    (A.identity W) P.obj
  have hq := podIdentityDerivedFactors (isoReductionIntegralInverse l E (𝟙 W))
    (A.identity W) Q.obj
  have hh := podIdentityDerivedFactors (isoReductionIntegralInverse l E (𝟙 W))
    (A.identity W) (H.obj (P.obj, Q.obj))
  change a.hom.app (DerivedCategory.Q.obj P.obj) =
    (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app P.obj ≫
      DerivedCategory.Q.map p.hom at hp
  change a.hom.app (DerivedCategory.Q.obj Q.obj) =
    (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app Q.obj ≫
      DerivedCategory.Q.map q.hom at hq
  change a.hom.app (DerivedCategory.Q.obj (H.obj (P.obj, Q.obj))) =
    (isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (α.hom.app (H.obj (P.obj, Q.obj))) at hh
  have hk :
      ((isoReductionIntegralInverse l E (𝟙 W)).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((D.roos
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))).hom ≫
            integralOperationsRoosFunctor.map (T.tower P Q).hom)) ≫
        DerivedCategory.Q.map (H.map (Prod.mkHom p.hom q.hom)) =
      a.hom.app (DerivedCategory.Q.obj (H.obj (P.obj, Q.obj))) := by
    rw [Category.assoc, ← DerivedCategory.Q.map_comp, Category.assoc, hc]
    exact hh.symm
  exact tensor_identity_of_model F B a (β.app (P, Q)) (β.app (FP, FQ))
    _ _ _ (DerivedCategory.Q.map p.hom) (DerivedCategory.Q.map q.hom)
    (DerivedCategory.Q.map (H.map (Prod.mkHom p.hom q.hom)))
    (T.tensor ⟨_, hP⟩ ⟨_, hQ⟩).hom hmPQ hβ hp hq hk

end TensorIdentityProof

/-- The identity relabelling commutes with reduction, total limit and completed tensor.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941
(blueprint: lem-pod-reindexing-identity-compatibility).

Proof: podIdentityLimit gives the whole-system limit equation from the restricted
section formula, the two Roos coordinates, normalized K-injective models and
localization. Unit compatibility and injectivity of the adjunction homEquiv give
the reduction equation. For good representatives, podIdentityTensorRoos gives the
whole cochain identity. Substitute the tensor Model equation, use naturality of
its representative comparison, and cancel that isomorphism. Essential surjectivity
of the good localization supplies representatives for both constructible inputs;
constructibility is preserved by their isomorphisms. Naturality transports the
tensor equation to the original inputs. The remaining strict tensor-tower lemma
is stated separately with its generator-and-sheafification argument. -/
theorem podReindexingIdentityCompatibility
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f))
    (hidentity : ∀ (W : Scheme.{u}) (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      ((A.identity W).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x) :
    A.Identity l E := by
  intro W _
  have hD := hcompletion (𝟙 W)
  have hT := htensor (𝟙 W)
  have hi := hidentity W
  have hl := podIdentityLimit l E A W hD hi
  refine ⟨?_, hl, ?_⟩
  · intro K
    exact reduction_identity_of_limit
      (podReindexCalculus l E W).reduction (coefficientSequenceLimit l E W)
      (podReindexCalculus l E W).adjunction
      (podOrdinaryReindex l E (𝟙 W)) (integralComparisonDerivedSequencePullback l E (𝟙 W))
      (A.identityDerived l E W) (integralComparisonSystemUnit l E W)
      (A.completion (𝟙 W)).reduction (A.completion (𝟙 W)).limit hD.2.2.2.1 hl K
  · intro M N
    let L := integralOperationsGoodLocalization l E W
    let V := (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E W).ι
    let : L.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
    have : L.EssSurj := Localization.essSurj L V
    let P := L.objPreimage M.obj
    let Q := L.objPreimage N.obj
    let eP : DerivedCategory.Q.obj P.obj ≅ M.obj := L.objObjPreimageIso M.obj
    let eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj := L.objObjPreimageIso N.obj
    let : (sfIntegralConstructible l E W).IsClosedUnderIsomorphisms :=
      sfIntegralConstructible_isClosedUnderIsomorphisms l E W
    let M₀ : sfIntegralConstructibleCategory l E W :=
      ⟨_, (sfIntegralConstructible l E W).prop_of_iso eP.symm M.property⟩
    let N₀ : sfIntegralConstructibleCategory l E W :=
      ⟨_, (sfIntegralConstructible l E W).prop_of_iso eQ.symm N.property⟩
    let p : M₀ ⟶ M := ObjectProperty.homMk eP.hom
    let q : N₀ ⟶ N := ObjectProperty.homMk eQ.hom
    let F := podOrdinaryReindex l E (𝟙 W)
    let B := integralCompletedTensor l E W
    let T := A.tensor (𝟙 W)
    let a := A.identityDerived l E W
    have ht := tensor_identity_on_good l E A W hD hT hi P Q M₀.property N₀.property
    have hn : PodCompletedTensorReindex.Naturality l E (𝟙 W) (A.completion (𝟙 W)) T :=
      hT.2.2.2.1
    have hp := a.hom.naturality eP.hom
    have hq := a.hom.naturality eQ.hom
    change F.map eP.hom ≫ a.hom.app M.obj =
      a.hom.app M₀.obj ≫ eP.hom at hp
    change F.map eQ.hom ≫ a.hom.app N.obj =
      a.hom.app N₀.obj ≫ eQ.hom at hq
    apply (cancel_epi (F.map (B.mapIso (eP.prod eQ)).hom)).1
    change F.map (B.map (Prod.mkHom eP.hom eQ.hom)) ≫
        ((T.tensor M N).hom ≫ B.map (Prod.mkHom (a.hom.app M.obj) (a.hom.app N.obj))) =
      F.map (B.map (Prod.mkHom eP.hom eQ.hom)) ≫ a.hom.app (B.obj (M.obj, N.obj))
    calc
      _ = (T.tensor M₀ N₀).hom ≫
          B.map (Prod.mkHom (F.map eP.hom) (F.map eQ.hom)) ≫
          B.map (Prod.mkHom (a.hom.app M.obj) (a.hom.app N.obj)) := by
        have h := hn M₀ N₀ M N p q
        change F.map (B.map (Prod.mkHom eP.hom eQ.hom)) ≫ (T.tensor M N).hom =
          (T.tensor M₀ N₀).hom ≫
            B.map (Prod.mkHom (F.map eP.hom) (F.map eQ.hom)) at h
        rw [← Category.assoc, h, Category.assoc]
      _ = (T.tensor M₀ N₀).hom ≫
          B.map (Prod.mkHom (a.hom.app M₀.obj) (a.hom.app N₀.obj)) ≫
          B.map (Prod.mkHom eP.hom eQ.hom) := by
        rw [← B.map_comp]
        change _ ≫ B.map (Prod.mkHom (F.map eP.hom ≫ a.hom.app M.obj)
          (F.map eQ.hom ≫ a.hom.app N.obj)) = _
        rw [hp, hq]
        rw [show Prod.mkHom (_ ≫ _) (_ ≫ _) =
          Prod.mkHom _ _ ≫ Prod.mkHom _ _ from rfl, B.map_comp]
      _ = a.hom.app (B.obj (M₀.obj, N₀.obj)) ≫
          B.map (Prod.mkHom eP.hom eQ.hom) := by rw [← Category.assoc, ht]
      _ = _ := (a.hom.naturality (B.map (Prod.mkHom eP.hom eQ.hom))).symm

end WeilConjectures
