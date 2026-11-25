/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import WeilConjectures.SixFunctors.Open.OpenDvrLimitComparison
import WeilConjectures.SixFunctors.Open.OpenDvrStrictReductionComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
/-! # Reduction and augmentation under canonical DVR coefficients

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-augmented-reduction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The reduction-only part of the augmented comparison, relative to the separately
constructed normalized limit comparison. Source: Stacks 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-augmented-reduction-comparison). -/
structure OpenDvrAugmentedReductionComparison
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (M : OpenDvrLimitComparison l E C) where
  /-- The two quotient tower functors are canonically identified. -/
  tower : C.derived.functor ⋙ completedAdicReduction T d ≅
    S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers
  /-- The same strict tensor augmentation, before taking total derived inverse limit. -/
  representative : ∀ (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (_hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (Q.X i)) →
    ∃ (B : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ)
      (a : ((Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _).mapHomologicalComplex
        (.up ℤ)).obj Q ⟶ B)
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj B ≅
        unrestrictedIntegralComplexTower.{u, u} l E T Q)
      (e : (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj B)
      (τ : ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
          (C.complexes.obj Q) ≅ C.towerComplexes.obj B),
      (∀ (i : ℤ) (n : ℕ),
        (reconstructionOrdinaryUnit T d).app (C.modules.functor.obj (Q.X i)) ≫
            limit.π ((completedAdicOrdinaryTower T d).obj
              (C.modules.functor.obj (Q.X i))) (op n) ≫ (τ.hom.f i).app (op n) =
          C.modules.functor.map ((a.f i).app (op n))) ∧
      ((completedAdicReduction T d).map
          (C.modules.functor.mapDerivedCategoryFactors.hom.app Q) ≫
          reconstructionReductionComplexCounit T d (C.complexes.obj Q) ≫
          DerivedCategory.Q.map τ.hom =
        tower.hom.app (DerivedCategory.Q.obj Q) ≫ C.towers.map e.hom ≫
          C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B) ∧
      (∀ n : ℕ, HEq
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app (op n) ≫
          κ.hom.app (op n)) (unrestrictedTowerUnit.{u, u} l E T Q n)) ∧
      (C.derived.functor.map (S.adjunction.unit.app (DerivedCategory.Q.obj Q)) ≫
          C.derived.functor.map ((coefficientConstantTowerLimit.{u, u} l E T).map e.hom) =
        C.derived.functor.map (DerivedCategory.Q.map
          (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
              lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
              ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
                (.up ℤ)).map a) ≫
          derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B))
  /-- The quotient completion unit is the actual semilinear reduction/limit unit. -/
  unit : ∀ P : DerivedCategory (scalarReductionSource.{u, u} l E T),
    (reconstructionCompletionUnit T d).app (C.derived.functor.obj P) ≫
        (reconstructionRlim T d).map (tower.hom.app P) ≫
          M.rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
            (S.reduction.obj P)) =
      C.derived.functor.map (S.adjunction.unit.app P)
private def reductionComplexCounitNat
    {B D : Type*} [Category B] [Abelian B] [Category D] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    {F : B ⥤ D} [F.Additive] {P : CochainComplex B ℤ → Prop}
    (R : DerivedReductionModelData F P) :
    DerivedCategory.Q ⋙ R.reduction ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso B).inv R.reduction ≫
    Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) R.counit ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom

private def limitComplexComparisonNat
    {B D : Type*} [Category B] [Abelian B] [Category D] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (L : D ⥤ B) [L.Additive] (RF : DerivedCategory D ⥤ DerivedCategory B)
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF) :
    L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
  Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B).inv ≫
    Functor.whiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient D (.up ℤ)) δ ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso D).hom RF

private theorem cancelMappedInverse
    {D H : Type*} [Category D] [Category H] (R : D ⥤ H)
    {V W : D} (f : V ⟶ W) [IsIso f] {X Y : H}
    (a : X ⟶ Y) (b : Y ⟶ R.obj W) :
    (a ≫ b ≫ R.map (inv f)) ≫ R.map f = a ≫ b := by
  rw [Category.assoc, Category.assoc, ← R.map_comp, IsIso.inv_hom_id,
    R.map_id, Category.comp_id]

private theorem completionUnit_complex
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    (reconstructionCompletionUnit T d).app (DerivedCategory.Q.obj P) ≫
        (reconstructionRlim T d).map (reconstructionReductionComplexCounit T d P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app P) ≫
        reconstructionRlimComparison T d
          (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := completedAdicOrdinaryTower T d
  let L := reconstructionLimit T d
  let RF := reconstructionRlim T d
  let ε := reductionComplexCounitNat (completedAdicReductionData T d)
  let δ := limitComplexComparisonNat L RF L.rightDerivedFunctorUnit
  let α : DerivedCategory.Q ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ RF :=
    Functor.whiskerLeft DerivedCategory.Q (reconstructionCompletionUnit T d) ≫
      Functor.whiskerRight ε RF
  let β : DerivedCategory.Q ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ RF :=
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ))
      DerivedCategory.Q ≫ Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) δ
  have hk (K : CochainComplex (CompletedAdicModules T d) ℤ)
      (hK : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) K) :
      α.app K = β.app K := by
    have := reconstructionTowerCounit_isIso T d K hK
    change (reconstructionCompletionUnit T d).app (DerivedCategory.Q.obj K) ≫
      RF.map (reconstructionReductionComplexCounit T d K) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app K) ≫
      reconstructionRlimComparison T d
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj K)
    unfold reconstructionCompletionUnit
    rw [(reconstructionCompletionUnit_exists T d).exists.choose_spec K hK]
    exact cancelMappedInverse RF (reconstructionReductionComplexCounit T d K) _ _
  obtain ⟨K, f, hK, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedAdicCommRing T d) P
  have : QuasiIso f := hf
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  have hn := α.naturality f
  have hn' := β.naturality f
  have hp : α.app P = β.app P := by
    apply (cancel_epi (DerivedCategory.Q.map f)).1
    exact hn.trans ((congrArg (fun z ↦ z ≫ _) (hk K hK)).trans hn'.symm)
  exact hp

private theorem augmentedUnit_on_flat
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (M : OpenDvrLimitComparison l E C) (A : OpenDvrStrictReductionComparison l E C S)
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i)) :
    (reconstructionCompletionUnit T d).app (C.derived.functor.obj (DerivedCategory.Q.obj Q)) ≫
        (reconstructionRlim T d).map (A.tower.hom.app (DerivedCategory.Q.obj Q)) ≫
          M.rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
            (S.reduction.obj (DerivedCategory.Q.obj Q))) =
      C.derived.functor.map (S.adjunction.unit.app (DerivedCategory.Q.obj Q)) := by
  obtain ⟨B, a, κ, e, τ, hτ, hred, _, hunit⟩ := A.representative Q hQ hflat
  obtain ⟨σ, hσ, hlim⟩ := M.limit_model B
  let L : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _ := lim
  let h : Q ⟶ (L.mapHomologicalComplex (.up ℤ)).obj B :=
    ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
        L).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
      (L.mapHomologicalComplex (.up ℤ)).map a
  have hOrd :
      (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app
          (C.complexes.obj Q) ≫
        ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).map τ.hom ≫ σ.hom =
      C.complexes.map h := by
    apply HomologicalComplex.hom_ext
    intro i
    apply (isLimitOfPreserves C.modules.functor (limit.isLimit (B.X i))).hom_ext
    intro n
    change _ ≫ C.modules.functor.map (limit.π (B.X i) n) =
      _ ≫ C.modules.functor.map (limit.π (B.X i) n)
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [hσ i n.unop]
    change (reconstructionOrdinaryUnit T d).app (C.modules.functor.obj (Q.X i)) ≫
      limMap (τ.hom.f i) ≫ limit.π _ n =
      C.modules.functor.map (h.f i) ≫ C.modules.functor.map (limit.π (B.X i) n)
    rw [limMap_π]
    erw [hτ i n.unop]
    dsimp only [h, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [← C.modules.functor.map_comp]
    congr 1
    symm
    change (constLimAdj.unit.app (Q.X i) ≫ lim.map (a.f i)) ≫
      limit.π (B.X i) n = (a.f i).app n
    simp [constLimAdj]
  have hOrd' :
      (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app
          (C.complexes.obj Q) ≫
        ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).map τ.hom =
      C.complexes.map h ≫ σ.inv := by
    apply (cancel_mono σ.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hOrd
  let R := reconstructionRlim T d
  let p := C.modules.functor.mapDerivedCategoryFactors.hom.app Q
  let b := C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B
  have hb : R.map (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app B) ≫ R.map b =
      𝟙 _ := by
    rw [← R.map_comp, Iso.inv_hom_id_app, R.map_id]
  have hnat := M.rlim.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hnat
  have hr := congrArg R.map hred
  simp only [Functor.map_comp] at hr
  have hn := (reconstructionCompletionUnit T d).naturality p
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hδ := (limitComplexComparisonNat (reconstructionLimit T d) R
    (reconstructionLimit T d).rightDerivedFunctorUnit).naturality τ.hom
  change DerivedCategory.Q.map
      (((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).map τ.hom) ≫
        reconstructionRlimComparison T d (C.towerComplexes.obj B) =
      reconstructionRlimComparison T d _ ≫ R.map (DerivedCategory.Q.map τ.hom) at hδ
  have hf := C.modules.functor.mapDerivedCategoryFactors.hom.naturality h
  dsimp only [Functor.comp_map] at hf
  apply (cancel_mono
    (C.derived.functor.map ((coefficientConstantTowerLimit.{u, u} l E T).map e.hom))).1
  rw [hunit]
  change _ = C.derived.functor.map (DerivedCategory.Q.map h ≫ _)
  rw [C.derived.functor.map_comp, hlim]
  simp only [Category.assoc]
  erw [← hnat]
  change (reconstructionCompletionUnit T d).app _ ≫ R.map (A.tower.hom.app _) ≫
    R.map (C.towers.map e.hom) ≫ M.rlim.hom.app _ = _
  apply (cancel_mono (M.rlim.inv.app (DerivedCategory.Q.obj B))).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, Category.comp_id]
  apply (cancel_mono (R.map b)).1
  simp only [Category.assoc]
  erw [hb, Category.comp_id]
  erw [← hr]
  erw [← reassoc_of% hn]
  erw [reassoc_of% (completionUnit_complex l E d T (C.complexes.obj Q))]
  erw [← hδ]
  erw [← DerivedCategory.Q.map_comp_assoc, hOrd', DerivedCategory.Q.map_comp]
  erw [reassoc_of% hf]
  exact congrArg (p ≫ ·) (Category.assoc
    (DerivedCategory.Q.map (C.complexes.map h)) (DerivedCategory.Q.map σ.inv)
    (reconstructionRlimComparison T d (C.towerComplexes.obj B)))

/-- The strict scalar tensor augmentation computes the actual unit after coefficient transport.
Source: Stacks Tags 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-augmented-reduction-comparison).

Proof: finite constants and completed projections identify the two ringed quotient
diagrams. On modules the tensor universal property identifies the quotient functors,
with identity on pure tensors and compatibility with each transition. The universal
left-derived property gives tower. For a flat-term K-flat representative Q, transpose
the actual scalar tensor complex to B. The same pure-tensor comparison gives kappa,
tau and the reduction counit comparison e, including the ordinary augmentation equation.
Apply sequenceTensorAugmentationUnit to the projection cone: its total-limit equation
identifies the actual adjunction unit with the localization of the ordinary compatible
family x tensor one. Uniqueness of derived left adjoints carries this equality to S.
The supplied limit_model equation transports this representative equation through M.
Finally the normalized reconstructionCompletionUnit equation on K-flat representatives
and localization naturality extend the result to every P. No completeness hypothesis,
regular generator, open immersion or exactness of countable products is used. -/
theorem openDvrAugmentedReductionComparison
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (M : OpenDvrLimitComparison l E C) :
    Nonempty (OpenDvrAugmentedReductionComparison l E C S M) := by
  classical
  obtain ⟨A⟩ := openDvrStrictReductionComparison l E d T C S
  let α : C.derived.functor ⟶
      (S.reduction ⋙ coefficientSequenceLimit.{u, u} l E T) ⋙ C.derived.functor :=
    Functor.whiskerLeft C.derived.functor (reconstructionCompletionUnit T d) ≫
      Functor.whiskerRight A.tower.hom (reconstructionRlim T d) ≫
      Functor.whiskerLeft (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T)
        M.rlim.hom
  let β : C.derived.functor ⟶
      (S.reduction ⋙ coefficientSequenceLimit.{u, u} l E T) ⋙ C.derived.functor :=
    Functor.whiskerRight S.adjunction.unit C.derived.functor
  refine ⟨{ tower := A.tower, representative := A.representative, unit := ?_ }⟩
  intro P
  let Q₀ : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ :=
    DerivedCategory.Q.objPreimage P
  obtain ⟨Q, f, hQ, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q₀
  have : QuasiIso f := hf
  let i : DerivedCategory.Q.obj Q ≅ P :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso P
  have hi : α.app (DerivedCategory.Q.obj Q) = β.app (DerivedCategory.Q.obj Q) :=
    augmentedUnit_on_flat l E d T C S M A Q hQ (fun i ↦
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i)).symm
        (hflat i))
  have hp : α.app P = β.app P := by
    apply (cancel_epi (C.derived.functor.map i.hom)).1
    exact (α.naturality i.hom).trans
      ((congrArg (fun z ↦ z ≫ _) hi).trans (β.naturality i.hom).symm)
  exact hp

end WeilConjectures
