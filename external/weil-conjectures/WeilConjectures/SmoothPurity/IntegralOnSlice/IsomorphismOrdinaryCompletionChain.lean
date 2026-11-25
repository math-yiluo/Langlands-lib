/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SmoothPurity.IntegralOnSlice.IsomorphismOrdinaryModuleNormalization
import WeilConjectures.SmoothPurity.IntegralOnSlice.IsomorphismOrdinaryQuotientTowerNormalization
import WeilConjectures.SmoothPurity.IntegralOnSlice.IsomorphismOrdinaryFiniteAugmentation
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismQuotientRoosComparison
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Strict completion chains under a scheme isomorphism

Source: the expanded DAG definition prose-10-21, clause 4;
Stacks Project, Tags 03EL and 08TC.
(blueprint: lem-pur-isomorphism-ordinary-completion-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralOnSlice

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted
attribute [local instance_reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring
attribute [local instance_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf

private instance sectionwise_additive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (inverseImageIntegralModules l E g).Additive :=
  isoSectionwiseModuleInverseImage_additive.{u, u} g _

section GenericAugmentation
universe a b c d
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]

omit [HasCountableProducts B] in
private theorem cocone_ext {K L M : CochainComplex B ℤ} (φ : K ⟶ L)
    {f g : M ⟶ CochainComplex.mappingCocone φ}
    (hfst : f ≫ CochainComplex.mappingCocone.fst φ =
      g ≫ CochainComplex.mappingCocone.fst φ)
    (hsnd : ∀ i : ℤ, f.f i ≫ (CochainComplex.mappingCocone.snd φ).v
        i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  have hf := congrArg (fun k ↦ k.f i) hfst
  change f.f i ≫ _ = g.f i ≫ _ at hf
  calc
    f.f i = f.f i ≫ 𝟙 _ := by rw [Category.comp_id]
    _ = f.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by rw [h]
    _ = g.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hf, hsnd]
    _ = g.f i := by rw [h, Category.comp_id]

private theorem augmentedRoosMap
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ) (H : CochainComplex B ℤ)
    (Q : ℕᵒᵖ ⥤ CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (b : H ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P)
    (a : Q ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ T)
    (γ : P ⟶ integralOperationsRoos Q) (θ : H ⟶ integralOperationsRoos T)
    (hθ : ∀ n : ℕ,
      b ≫ (F.mapHomologicalComplex (.up ℤ)).map
          (γ ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary Q) ≫
            Pi.π (fun n : ℕ ↦ Q.obj (op n)) n) ≫ a.app (op n) =
        θ ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
          Pi.π (fun n : ℕ ↦ T.obj (op n)) n)
    (hγ₀ : ∀ i : ℤ, γ.f i ≫ (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary Q)).v i (i - 1) (by omega) = 0)
    (hθ₀ : ∀ i : ℤ, θ.f i ≫ (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary T)).v i (i - 1) (by omega) = 0) :
    b ≫ (F.mapHomologicalComplex (.up ℤ)).map γ ≫ scalarRoosMap F Q ≫
        integralOperationsRoosMap a = θ := by
  apply cocone_ext
  · simp only [Category.assoc]
    erw [(IntegralAmbient.roosMap_coordinates a).1]
    rw [← Category.assoc (scalarRoosMap F Q), (podReindexingRoosCoordinates F Q).1]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π]
    dsimp only [CategoryTheory.Functor.comp_obj]
    erw [piComparison_comp_π_assoc]
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using hθ n
  · intro i
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    simp only [Category.assoc]
    erw [(IntegralAmbient.roosMap_coordinates a).2 i (i - 1) (by omega)]
    erw [← Category.assoc ((scalarRoosMap F Q).f i),
      (podReindexingRoosCoordinates F Q).2 i]
    change b.f i ≫ F.map (γ.f i) ≫ _ = _
    simp only [Category.assoc]
    erw [← F.map_comp_assoc, hγ₀ i, F.map_zero, zero_comp, comp_zero, hθ₀ i]

end GenericAugmentation

attribute [local irreducible] IntegralOnSlice.ordinaryPull

/-- Reindexing the strict quotient Roos complex along an isomorphism carries its
specified quotient-map/zero augmentation to the ordinary pullback completion chain.

Source: expanded DAG definition prose-10-21, clause 4, and
lem-weil-isomorphism-derived-pullback; Stacks Tags 03EL and 08TC.
(blueprint: lem-pur-isomorphism-ordinary-completion-chain).
Proof: the pro-etale base-change equivalence identifies ordinary module pullback
with reindexing, transporting the completed coefficient action by its finite
projection-normalized ring isomorphism. This equivalence preserves products and
identifies each scalar quotient with the finite pullback quotient; on an
adjunction-unit section both augmentations insert the unit scalar. These quotient
identifications commute with all transitions, since the coefficient maps commute
with quotient projections. Apply the product comparison in both coordinates of
the mapping cocone of 1 minus shift. Its inverse uses the inverse product and
quotient comparisons, so it is a chain isomorphism. The unshifted component of the
pulled-back augmentation is the product of the same quotient insertions, and the
shifted component is zero. The mapping-cocone component identity proves the stated
equality. This uses no completeness, flatness, constructibility, invertibility of
ell on the schemes, or nonemptiness assumption. -/
theorem isomorphismOrdinaryCompletionChain
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : Cx l E Y none) :
    ∃ e : (ordinaryComplexPull l E g).obj ((roos l E Y none).obj P) ≅
        (integralOperationsPullbackComplexFunctor l E g).obj P,
      (ordinaryComplexPull l E g).map (roosUnit l E Y none P) ≫ e.hom =
        ordinaryCompletionChain l E g P := by
  let F := inverseImageIntegralModules l E g
  obtain ⟨b₀, hb₀⟩ := isomorphismOrdinaryModuleNormalization l E g
  let : F.Additive := sectionwise_additive l E g
  let b : ordinaryComplexPull l E g ≅ trfInverseImageComplex l E g :=
    NatIso.mapHomologicalComplex b₀ (.up ℤ)
  let T := (tower l E Y none).obj P
  obtain ⟨a, ha⟩ := isomorphismOrdinaryQuotientTowerNormalization l E g P
  let : F.IsEquivalence := WeilConjectures.quotientModuleEquivalence g _
  let : IsIso (scalarRoosMap F T) := podReindexingRoosComparison F T
  let e := b.app ((roos l E Y none).obj P) ≪≫ asIso (scalarRoosMap F T) ≪≫
    integralOperationsRoosFunctor.mapIso a
  refine ⟨e, ?_⟩
  change (ordinaryComplexPull l E g).map (roosUnit l E Y none P) ≫
      b.hom.app ((roos l E Y none).obj P) ≫ scalarRoosMap F T ≫
        integralOperationsRoosFunctor.map a.hom = ordinaryCompletionChain l E g P
  rw [← Category.assoc ((ordinaryComplexPull l E g).map _)]
  erw [b.hom.naturality]
  simp only [Category.assoc]
  apply augmentedRoosMap F P ((ordinaryComplexPull l E g).obj P) T
    ((integralOperationsPullbackTowerFunctor l E g).obj P) (b.hom.app P) a.hom
    (roosUnit l E Y none P) (ordinaryCompletionChain l E g P)
  · intro n
    have hγ : roosUnit l E Y none P ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
          Pi.π (fun n : ℕ ↦ T.obj (op n)) n =
        ((augmentation l E Y none).app P).app (op n) := by
      rw [← Category.assoc, IntegralAmbient.roosUnit_fst]
      exact Pi.lift_comp_π _ _
    have hθ : ordinaryCompletionChain l E g P ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary
          ((integralOperationsPullbackTowerFunctor l E g).obj P)) ≫ Pi.π _ n =
        ((ordinaryQuotientAugmentation l E g).app P).app (op n) := by
      rw [← Category.assoc, ordinaryCompletionChain, CochainComplex.mappingCocone.lift_fst]
      exact Pi.lift_comp_π _ _
    rw [hγ, hθ]
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, b, NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplex_map_f]
    dsimp only [F, T, Functor.mapHomologicalComplex]
    exact isomorphismOrdinaryFiniteAugmentation l E g b₀ hb₀ P n a ha i
  · intro i
    exact CochainComplex.mappingCocone.lift_f_snd_v (scalarRoosBoundary T) _ _ _ i (i - 1)
      (by omega)
  · intro i
    exact CochainComplex.mappingCocone.lift_f_snd_v
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E g).obj P)) _ _ _ i (i - 1)
      (by omega)

end WeilConjectures.IntegralOnSlice
