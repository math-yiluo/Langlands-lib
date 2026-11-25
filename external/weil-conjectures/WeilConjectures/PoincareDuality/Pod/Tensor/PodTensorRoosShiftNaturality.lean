/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorSignedShiftTowers
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRightShiftNaturality
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus

/-! # Signed tensor shifts on good representatives

Compose the fixed strict tower comparisons, the supplied signed Roos comparison,
and localization, retaining their precise components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section RoosNaturality
attribute [local instance] CategoryTheory.RoosConeCalculus.levelCommShift
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

private theorem signedRoos_unique (ρ σ : PodSignedRoosShift A)
    (hρ : ρ.Laws) (hσ : σ.Laws) (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    (ρ.comparison C r).hom = (σ.comparison C r).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  have hf := congrArg (fun f ↦ f.f i) ((hρ.1 C r).trans (hσ.1 C r).symm)
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at hf
  have hs := (hρ.2 C r i).trans (hσ.2 C r i).symm
  have hid := CochainComplex.mappingCocone.id_X (podRoosBoundary C)
    (i + r) (i - 1 + r) (by omega)
  have hleft := congrArg (fun z ↦ (ρ.comparison C r).hom.f i ≫ z) hid
  have hright := congrArg (fun z ↦ (σ.comparison C r).hom.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hleft hright
  rw [hf, hs] at hleft
  exact (Category.comp_id _).symm.trans
    (hleft.symm.trans (hright.trans (Category.comp_id _)))

/-- The two prescribed cone-coordinate laws force naturality of the Roos shift.
Source: Stacks 011G and 0941 (blueprint: lem-pod-tensor-roos-shift-naturality).
Proof: identify the supplied maps with the native mapping-cocone comparison by
its two coordinates, then apply the native Roos commShift naturality. -/
theorem podTensorSignedRoosShift_naturality (ρ : PodSignedRoosShift A) (hρ : ρ.Laws)
    {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : C ⟶ D) (r : ℤ) :
    integralOperationsRoosFunctor.map (whiskerRight f (shiftFunctor _ r)) ≫
        (ρ.comparison D r).hom =
      (ρ.comparison C r).hom ≫ (integralOperationsRoosFunctor.map f)⟦r⟧' := by
  have hn : (podNativeRoosShift (A := A)).Laws := by
    constructor
    · intro C r
      apply HomologicalComplex.hom_ext
      intro i
      have h := CategoryTheory.RoosConeCalculus.roosShift_v (towerAsComplex C) r i
      change (podNativeRoosShift.comparison C r).hom.f i ≫
          𝟙 _ ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C)).f (i + r) =
        (CochainComplex.mappingCocone.fst (podRoosBoundary (podShiftTower C r))).f i ≫
          (ProductShift.productShiftIso
            (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
            (towerAsComplex C) r).hom.f i at h
      simpa only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
        Category.id_comp, podProductShift] using h
    · intro C r i
      have h := CategoryTheory.RoosConeCalculus.roosShift_u (towerAsComplex C) r i
      change (podNativeRoosShift.comparison C r).hom.f i ≫ 𝟙 _ ≫
          (CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
            (i + r) (i - 1 + r) (by omega) =
        r.negOnePow • ((CochainComplex.mappingCocone.snd
          (podRoosBoundary (podShiftTower C r))).v i (i - 1) (by omega) ≫
          (ProductShift.productShiftIso
            (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
            (towerAsComplex C) r).hom.f (i - 1)) at h
      simpa only [Category.id_comp, podProductShift] using h
  rw [signedRoos_unique ρ podNativeRoosShift hρ hn,
    signedRoos_unique ρ podNativeRoosShift hρ hn]
  let g : towerAsComplex C ⟶ towerAsComplex D :=
    { f := fun i ↦
        { app := fun n ↦ (f.app n).f i
          naturality := fun _ _ a ↦ congrArg (fun z ↦ z.f i) (f.naturality a) }
      comm' := fun i j _ ↦ by ext n; exact (f.app n).comm i j }
  have he {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (a : N ⟶ N') :
      integralOperationsRoosMap
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a) =
        CategoryTheory.roosF.map a := by
    unfold integralOperationsRoosMap
    rw [CategoryTheory.RoosConeCalculus.cofiberMap_eq_coneMap
      _ _ _ _ (integralOperationsRoos_square _)]
    rfl
  have h := (Functor.commShiftIso CategoryTheory.roosF
    (self := CategoryTheory.RoosConeCalculus.roosCommShift) r).hom.naturality g
  dsimp only [Functor.comp_map] at h
  rw [← he (g⟦r⟧'), ← he g] at h
  exact h

/-- The supplied signed Roos comparison gives a natural shift isomorphism.
Source: Stacks 011G and 0941 (blueprint: lem-pod-tensor-roos-shift-naturality).
-/
def podTensorRoosShiftIso {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (ρ : PodSignedRoosShift A) (hρ : ρ.Laws) (r : ℤ) :
    podTensorTowerShift r ⋙ integralOperationsRoosFunctor (A := A) ≅
      integralOperationsRoosFunctor (A := A) ⋙ shiftFunctor _ r :=
  NatIso.ofComponents (fun C ↦ ρ.comparison C r)
    (fun f ↦ podTensorSignedRoosShift_naturality ρ hρ f r)

end RoosNaturality

end WeilConjectures
