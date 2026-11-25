/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteSignedShifts
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift

/-! # Naturality of the finite signed tensor shift comparisons
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
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

private def nativeTensorShiftLeft {A : Type a} [Category.{b} A] [Preadditive A]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ P Q : CochainComplex A ℤ, CochainComplex.HasMapBifunctor P Q T] (r : ℤ) :
    ((shiftFunctor (CochainComplex A ℤ) r).prod (𝟭 _)) ⋙
        Functor.uncurry.obj T.map₂CochainComplex ≅
      Functor.uncurry.obj T.map₂CochainComplex ⋙ shiftFunctor _ r :=
  NatIso.ofComponents (fun P ↦ CochainComplex.mapBifunctorShift₁Iso P.1 P.2 T r) (by
    intro P Q f
    have h₁ : (T.map₂CochainComplex.map (f.1⟦r⟧')).app P.2 ≫
        (CochainComplex.mapBifunctorShift₁Iso Q.1 P.2 T r).hom =
      (CochainComplex.mapBifunctorShift₁Iso P.1 P.2 T r).hom ≫
        ((T.map₂CochainComplex.map f.1).app P.2)⟦r⟧' :=
      CochainComplex.mapBifunctorShift₁Iso_hom_naturality₁ f.1 P.2 T r
    have h₂ : (T.map₂CochainComplex.obj (Q.1⟦r⟧)).map f.2 ≫
        (CochainComplex.mapBifunctorShift₁Iso Q.1 Q.2 T r).hom =
      (CochainComplex.mapBifunctorShift₁Iso Q.1 P.2 T r).hom ≫
        ((T.map₂CochainComplex.obj Q.1).map f.2)⟦r⟧' :=
      CochainComplex.mapBifunctorShift₁Iso_hom_naturality₂ Q.1 f.2 T r
    change ((T.map₂CochainComplex.map (f.1⟦r⟧')).app P.2 ≫
        (T.map₂CochainComplex.obj (Q.1⟦r⟧)).map f.2) ≫
          (CochainComplex.mapBifunctorShift₁Iso Q.1 Q.2 T r).hom =
      (CochainComplex.mapBifunctorShift₁Iso P.1 P.2 T r).hom ≫
        ((T.map₂CochainComplex.map f.1).app P.2 ≫
          (T.map₂CochainComplex.obj Q.1).map f.2)⟦r⟧'
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, ← Functor.map_comp])

private def nativeTensorShiftRight {A : Type a} [Category.{b} A] [Preadditive A]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ P Q : CochainComplex A ℤ, CochainComplex.HasMapBifunctor P Q T] (r : ℤ) :
    ((𝟭 _).prod (shiftFunctor (CochainComplex A ℤ) r)) ⋙
        Functor.uncurry.obj T.map₂CochainComplex ≅
      Functor.uncurry.obj T.map₂CochainComplex ⋙ shiftFunctor _ r :=
  NatIso.ofComponents (fun P ↦ CochainComplex.mapBifunctorShift₂Iso P.1 P.2 T r) (by
    intro P Q f
    have h₁ : (T.map₂CochainComplex.map f.1).app (P.2⟦r⟧) ≫
        (CochainComplex.mapBifunctorShift₂Iso Q.1 P.2 T r).hom =
      (CochainComplex.mapBifunctorShift₂Iso P.1 P.2 T r).hom ≫
        ((T.map₂CochainComplex.map f.1).app P.2)⟦r⟧' :=
      CochainComplex.mapBifunctorShift₂Iso_hom_naturality₁ f.1 P.2 T r
    have h₂ : (T.map₂CochainComplex.obj Q.1).map (f.2⟦r⟧') ≫
        (CochainComplex.mapBifunctorShift₂Iso Q.1 Q.2 T r).hom =
      (CochainComplex.mapBifunctorShift₂Iso Q.1 P.2 T r).hom ≫
        ((T.map₂CochainComplex.obj Q.1).map f.2)⟦r⟧' :=
      CochainComplex.mapBifunctorShift₂Iso_hom_naturality₂ Q.1 f.2 T r
    change ((T.map₂CochainComplex.map f.1).app (P.2⟦r⟧) ≫
        (T.map₂CochainComplex.obj Q.1).map (f.2⟦r⟧')) ≫
          (CochainComplex.mapBifunctorShift₂Iso Q.1 Q.2 T r).hom =
      (CochainComplex.mapBifunctorShift₂Iso P.1 P.2 T r).hom ≫
        ((T.map₂CochainComplex.map f.1).app P.2 ≫
          (T.map₂CochainComplex.obj Q.1).map f.2)⟦r⟧'
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, ← Functor.map_comp])

private abbrev pairOf {C : Type*} [Category C] (S : C ⥤ C) (right : Bool) :
    C × C ⥤ C × C :=
  if right then (𝟭 C).prod S else S.prod (𝟭 C)

private abbrev pairShift (C : Type*) [Category C] [HasShift C ℤ] (r : ℤ) (right : Bool) :
    C × C ⥤ C × C :=
  pairOf (shiftFunctor C r) right

private def pairShiftComparison {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    (r : ℤ) (right : Bool) :
    pairShift C r right ⋙ F.prod F ≅ F.prod F ⋙ pairShift D r right := by
  cases right
  · exact NatIso.ofComponents
      (fun P ↦ Iso.prod ((F.commShiftIso r).app P.1) (Iso.refl _)) (by
        intro P Q f
        ext
        · exact (F.commShiftIso r).hom.naturality f.1
        · simp [pairShift, pairOf])
  · exact NatIso.ofComponents
      (fun P ↦ Iso.prod (Iso.refl _) ((F.commShiftIso r).app P.2)) (by
        intro P Q f
        ext
        · simp [pairShift, pairOf]
        · exact (F.commShiftIso r).hom.naturality f.2)

private def composeShiftIso {C D B A : Type*}
    [Category C] [Category D] [Category B] [Category A]
    (F : C ⥤ D) (R : D ⥤ B) (Q : B ⥤ A)
    (s : C ⥤ C) (S : D ⥤ D) (H : B ⥤ B) (J : A ⥤ A)
    (e : s ⋙ F ≅ F ⋙ S) (f : S ⋙ R ≅ R ⋙ H) (g : H ⋙ Q ≅ Q ⋙ J) :
    s ⋙ (F ⋙ R ⋙ Q) ≅ (F ⋙ R ⋙ Q) ⋙ J :=
  isoWhiskerRight (isoWhiskerRight e R) Q ≪≫
    isoWhiskerRight (isoWhiskerLeft F f) Q ≪≫
      isoWhiskerLeft (F ⋙ R) g

attribute [local instance] integralOperationsFiniteHasMap

private def finiteTensorShift (W : Scheme.{u}) (n : ℕ) (r : ℤ) (right : Bool) :
    pairShift (CochainComplex (integralTowerModules l E W) ℤ) r right ⋙
        integralOperationsTensorLevel l E W n ≅
      integralOperationsTensorLevel l E W n ⋙ shiftFunctor _ r := by
  letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  letI := integralCoefficientAbSheafify.{u, u} W
  letI := integralCoefficientAbLocallyBijective.{u, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)
  letI : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  letI : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf l E W n)
  let F := unrestrictedIntegralFiniteComplex l E W n
  let R := integralOperationsRestrict l E W n
  have : R.CommShift ℤ := by
    dsimp [R, integralOperationsRestrict]
    infer_instance
  let T := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)
  let B := Functor.uncurry.obj T.map₂CochainComplex
  let β : pairShift _ r right ⋙ B ≅ B ⋙ shiftFunctor _ r := by
    cases right
    · exact nativeTensorShiftLeft T r
    · exact nativeTensorShiftRight T r
  exact composeShiftIso (F.prod F) B R (pairShift _ r right) (pairShift _ r right)
    (shiftFunctor _ r) (shiftFunctor _ r) (pairShiftComparison F r right) β
    (R.commShiftIso r)

private theorem finiteTensorShift_left (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) :
    (finiteTensorShift l E W n r false).hom.app (P, Q) =
      (podTensorFiniteShiftLeft l E W n P Q r).hom := by
  rfl

private theorem finiteTensorShift_right (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) :
    (finiteTensorShift l E W n r true).hom.app (P, Q) =
      (podTensorFiniteShiftRight l E W n P Q r).hom := by
  rfl

attribute [local irreducible] finiteTensorShift podTensorFiniteShiftLeft podTensorFiniteShiftRight
  integralOperationsTensorLevel

/-- The fixed finite tensor shift maps are natural in both input complexes.
Source: Mathlib's `mapBifunctorShift₁Iso` and `mapBifunctorShift₂Iso`, their
naturality lemmas, and Stacks 011G and 07A4.
(blueprint: lem-pod-tensor-finite-shift-naturality).

Proof: package the native tensor shift in each variable as a natural isomorphism
on pairs. Whisker with ordinary coefficient reduction and scalar restriction,
using their shift comparisons. The resulting components are definitionally the
specified finite shifts, so their naturality equations are the desired ones. -/
theorem podTensorFiniteShift_naturality (W : Scheme.{u}) (n : ℕ)
    {P Q : CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ} (f : P ⟶ Q) (r : ℤ) :
    ((integralOperationsTensorLevel l E W n).map (Prod.mkHom (f.1⟦r⟧') f.2) ≫
        (podTensorFiniteShiftLeft l E W n Q.1 Q.2 r).hom =
      (podTensorFiniteShiftLeft l E W n P.1 P.2 r).hom ≫
        ((integralOperationsTensorLevel l E W n).map f)⟦r⟧') ∧
    ((integralOperationsTensorLevel l E W n).map (Prod.mkHom f.1 (f.2⟦r⟧')) ≫
        (podTensorFiniteShiftRight l E W n Q.1 Q.2 r).hom =
      (podTensorFiniteShiftRight l E W n P.1 P.2 r).hom ≫
        ((integralOperationsTensorLevel l E W n).map f)⟦r⟧') := by
  constructor
  · have h := (finiteTensorShift l E W n r false).hom.naturality f
    change (integralOperationsTensorLevel l E W n).map (Prod.mkHom (f.1⟦r⟧') f.2) ≫
        (finiteTensorShift l E W n r false).hom.app Q =
      (finiteTensorShift l E W n r false).hom.app P ≫
        ((integralOperationsTensorLevel l E W n).map f)⟦r⟧' at h
    rw [finiteTensorShift_left, finiteTensorShift_left] at h
    exact h
  · have h := (finiteTensorShift l E W n r true).hom.naturality f
    change (integralOperationsTensorLevel l E W n).map (Prod.mkHom f.1 (f.2⟦r⟧')) ≫
        (finiteTensorShift l E W n r true).hom.app Q =
      (finiteTensorShift l E W n r true).hom.app P ≫
        ((integralOperationsTensorLevel l E W n).map f)⟦r⟧' at h
    rw [finiteTensorShift_right, finiteTensorShift_right] at h
    exact h

end WeilConjectures
