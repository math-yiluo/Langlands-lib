/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # The strict tensor quotient augmentation

The constructed map retains both coordinates of the strict Roos complex.
Source: Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictTensorAugmentation
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoos integralOperationsRoosFunctor
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
  coefficientTotalTensor
attribute [local implicit_reducible] IntegralOnSlice.ring IntegralOnSlice.restrict
  IntegralOnSlice.topology IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.roos IntegralAmbient.tensorTower

attribute [local irreducible] map IntegralAmbient.tensorOperationUnit
  IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  integralOperationsTotalTensorSection unrestrictedIntegralTensorSection

private theorem product_projection {A : Type*} [Category A]
    {F G : ℕ → A} [HasProduct F] [HasProduct G] {X : A}
    (a : ∀ n, X ⟶ F n) (b : ∀ n, F n ⟶ G n) (n : ℕ) :
    (Pi.lift a ≫ Limits.Pi.map b) ≫ Pi.π G n = a n ≫ b n := by
  simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc]

/-- The product coordinates are the tensors of quotient units, and the second coordinate
is zero. Source: Stacks 03EL, 07A4 and 0941
(blueprint: lem-pur-strict-tensor-augmentation-coordinates).
Proof: project the coordinate equation for tensorOperationUnit to the nth factor.
The slice augmentation sends z to 1 tensor z. The normalized tensorTowerIso sends
1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). Its Roos image preserves
both coordinates and therefore preserves the identically zero second coordinate. -/
theorem coordinates (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    (∀ (P Q : CochainComplex (integralTowerModules.{u, u} l E T) ℤ)
        (p q : ℤ) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((((map l E T).app (P, Q)).f (p + q) ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj
                (P, Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj (P, Q))))).f (p + q) ≫
          (Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj
            (P, Q)).obj (op j)) n).f (p + q)).val.app U)
            (@coefficientTensorGenerator.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
              (completedIntegralCommRingSheafUnrestricted.{u, u} l E T) P Q p q (p + q) rfl U x y) =
          integralOperationsTotalTensorSection.{u, u} l E T n P Q p q U
            (unrestrictedIntegralTensorSection.{u, u} l E T n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection.{u, u} l E T n (Q.X q) U 1 y)) ∧
      ∀ (P Q : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ),
        ((map l E T).app (P, Q)).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj
                (P, Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj (P, Q))))).v
                  i (i - 1) (by omega) = 0 := by
  let : HasLimitsOfShape (Discrete ℕ) (integralTowerModules.{u, u} l E T) :=
    (integralOperationsCountableProducts.{u, u} l E T).out ℕ
  let : HasLimitsOfShape (Discrete ℕ)
      (CochainComplex (integralTowerModules.{u, u} l E T) ℤ) :=
    HomologicalComplex.instHasLimitsOfShape
  let : HasLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Cx.{u, u} l E T none) :=
    inferInstanceAs (HasLimitsOfShape (Discrete ℕ)
      (CochainComplex (integralTowerModules.{u, u} l E T) ℤ))
  constructor
  · intro P Q p q n U x y
    let Z := (P, Q)
    let C := (integralOperationsTensorTowerFunctor.{u, u} l E T).obj Z
    have h := congrArg
      (fun f ↦ f ≫ Pi.π (fun j ↦ C.obj (op j)) n)
      (IntegralAmbient.tensorOperationUnit_coordinates.{u, u} l E T P Q).1
    have hπ := product_projection
      (A := CochainComplex (integralTowerModules.{u, u} l E T) ℤ)
      (fun j ↦ ((IntegralOnSlice.augmentation.{u, u} l E T none).app
        ((@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
          (integralOperationsAbSheafify.{u, u} T)
          (integralOperationsAbLocallyBijective.{u, u} T)
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)).obj Z)).app (op j))
      (fun j ↦ ((IntegralAmbient.tensorTowerIso.{u, u} l E T).hom.app Z).app (op j)) n
    have h' := h.trans hπ
    let z := @coefficientTensorGenerator.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      P Q p q (p + q) rfl U x y
    have hh := congrArg (fun f ↦ (f.f (p + q)).val.app U z) h'
    simp only [HomologicalComplex.comp_f, Category.assoc] at hh
    rw [map_app]
    erw [hh]
    erw [HomologicalComplex.comp_f]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    unfold IntegralOnSlice.augmentation
    erw [(IntegralOnSlice.augmentation_existsUnique.{u, u} l E T none).exists.choose_spec]
    unfold IntegralAmbient.tensorTowerIso
    exact (IntegralAmbient.tensorTowerModel.{u, u} l E T).exists.choose_spec P Q n p q U 1 x y
  · intro P Q i
    rw [map_app]
    exact (IntegralAmbient.tensorOperationUnit_coordinates.{u, u} l E T P Q).2 i (i - 1) (by omega)

/-- Pure total tensors determine a morphism from the ordinary total tensor.
Source: Stacks 03EK and 06YN
(blueprint: lem-pur-strict-tensor-augmentation-coordinates).
Proof: first use the direct-sum universal property, then tensor extensionality. -/
theorem total_hom_ext (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E T) ℤ) (k : ℤ)
    (H : integralTowerModules l E T)
    {f g : (((@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T))).obj (P, Q)).X k ⟶ H}
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (U : T.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      f.val.app U (@coefficientTensorGenerator.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
        (integralOperationsAbSheafify.{u, u} T)
        (integralOperationsAbLocallyBijective.{u, u} T)
        (completedIntegralCommRingSheafUnrestricted l E T) P Q p q k hpq U x y) =
      g.val.app U (@coefficientTensorGenerator.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
        (integralOperationsAbSheafify.{u, u} T)
        (integralOperationsAbLocallyBijective.{u, u} T)
        (completedIntegralCommRingSheafUnrestricted l E T) P Q p q k hpq U x y)) :
    f = g := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} T.ProEt
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E T)
  unfold coefficientTotalTensor at f g ⊢
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E T) (P.X p) (Q.X q) H
  intro U x y
  exact h p q hpq U x y

/-- Both coordinates determine a morphism into the Roos mapping cocone.
Source: Stacks 08TC (blueprint: lem-pur-strict-tensor-augmentation-coordinates).
Proof: the sum of the two coordinate projection-inclusion composites is the identity. -/
theorem mappingCocone_hom_ext {A : Type*} [Category A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L)
    {f g : M ⟶ CochainComplex.mappingCocone φ}
    (hfst : f ≫ CochainComplex.mappingCocone.fst φ =
      g ≫ CochainComplex.mappingCocone.fst φ)
    (hsnd : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun a ↦ a.f i) hfst
  have he := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by rw [he]
    _ = g.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc]
      rw [show f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
        g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i from h, hsnd i]
    _ = g.f i := by rw [he, Category.comp_id]

end WeilConjectures.StrictTensorAugmentation
