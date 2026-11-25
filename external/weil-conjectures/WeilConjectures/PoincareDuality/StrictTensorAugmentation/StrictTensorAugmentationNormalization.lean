/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # Uniqueness of the strict tensor quotient augmentation

The two prescribed coordinates identify the constructed natural map uniquely.
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

/-- The prescribed pure-tensor product coordinates and zero shifted coordinate.
Source: rational purity proof Step 1
(blueprint: lem-pur-strict-tensor-augmentation-normalization). -/
def Normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (eta : (@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)) ⟶
        integralOperationsTensorComplexFunctor.{u, u} l E T) : Prop :=
    (∀ (P Q : CochainComplex (integralTowerModules.{u, u} l E T) ℤ)
        (p q : ℤ) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((eta.app (P, Q)).f (p + q) ≫
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
        (eta.app (P, Q)).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj
                (P, Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor.{u, u} l E T).obj (P, Q))))).v
                  i (i - 1) (by omega) = 0

private theorem map_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    Normalized l E T (map l E T) := by
  unfold Normalized
  exact coordinates l E T

private theorem normalized_unique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (eta eta' : (@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)) ⟶
        integralOperationsTensorComplexFunctor.{u, u} l E T)
    (h : Normalized l E T eta) (h' : Normalized l E T eta') : eta = eta' := by
  unfold Normalized at h h'
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply mappingCocone_hom_ext
  · apply Pi.hom_ext
    intro n
    apply HomologicalComplex.hom_ext
    intro k
    apply total_hom_ext l E T P Q k
    intro p q hpq U x y
    subst k
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      (h.1 P Q p q n U x y).trans (h'.1 P Q p q n U x y).symm
  · intro i
    exact (h.2 P Q i).trans (h'.2 P Q i).symm

/-- There is exactly one natural strict tensor map with these two coordinates.
Source: rational purity proof Step 1
(blueprint: lem-pur-strict-tensor-augmentation-normalization).
Proof: the constructed quotient unit has the prescribed coordinates. Compare two
normalized maps on pure generators in every degree and every product projection.
Pure-tensor and product extensionality identify the first coordinates; the second
coordinates vanish. Mapping-cocone and natural-transformation extensionality finish. -/
theorem existsUnique_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    ∃! eta : (@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)) ⟶
        integralOperationsTensorComplexFunctor.{u, u} l E T, Normalized l E T eta := by
  refine ⟨map l E T, map_normalized l E T, ?_⟩
  intro eta h
  exact normalized_unique l E T eta _ h (map_normalized l E T)

end WeilConjectures.StrictTensorAugmentation
