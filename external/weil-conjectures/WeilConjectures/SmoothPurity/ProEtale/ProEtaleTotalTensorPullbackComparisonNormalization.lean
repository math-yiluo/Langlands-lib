/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorComparisonAssociativity
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import all WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators

/-! # Normalized natural total tensor pullback comparison
Source: Stacks 03EL and 07A4; signed total tensor, 06YN.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.RingedForgetTensorTransposition
namespace WeilConjectures
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification coefficientTensorGenerator
attribute [local implicit_reducible] coefficientTotalTensor

private theorem canonical_total_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R') :
    let L := (proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ)
    ∃ e : (L.prod L) ⋙ coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R' ≅
        coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y) R ⋙ L,
      ∀ P Q, e.inv.app (P, Q) = (proEtaleTensorPullbackTotalIso f R R' c P Q).inv := by
  exact totalTensorPullbackIso_exists f R R' c

private theorem canonical_total_summand
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R')
    (ν : @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R) ⋙
        proEtaleRingModulePullback f R R' c ≅
      ((proEtaleRingModulePullback f R R' c).prod
        (proEtaleRingModulePullback f R R' c)) ⋙
        @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R'))
    (hμ : ∀ M N, ν.hom.app (M, N) =
      (proEtaleOrdinaryTensorPullback f R R' c M N).hom)
    (e : (((proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ)).prod
        ((proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R' ≅
      coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y) R ⋙
        (proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ))
    (he : ∀ P Q, e.inv.app (P, Q) =
      (proEtaleTensorPullbackTotalIso f R R' c P Q).inv) :
    let L := proEtaleRingModulePullback f R R' c
    ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
      (p q k : ℤ) (h : p + q = k),
      L.map (RingedForgetTensorTransposition.coefficientTensorSummand.{u + 1, u, u}
        (Scheme.ProEt.topology Y) R P Q p q k h) ≫
          (e.symm.hom.app (P, Q)).f k =
        ν.hom.app (P.X p, Q.X q) ≫
          RingedForgetTensorTransposition.coefficientTensorSummand.{u + 1, u, u}
            (Scheme.ProEt.topology X) R' ((L.mapHomologicalComplex (.up ℤ)).obj P)
              ((L.mapHomologicalComplex (.up ℤ)).obj Q) p q k h := by
  dsimp only
  intro P Q p q k h
  rw [Iso.symm_hom, he, hμ]
  exact geometric_total_ι f R R' c P Q p q k h

/-- Natural total pullback comparison with its component and summand normalizations.
Source: Stacks 03EL, 07A4 and 06YN
(blueprint: lem-pur-total-tensor-pullback-comparison-normalization).
Proof: the natural total comparison has the prescribed pointwise total isomorphisms.
Rewrite its components and the ordinary natural comparison by their specified
normalizations. The existing total-coproduct summand formula gives the equation.
This uses no associator, flatness, or derived localization. -/
theorem proEtaleTotalTensorPullbackComparisonNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R')
    (ν : @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R) ⋙
        proEtaleRingModulePullback f R R' c ≅
      ((proEtaleRingModulePullback f R R' c).prod
        (proEtaleRingModulePullback f R R' c)) ⋙
        @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R'))
    (hμ : ∀ M N, ν.hom.app (M, N) =
      (proEtaleOrdinaryTensorPullback f R R' c M N).hom)
 :
    let L := proEtaleRingModulePullback f R R' c
    ∃ e : (((proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ)).prod
        ((proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R' ≅
      coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y) R ⋙
        (proEtaleRingModulePullback f R R' c).mapHomologicalComplex (.up ℤ),
      (∀ P Q, e.inv.app (P, Q) = (proEtaleTensorPullbackTotalIso f R R' c P Q).inv) ∧
    ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
      (p q k : ℤ) (h : p + q = k),
      L.map (RingedForgetTensorTransposition.coefficientTensorSummand.{u + 1, u, u}
        (Scheme.ProEt.topology Y) R P Q p q k h) ≫
          (e.inv.app (P, Q)).f k =
        ν.hom.app (P.X p, Q.X q) ≫
          RingedForgetTensorTransposition.coefficientTensorSummand.{u + 1, u, u}
            (Scheme.ProEt.topology X) R' ((L.mapHomologicalComplex (.up ℤ)).obj P)
              ((L.mapHomologicalComplex (.up ℤ)).obj Q) p q k h := by
  obtain ⟨e, he⟩ := canonical_total_exists f R R' c
  refine ⟨e, he, ?_⟩
  exact canonical_total_summand f R R' c ν hμ e he

end WeilConjectures
