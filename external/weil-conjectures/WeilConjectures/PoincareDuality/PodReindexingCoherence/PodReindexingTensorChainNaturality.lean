/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreTensorData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! Naturality of the pure-normalized reindexing comparison on total tensor complexes.
(blueprint: lem-pod-reindexing-tensor-chain-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local instance 1000001] cachedCompose

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] podReindexingCoefficient podReindexingHomModel
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientTotalTensor coefficientTensorGenerator SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  CoefficientClosedStructure.tensor

/-- The pure-normalized tensor-chain comparison is natural in both inputs.
Source: blueprint dual-Tate compatibility, Steps 1 and 2.
(blueprint: lem-pod-reindexing-tensor-chain-naturality).

Proof: cancel the invertible chain comparison and test each degree on every
pure-tensor summand. Its inverse sends a target generator to the corresponding
source generator, by the stated pure normalization. Mapping that source generator
and then applying the comparison gives the same generator as first applying the
comparison and then mapping the two factors. Total-tensor generator extensionality
finishes the equation. This also covers zero complexes and empty sites.
-/
theorem tensor_chain_naturality {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (t : ComparisonCoreTensorData l E g s SX SY TX TY)
    {P L P' L' : K l E Y s} (f : P ⟶ P') (h : L ⟶ L') :
    (podReindexingComplexFunctor l E g s).map ((total l E Y s).map (f, h)) ≫
        (t.tensorChain P' L').hom =
      (t.tensorChain P L).hom ≫ (total l E X s).map
        ((podReindexingComplexFunctor l E g s).map f,
          (podReindexingComplexFunctor l E g s).map h) := by
  apply (cancel_epi (t.tensorChain P L).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  ext n : 1
  apply ScalarHomTensor.total_pure_hom_ext (J := ProEt.topology X)
    (R := podReindexingRing l E X s)
  intro p q hpq U x y
  let z := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (podReindexingRing l E Y s) P L p q n hpq
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x y
  have hcancel := congrArg (fun a ↦ (a.f n).val.app U z)
    (t.tensorChain P L).hom_inv_id
  have hi := congrArg
    (fun z ↦ (((t.tensorChain P L).inv.f n).val.app U) z)
    (t.tensorChain_pure P L p q n hpq U.unop x y)
  have hi' : (((t.tensorChain P L).inv.f n).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj L) p q n hpq U x y) = z :=
    hi.symm.trans hcancel
  -- Apply the generator equations directly, without searching through coefficient transports.
  refine (congrArg (fun w ↦ (((t.tensorChain P' L').hom.f n).val.app U)
    ((((total l E Y s).map (f, h)).f n).val.app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) w)) hi').trans ?_
  refine (congrArg (fun w ↦ (((t.tensorChain P' L').hom.f n).val.app U) w)
    (ScalarHomTensor.tensor_generator_map (J := ProEt.topology Y)
      (R := podReindexingRing l E Y s) f h p q n hpq
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x y)).trans ?_
  refine (t.tensorChain_pure P' L' p q n hpq U.unop
    ((f.f p).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x)
    ((h.f q).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) y)).trans ?_
  exact (ScalarHomTensor.tensor_generator_map (J := ProEt.topology X)
    (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E g s).map f)
    ((podReindexingComplexFunctor l E g s).map h) p q n hpq U x y).symm

end WeilConjectures.PodReindexingCoherence
