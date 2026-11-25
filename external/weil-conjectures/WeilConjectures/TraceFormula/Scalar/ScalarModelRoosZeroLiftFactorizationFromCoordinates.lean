/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftUniqueness
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosCounitNormalization

/-! # Factorization from normalized scalar Roos coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedScalarChangeData

attribute [local implicit_reducible] completedOrdinaryScalarComplex integralOperationsRoos
  completedDerivedScalarExtension completedScalarCounit completedOrdinaryScalarExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

/-- Naturality of the universal cochain counit, without expanding scalar-change data.
Source: Stacks 06YY; the homotopy counit's naturality square. -/
private theorem scalarCounit_natural
    {A B : CochainComplex (integralTowerModules l L X) ℤ} (g : A ⟶ B) :
    (completedDerivedScalarExtension l L F j X).map (DerivedCategory.Q.map g) ≫
        completedScalarCounit l L F j X B =
      completedScalarCounit l L F j X A ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l L F j X).map g) := by
  dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]
  with_unfolding_all
    exact homotopyCounit_naturality
      (completedOrdinaryScalarExtension.{u, u} l L F j X)
      (completedDerivedScalarExtension.{u, u} l L F j X)
      ((completedScalarChangeData.{u, u} l L F j X).choose_spec.choose_spec.choose_spec
        |>.choose_spec.2.2.choose_spec.choose) g

/-- The normalized scalar realization factors a strict zero-shift lift satisfying the
quotient-coordinate predicate.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-factorization-from-coordinates)

Proof in words: assemble the levelwise scalar extension maps from the core into a
natural transformation a, and form k by applying ordinary scalar extension to f,
then scalarRoosMap, then the Roos map of a. Its shifted coordinate is zero by hf.
Its first coordinate on tensor generators is the prescribed quotient tensor map.
The coordinate predicate and nested tensor extensionality identify h with k.
Apply the whole-system scalar counit normalization before inserting f, use the
naturality of the universal scalar counit, and substitute the equality h = k.

STATEMENT-DISPUTED: the former signature omitted hf on f; it is repaired here.
First-product coordinates alone do not control the shifted Roos summand. The
corrected hypothesis is already supplied by the unchanged outer existence theorem.
-/
theorem scalarModelRoosZeroLift_factorization_from_coordinates
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D)
    (hh : scalarModelRoosZeroLiftZero l E L F ι j X SL P D h)
    (hcoord : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h) :
    ((completedDerivedScalarExtension l L F j X).map
          (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
        (completedScalarComparison l L F j X).app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        b.realization.hom.app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonDerivedSequenceScalar l L F j X).map
            (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
        (integralComparisonRoosBridge l F X ρF _).hom =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h) := by
  let C := ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D
  let C' := ((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
    (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
      (.up ℤ)).obj D)
  let G := completedOrdinaryScalarExtension l L F j X
  let T := G.mapHomologicalComplex (.up ℤ)
  let a : C.asFunctor ⋙ T ⟶ C'.asFunctor :=
    { app n := ScalarRoosLiftProof.levelChange l L F j X D n.unop
      naturality n m t := ScalarRoosLiftProof.levelChange_horizontal l L F j X D t }
  let r := scalarRoosMap G C.asFunctor ≫ integralOperationsRoosMap a
  let k : scalarModelRoosZeroLiftType l E L F ι j X SL P D := T.map f ≫ r
  have hk (i : ℤ) : k.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C'.asFunctor)).v
        i (i - 1) (by omega) = 0 := by
    dsimp only [k, r, HomologicalComplex.comp_f, completedOrdinaryScalarComplex,
      Functor.mapHomologicalComplex_map_f]
    simp only [Category.assoc]
    rw [(scalarRoosTowerCoordinates a).2 i (i - 1) (by omega),
      ← Category.assoc ((scalarRoosMap G C.asFunctor).f i),
      (scalarRoosCoordinates G C.asFunctor).2 i]
    simp only [Category.assoc]
    change G.map (f.f i) ≫ G.map _ ≫ _ = 0
    rw [← G.map_comp_assoc, hf i, G.map_zero, zero_comp]
  have kp (n : ℕ) : k ≫
      CochainComplex.mappingCocone.fst (scalarRoosBoundary C'.asFunctor) ≫
        Pi.π (fun m : ℕ ↦ C'.asFunctor.obj (op m)) n =
      T.map (f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) ≫
        Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n) ≫ a.app (op n) := by
    dsimp only [k, r]
    simp only [Category.assoc]
    rw [reassoc_of% (scalarRoosTowerCoordinates a).1]
    simp only [Pi.map_π]
    rw [reassoc_of% (scalarRoosCoordinates G C.asFunctor).1]
    simp only [Functor.map_comp, Category.assoc]
    change T.map f ≫ T.map _ ≫ piComparison T (fun m : ℕ ↦ C.asFunctor.obj (op m)) ≫
      Pi.π (fun m : ℕ ↦ T.obj (C.asFunctor.obj (op m))) n ≫ a.app (op n) = _
    rw [reassoc_of% (piComparison_comp_π T (fun m : ℕ ↦ C.asFunctor.obj (op m)) n)]
  have hcoordk : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f k := by
    intro n i U s t x y hxy
    change ((k ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C'.asFunctor) ≫
      Pi.π (fun m : ℕ ↦ C'.asFunctor.obj (op m)) n).f i).val.app U _ = _
    rw [kp n]
    change ((ScalarRoosLiftProof.scalarComponentNat l L F j X n).app (D.X i)).val.app U
      ((G.map ((f ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary C.asFunctor) ≫
          Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n).f i)).val.app U _) = _
    rw [completedScalarTensorSection_naturality]
    change ((ScalarRoosLiftProof.scalarComponentNat l L F j X n).app (D.X i)).val.app U
      (completedScalarTensorSection l L F j X _ U s
        (((f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) ≫
          Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n).f i).val.app U
            (completedScalarTensorSection l E L ι X _ U t x))) = _
    rw [show (((f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) ≫
      Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n).f i).val.app U
        (completedScalarTensorSection l E L ι X _ U t x)) =
      integralComparisonRestrictedSection l L X (D.X i) n U y from hxy]
    exact ScalarRoosLiftProof.scalarComponent_tensor.{u} l L F j X (D.X i) n U s y
  have hc : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (P.obj.X i).val.obj U),
      ((h.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        C'.asFunctor)).f i ≫ (Pi.π (fun m : ℕ ↦ C'.asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X _ U s
          (completedScalarTensorSection l E L ι X _ U t x)) =
      ((k.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        C'.asFunctor)).f i ≫ (Pi.π (fun m : ℕ ↦ C'.asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X _ U s
          (completedScalarTensorSection l E L ι X _ U t x)) := by
    intro n i U s t x
    let z := ((f.f i ≫ (CochainComplex.mappingCocone.fst
      (scalarRoosBoundary C.asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n).f i).val.app U)
          (completedScalarTensorSection l E L ι X _ U t x)
    let y : (D.X i).val.obj (op (n, U.unop)) :=
      cast (integralComparisonRestrictedSectionType l L X (D.X i) n U) z
    have hy : z = integralComparisonRestrictedSection l L X (D.X i) n U y := by
      dsimp only [y, integralComparisonRestrictedSection]
      simp only [cast_cast, cast_eq]
    exact (hcoord n i U s t x y hy).trans (hcoordk n i U s t x y hy).symm
  have hq := scalarModelRoosZeroLift_uniqueness l E L F ι j X P D h k hh hk hc
  have hn := scalarModelRoos_counit_normalization.{u} l L F j X SL ρL ρF b D a
    (fun n i U s x ↦
      ScalarRoosLiftProof.scalarComponent_tensor.{u} l L F j X (D.X i) n U s x)
  have hε : (completedDerivedScalarExtension l L F j X).map (DerivedCategory.Q.map f) ≫
      completedScalarCounit l L F j X (integralOperationsRoos C.asFunctor) =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫
          DerivedCategory.Q.map (T.map f) := by
    exact scalarCounit_natural l L F j X f
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc, hε, Category.assoc, ← Functor.map_comp]
  exact congrArg (completedScalarCounit l L F j X
    ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ ·) hq.symm

end WeilConjectures
