/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Retract

/-! # Forgetting native K-flat complexes by an orbit-sum retract

Source: Stacks 06YS, and the exact integer-orbit induction argument in step 2 of
native Weil tensor transport. No termwise flatness is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor Opposite WeilConjectures

section OrbitRetract
variable {C : Type v} [Category.{w} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{w} C]

private instance freeAdditive : (IsoAlgebra.Free.functor F).Additive :=
  (IsoAlgebra.Free.adjunction F).left_adjoint_additive

private instance freeExact : (IsoAlgebra.Free.functor F).PreservesHomology := by
  let := (IsoAlgebra.Free.adjunction F).isLeftAdjoint
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

private def orbitRetract (N : CochainComplex C ℤ) :
    Retract N (((IsoAlgebra.forget F).mapHomologicalComplex (.up ℤ)).obj
      (((IsoAlgebra.Free.functor F).mapHomologicalComplex (.up ℤ)).obj N)) where
  i :=
    { f := fun n ↦ Sigma.ι (IsoAlgebra.Free.obj F (N.X n)) 0
      comm' := by
        intro n m hnm
        change Sigma.ι (IsoAlgebra.Free.obj F (N.X n)) 0 ≫
            Limits.Sigma.map (IsoAlgebra.Free.objMap F (N.d n m)) =
          N.d n m ≫ Sigma.ι (IsoAlgebra.Free.obj F (N.X m)) 0
        simp [IsoAlgebra.Free.objMap, IsoAlgebra.Free.posMap] }
  r :=
    { f := fun n ↦ Sigma.desc (Pi.single (0 : ℤ) (𝟙 (N.X n)))
      comm' := by
        intro n m hnm
        apply Sigma.hom_ext
        intro j
        change Sigma.ι _ j ≫ Sigma.desc _ ≫ N.d n m =
          Sigma.ι (IsoAlgebra.Free.obj F (N.X n)) j ≫
            Limits.Sigma.map (IsoAlgebra.Free.objMap F (N.d n m)) ≫ Sigma.desc _
        simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
        by_cases hj : j = 0
        · subst j
          simp only [Pi.single_eq_same, IsoAlgebra.Free.objMap_zero]
          exact (Category.id_comp (N.d n m)).trans (Category.comp_id (N.d n m)).symm
        · simp [Pi.single_eq_of_ne hj] }
  retract := by
    ext n
    exact Sigma.ι_comp_desc _ _

private theorem isZero_of_retract {D : Type*} [Category D] [HasZeroMorphisms D]
    {Y Z : D} (r : Retract Y Z) (h : IsZero Z) : IsZero Y := by
  apply (IsZero.iff_id_eq_zero _).mpr
  calc
    𝟙 Y = r.i ≫ r.r := r.retract.symm
    _ = 0 := by rw [h.eq_of_tgt r.i 0, zero_comp]

end OrbitRetract

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- A native acyclic-test K-flat complex stays K-flat after forgetting Frobenius.

Source: Stacks 06YS; native tensor transport, step 2.
(blueprint: lem-sf-native-weil-tensor-forget-kflat).

Proof: for an ordinary acyclic test N, take the explicit free Frobenius complex,
the integer sum of its translates. This functor is additive and exact: each
translate is an equivalence, coproducts preserve monomorphisms in the Grothendieck
heart, and the free adjunction preserves cokernels. The native K-flat hypothesis
makes its tensor with P acyclic. Forgetting is exact, so the supplied chain
comparison makes the ordinary tensor with the underlying free complex acyclic.
The inclusion of the zero translate and the projection killing every other
translate are chain maps splitting N off that underlying complex. Tensoring
these maps with P gives a retract, and homology preserves the splitting. A
retract of a zero homology object is zero. This works for every unbounded N,
and also for the zero module and empty sites. -/
theorem native_weil_tensor_forget_kflat
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
            (.up ℤ)).obj Q))
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) :
    NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  intro N hN
  let F := WeilSheaf.frobeniusPullback k₀ l X
  let U := IsoAlgebra.forget F
  let I := IsoAlgebra.Free.functor F
  have hI : ((I.mapHomologicalComplex (.up ℤ)).obj N).Acyclic := hN.map I
  have ht := (hP _ hI).map U
  have ho : (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      ((U.mapHomologicalComplex (.up ℤ)).obj P)
      ((U.mapHomologicalComplex (.up ℤ)).obj
        ((I.mapHomologicalComplex (.up ℤ)).obj N))).Acyclic := by
    intro n
    exact (ht n).of_iso (chain P ((I.mapHomologicalComplex (.up ℤ)).obj N))
  let r := (orbitRetract F N).map
    ((ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).map₂CochainComplex
      |>.obj ((U.mapHomologicalComplex (.up ℤ)).obj P))
  intro n
  have hz := (ho n).isZero_homology
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  let rn := r.map (HomologicalComplex.homologyFunctor _ _ n)
  exact isZero_of_retract rn hz

end AlgebraicGeometry.ProEtaleWeilSheaf
