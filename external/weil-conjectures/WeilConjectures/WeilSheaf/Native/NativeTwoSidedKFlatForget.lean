/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorChain
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
import Mathlib.Algebra.Homology.BifunctorFlip

/-! # The two-sided native K-flat test and ordinary forgetting -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.MonoidalCategory
open ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

private instance tensor_additive : (nativeTensorBifunctor k₀ l X).Additive where
  map_add := by
    intro P Q f g
    apply NatTrans.ext
    funext N
    exact ((nativeTensorBifunctor k₀ l X).flip.obj N).map_add

private instance tensor_obj_additive (P : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorBifunctor k₀ l X).obj P).Additive :=
  (tensorIhomAdjunction k₀ l X P).left_adjoint_additive

private theorem acyclic_of_quasiIso_test
    {A : Type*} [Category* A] [Abelian A]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ) [F.Additive]
    (hF : ∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q), QuasiIso f → QuasiIso (F.map f))
    (N : CochainComplex A ℤ) (hN : N.Acyclic) : (F.obj N).Acyclic := by
  let Z : CochainComplex A ℤ := 0
  have hZ : Z.Acyclic := HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
  have hs : QuasiIso (0 : Z ⟶ N) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt _ n (hZ n)).mpr (hN n)
  have ht := hF (0 : Z ⟶ N) hs
  have hz : (F.obj Z).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (F.map_isZero (isZero_zero _))
  intro n
  have : QuasiIsoAt (F.map (0 : Z ⟶ N)) n := (quasiIso_iff _).mp ht n
  exact (quasiIsoAt_iff_exactAt _ n (hz n)).mp this

/-- The canonical native two-sided K-flat test implies the ordinary acyclic tensor test.
Source: Stacks 06YS and the exact orbit-induction argument of native tensor transport.
(blueprint: lem-sf-native-two-sided-kflat-forget).

Proof: an acyclic complex N admits a quasi-isomorphism from the zero complex.
The second quasi-isomorphism test for P sends this map to a quasi-isomorphism;
additivity sends the zero object to a zero object, so its target is acyclic.
The total-complex flip identifies that target with the unflipped total tensor of
P with N. Apply native_weil_tensor_forget_kflat: its exact orbit induction places
any ordinary acyclic test in the underlying native category, and the degree-zero
orbit summand exhibits its tensor with the forgotten P as a retract. Exact
forgetting and that splitting prove ordinary acyclicity. Zero complexes, empty
sites and unbounded complexes satisfy exactly the same argument. -/
theorem native_two_sided_kflat_forget
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) :
    NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
        |>.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨chain, _⟩ := native_weil_tensor_chain k₀ l X
    (nativeTensorBifunctor k₀ l X) (tensorBifunctorForget k₀ l X)
  apply native_weil_tensor_forget_kflat k₀ l X
    (nativeTensorBifunctor k₀ l X) chain P
  intro N hN n
  have : ((nativeTensorTotal k₀ l X).flip.obj P).Additive := by
    change (((nativeTensorBifunctor k₀ l X).flip.map₂CochainComplex).flip.obj P).Additive
    infer_instance
  have ht := acyclic_of_quasiIso_test
    ((nativeTensorTotal k₀ l X).flip.obj P) hP.2 N hN
  exact (ht n).of_iso
    (HomologicalComplex.mapBifunctorFlipIso P N (nativeTensorBifunctor k₀ l X) (.up ℤ))

end AlgebraicGeometry.ProEtaleWeilSheaf
