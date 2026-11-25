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
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryCanonicalTensorRepresentatives
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.BifunctorFlip

/-! # The ordinary acyclic tensor test implies the two-sided native K-flat test -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.MonoidalCategory

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

omit [Fact (ringChar k₀ ≠ l)] in
/-- Forgetting the Weil structure reflects acyclicity of complexes, since it is
faithful and exact. -/
private theorem acyclic_of_forget (K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hK : (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
      |>.mapHomologicalComplex (.up ℤ)).obj K).Acyclic) : K.Acyclic := by
  intro i
  exact (ShortComplex.exact_map_iff_of_faithful _
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).1 (hK i)

/-- If the forgotten complex of `P` passes the ordinary acyclic tensor test, then
the native total tensor of `P` with an acyclic complex (on the left) is acyclic. -/
private theorem acyclic_tensor_left (P N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
        |>.mapHomologicalComplex (.up ℤ)).obj P))
    (hN : N.Acyclic) :
    (CochainComplex.mapBifunctor P N (nativeTensorBifunctor k₀ l X)).Acyclic := by
  obtain ⟨chain, _⟩ := native_weil_tensor_chain k₀ l X
    (nativeTensorBifunctor k₀ l X) (tensorBifunctorForget k₀ l X)
  apply acyclic_of_forget
  intro n
  exact (hP _ (hN.map _) n).of_iso (chain P N).symm

/-- The same test with the acyclic complex in the first total-tensor slot, using
the ordinary signed swap of total tensors. -/
private theorem acyclic_tensor_right (P N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
        |>.mapHomologicalComplex (.up ℤ)).obj P))
    (hN : N.Acyclic) :
    (CochainComplex.mapBifunctor N P (nativeTensorBifunctor k₀ l X)).Acyclic := by
  obtain ⟨chain, _⟩ := native_weil_tensor_chain k₀ l X
    (nativeTensorBifunctor k₀ l X) (tensorBifunctorForget k₀ l X)
  obtain ⟨-, -, swap, -⟩ := native_ordinary_canonical_tensor_representatives l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  apply acyclic_of_forget
  intro n
  exact (hP _ (hN.map _) n).of_iso (chain N P ≪≫ swap _ _).symm

/-- The ordinary acyclic tensor test for the forgotten complex implies the
canonical native two-sided K-flat test.
Source: Stacks 06YS (blueprint: lem-sf-native-two-sided-kflat-forget).

Proof: a chain map is a quasi-isomorphism iff its mapping cone is acyclic, and the
total tensor with a fixed complex commutes with mapping cones. So it suffices that
the native total tensor of P with an acyclic complex, on either side, is acyclic.
Forgetting is faithful and exact, hence reflects acyclicity; after forgetting, the
chain comparison (and the ordinary signed swap for the other side) identifies the
complex with the ordinary total tensor of the forgotten P with an acyclic complex. -/
theorem nativeIsKFlat_of_nativeOrdinaryKFlat_forget
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
        |>.mapHomologicalComplex (.up ℤ)).obj P)) :
    NativeIsKFlat k₀ l X P := by
  refine ⟨fun {Q Q'} s hs ↦ ?_, fun {Q Q'} s hs ↦ ?_⟩
  · have hc := acyclic_tensor_right k₀ l X P _ hP
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic s).1 hs)
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    intro i
    exact (hc i).of_iso ((HomologicalComplex.mapBifunctorFlipIso
      (CochainComplex.mappingCone s) P (nativeTensorBifunctor k₀ l X) (.up ℤ)).symm ≪≫
        CochainComplex.mapBifunctorMappingCone₂Iso P s (nativeTensorBifunctor k₀ l X).flip)
  · have hc := acyclic_tensor_left k₀ l X P _ hP
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic s).1 hs)
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    intro i
    exact (hc i).of_iso ((HomologicalComplex.mapBifunctorFlipIso
      P (CochainComplex.mappingCone s) (nativeTensorBifunctor k₀ l X) (.up ℤ)).symm ≪≫
        CochainComplex.mapBifunctorMappingCone₁Iso s P (nativeTensorBifunctor k₀ l X).flip)

end AlgebraicGeometry.ProEtaleWeilSheaf
