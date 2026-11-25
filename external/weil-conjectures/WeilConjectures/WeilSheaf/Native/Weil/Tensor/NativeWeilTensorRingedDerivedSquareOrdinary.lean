/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelNaturality
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionExtension

/-! # Ordinary model part of the native ringed derived square

Source: Stacks 06YU, 0FPT; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The ordinary one-K-flat representative, its adjunction normalization, and its
naturality are the ordinary part of the derived-square construction.

Source: Stacks 06YU, 0FPT; blueprint:
`lem-sf-native-weil-tensor-ringed-derived-square`.

Proof: extract the normalized ordinary model supplied by `NativeOrdinaryTensorModels`.
By `native_ordinary_tensor_model_naturality_kflat`, the normalization (componentwise
uncurrying against K-injective targets) forces naturality when both second inputs are
K-flat.  By `native_ordinary_tensor_model_resolution_extension`, the K-flat replacement
theorem then yields a new model, equal to the given one on K-flat second inputs (hence
still normalized) and natural in both representative complexes for arbitrary second
inputs.  The signed swap is used only for the later coherence step and is therefore not
part of this intermediate assertion. -/
theorem native_weil_tensor_ringed_derived_square_ordinary_data
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hS : NativeOrdinaryTensorModels l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber M.ordinaryHom
      M.ordinaryRepresentatives S β) :
    ∃ ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q),
      NativeAdjunctionNormalization
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (fun P ↦ Mod.ihomAdjunction P) M.ordinaryHom M.ordinaryRepresentatives S
        (NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ordinaryModel ∧
      (∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
          (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
          (hP' : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P')
          (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (ordinaryModel P' Q' hP').hom =
          (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ))) := by
  obtain ⟨ordinaryModel, ⟨_hswap, hordinary, _hsigned, _hbraiding⟩⟩ := hS
  have hkflat := native_ordinary_tensor_model_naturality_kflat
    l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber M.ordinaryHom
    M.ordinaryRepresentatives S ordinaryModel hordinary
  exact native_ordinary_tensor_model_resolution_extension
    l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber M.ordinaryHom
    M.ordinaryRepresentatives S ordinaryModel hordinary hkflat

end AlgebraicGeometry.ProEtaleWeilSheaf
