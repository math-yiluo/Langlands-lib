/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionData
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionNaturality

/-! # Extension of ordinary tensor models through K-flat resolutions

Source: Stacks 06YS, 06YU, 0FPT; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-data`.
(blueprint: lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Extend normalized tensor representatives from K-flat second inputs to all inputs.

Choose the degreewise-epimorphic K-flat resolutions supplied by
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`; for a
K-flat second input keep the given model, so the normalization (which only
constrains K-flat second inputs) holds unchanged.  Since `P` is K-flat,
tensoring with `P` sends the resolution to a quasi-isomorphism.  The
K-flat naturality square `hkflat` (applied also to roofs through a further
K-flat resolution, to handle derived maps between resolutions) transports the
model across each resolution; the
quasi-isomorphism and the derived tensor localization identify the transported
value with the original input.  The same comparison transports the normalized
uncurrying equation and gives naturality for arbitrary maps in the second
variable. -/
theorem native_ordinary_tensor_model_resolution_extension
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (hnormalization : NativeAdjunctionNormalization
      (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
      (fun P ↦ Mod.ihomAdjunction P) H R S
      (NativeOrdinaryKFlat l Y) model)
    (hkflat : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (hQ : NativeOrdinaryKFlat l Y Q)
      (hQ' : NativeOrdinaryKFlat l Y Q')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ))) :
    ∃ extendedModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q),
      NativeAdjunctionNormalization
        (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
        (fun P ↦ Mod.ihomAdjunction P) H R S
        (NativeOrdinaryKFlat l Y) extendedModel ∧
      (∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P)
        (hP' : NativeOrdinaryKFlat l Y P')
        (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (extendedModel P' Q' hP').hom =
          (extendedModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l Y) (.up ℤ))) := by
  classical
  obtain ⟨extendedModel, hext, htransport, hresolution⟩ :=
    native_ordinary_tensor_model_resolution_data l Y H R S model hkflat
  refine ⟨extendedModel, ?_, ?_⟩
  · intro P Q I hP hQ hI φ
    obtain ⟨ψ, hψ, hmodel⟩ := hnormalization P Q I hP hQ hI φ
    refine ⟨ψ, hψ, ?_⟩
    rw [hext P Q hP hQ]
    exact hmodel
  · exact native_ordinary_tensor_model_resolution_naturality
      l Y H R S model extendedModel htransport hresolution hkflat

end AlgebraicGeometry.ProEtaleWeilSheaf
