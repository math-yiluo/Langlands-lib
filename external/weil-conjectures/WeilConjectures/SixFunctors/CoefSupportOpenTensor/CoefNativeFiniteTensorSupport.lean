/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.NativeOpenTensorPrimitives.CoefNativeOpenTensorPrimitives
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Tensor closure of native finite open support

Source: Stacks, Modules on Sites, Tag 0E8I.
(blueprint: lem-coef-native-finite-tensor-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

/-- Tensoring a native finite extension by an ambient module stays in its essential image.
Source: Stacks, Modules on Sites, Tag 0E8I (lemma-j-shriek-and-tensor).
(blueprint: lem-coef-native-finite-tensor-support).

Proof: the native extension is an equivalence from open modules to slice modules,
followed by localized extension. On the slice the extension/tensor isomorphism
identifies the ambient tensor with extension of the sheafified tensor of the open
module and the restricted ambient module. Apply the inverse equivalence to this
slice tensor to obtain an open witness. The counit of the equivalence and the
slice tensor isomorphism identify its extension with the desired tensor.
No tensor compatibility for the equivalence is needed. This applies equally to
empty opens, zero modules and the first positive quotient n=0. -/
theorem nativeFiniteTensor_mem_essImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ)
    (M : normalizedDVRModules.{u, u} l E X n)
    (N : normalizedDVRModules.{u, u} l E Z n) :
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).essImage
      (ordinaryTensor.{u + 1, u, u} (ProEt.topology Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        ((ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).obj M) N) := by
  let B := compactSupportSystemLevel l E n
  let R := ProEtale.StrictTower.coefficients B Z
  let W := ProEt.mk j
  let : EssentiallySmall.{u + 1} Z.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures Z
  let := abelianSheafify.{u + 1, u, u + 1} (ProEt.topology Z)
  let := locallyBijective.{u + 1, u, u + 1} (ProEt.topology Z)
  let := abelianSheafify.{u + 1, u, u + 1} ((ProEt.topology Z).over W)
  let := locallyBijective.{u + 1, u, u + 1} ((ProEt.topology Z).over W)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let F := ProEtale.StrictTower.moduleJ B j
  let L := SheafOfModules.localizedModuleExtension.{u} R W
  obtain ⟨e, ⟨ie⟩⟩ := proEtaleOpen_slicePresentation j R
    (ProEtale.StrictTower.coefficients B X) (ProEtale.StrictTower.constantRingIso B j)
  have ie : F ≅ e.functor ⋙ L := ie
  obtain ⟨θ⟩ := SheafOfModules.ringedSlice_extension_tensor.{u + 1, u + 1, u}
    (ProEt.topology Z) R W
  let S := (PresheafOfModules.sheafification.{u + 1}
    (R := ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over W) (𝟙 _)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := (R.over W).obj)
      (e.functor.obj M).val (N.over W).val)
  refine ⟨e.inverse.obj S, ⟨?_⟩⟩
  exact ie.app _ ≪≫ L.mapIso (e.counitIso.app S) ≪≫ θ.app (e.functor.obj M, N) ≪≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) (L.obj (e.functor.obj M)) N).symm ≪≫
      tensorIso (ie.app M).symm (Iso.refl N)

end WeilConjectures.CoefSupportOpenTensor
