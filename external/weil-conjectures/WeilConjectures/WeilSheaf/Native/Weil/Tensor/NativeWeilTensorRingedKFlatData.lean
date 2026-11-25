/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatFlat
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatLocalization

/-! # K-flat and localization data for normalized native ringed tensors

The two homological clauses are independent of the construction of the
underived and total comparison maps, so they are recorded as a separate
intermediate interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

structure NativeWeilRingedTensorKFlatData
    (_adj : T ⊣₂ ihomBifunctor k₀ l X) where
  flat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := b.R)
      ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
  localization :
    ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X T)))

/-- The transport of K-flatness and the resolving localization.
Source: Stacks 06YS, 06YU and 0FPT
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-data).

Proof: transport acyclic tests through the additive equivalence `b.native`,
using the ringed tensor total.  The resolution theorem for sheaves of modules
gives flat-term K-flat replacements; restriction to the native image and the
homotopy localization criterion then give the displayed localization.  The
argument applies to unbounded complexes and does not use the chosen chain map.
-/
theorem native_weil_tensor_ringed_kflat_data :
    Nonempty (NativeWeilRingedTensorKFlatData b T adj) := by
  refine ⟨{ flat := native_weil_tensor_ringed_kflat_flat b T adj
            localization := native_weil_tensor_ringed_kflat_localization b T adj }⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
