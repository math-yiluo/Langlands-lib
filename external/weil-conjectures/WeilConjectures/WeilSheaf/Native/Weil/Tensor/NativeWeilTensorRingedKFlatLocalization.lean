/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatLocalizationEquivalence

/-! # Localization for normalized native ringed tensors

The localization assertion is the second independent field of the native
ringed tensor interface.  It uses functorial K-flat replacements
for the tensor normalized by the given tensor-Hom adjunction.
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

include b in
/--
Native K-flat complexes localize to the unbounded derived category.
Source: Stacks 06YS, 06YU and 0FPT.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-localization).

Proof: the derived quotient inverts the restricted quasi-isomorphisms.
Apply the equivalence field obtained from functorial native K-flat replacements,
using the bridge and the tensor-Hom adjunction to normalize the tensor.
Together these are exactly the two fields of the localization predicate.
-/
theorem native_weil_tensor_ringed_kflat_localization
    (adj : T ⊣₂ ihomBifunctor k₀ l X) :
    ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X T))) := by
  let P := ObjectProperty.ι (NativeTensorKFlat k₀ l X T)
  let W := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage P
  let L := P ⋙ DerivedCategory.Q
  have hInv : W.IsInvertedBy L := by
    intro A B f hf
    change IsIso (DerivedCategory.Q.map f.hom)
    change (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)) f.hom at hf
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)) f.hom hf
  refine { inverts := hInv, isEquivalence := ?_ }
  exact native_weil_tensor_ringed_kflat_localization_equivalence b T adj hInv

end AlgebraicGeometry.ProEtaleWeilSheaf
