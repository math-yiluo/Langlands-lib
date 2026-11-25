/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatResolution
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridge
import all WeilConjectures.WeilSheaf.Native.NativeTensorAcyclicTestComparison

/-! Full native K-flat localization used by normalized extension descent.
(blueprint: lem-sf-native-open-tensor-full-kflat-localization) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The functorial ringed K-flat resolution localizes the full native predicate.
Source: Stacks 06YS and 06YU; native ringed bridge and acyclic-test comparison.
(blueprint: lem-sf-native-open-tensor-full-kflat-localization)

Proof: obtain a functorial native acyclic-test K-flat replacement and its
quasi-isomorphic augmentation from the ringed bridge. The cone criterion makes
each replacement NativeIsKFlat. Lift the replacement functor to the full subcategory
of that predicate. Its augmentation is a functorial left resolution for the
inclusion localizer morphism, hence the inclusion is a localized equivalence.
The ambient derived quotient is a localization, so its restriction is one too. -/
theorem native_open_tensor_full_kflat_localization (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ((ObjectProperty.ι (NativeIsKFlat k₀ l X)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeIsKFlat k₀ l X))) := by
  let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
    NativeIsKFlat k₀ l X
  let W₀ := HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
  let W := W₀.inverseImage P.ι
  obtain ⟨b⟩ := native_weil_tensor_ringed_bridge k₀ l X
  obtain ⟨ρ, ε, hρ, hε⟩ := native_weil_tensor_ringed_kflat_resolution
    (nativeTensorBifunctor k₀ l X) b (nativeTensorParametrizedAdjunction k₀ l X)
  let B := ObjectProperty.lift P ρ (fun K ↦
    native_tensor_acyclic_test_kflat k₀ l X _ (hρ K))
  let Φ : LocalizerMorphism W W₀ :=
    { functor := P.ι
      map := fun _ _ _ h ↦ h }
  let : Φ.IsInduced := ⟨rfl⟩
  let : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions (ρ := B) ε
      (fun K ↦ hε K) rfl
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ DerivedCategory.Q

end AlgebraicGeometry.ProEtaleWeilSheaf
