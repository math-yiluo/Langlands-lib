/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import Mathlib.CategoryTheory.Localization.Construction
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Equivalence field of native K-flat localization

Functorial native K-flat replacements give a localized equivalence by the
fully faithful inclusion criterion. No fraction calculus on complexes is used.
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
/-- The localization construction for native K-flat complexes is an equivalence.
Source: Stacks 06YS, 06YU and 0FPT.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-localization-equivalence).

Proof: the normalized tensor-Hom adjunction and ringed bridge give a functorial
native K-flat replacement with a natural quasi-isomorphic augmentation. Lift
its functor to the full subcategory of native K-flat complexes. The inclusion
is fully faithful, its weak equivalences are induced, and quasi-isomorphisms
have two-out-of-three. The functorial-left-resolution criterion therefore makes
the inclusion a localized equivalence. Since the ambient derived quotient is a
localization, the restricted quotient is one too, giving the equivalence field.
The argument covers unbounded and zero complexes.
-/
theorem native_weil_tensor_ringed_kflat_localization_equivalence
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (hInv :
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X T))).IsInvertedBy
        ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q)) :
    (Localization.Construction.lift
      ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q)
      hInv).IsEquivalence := by
  let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
    NativeTensorKFlat k₀ l X T
  let W₀ := HomologicalComplex.quasiIso
    (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
  let W := W₀.inverseImage P.ι
  let L := P.ι ⋙ DerivedCategory.Q
  obtain ⟨ρ, ε, hρ, hε⟩ := native_weil_tensor_ringed_kflat_resolution T b adj
  let B := ObjectProperty.lift P ρ hρ
  let Φ : LocalizerMorphism W W₀ :=
    { functor := P.ι
      map := fun _ _ _ h ↦ h }
  let : Φ.IsInduced := ⟨rfl⟩
  let : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions (ρ := B) ε
      (fun K ↦ hε K) rfl
  let : L.IsLocalization W :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ DerivedCategory.Q
  exact Functor.IsLocalization.isEquivalence (L := L) (W := W)

end AlgebraicGeometry.ProEtaleWeilSheaf
