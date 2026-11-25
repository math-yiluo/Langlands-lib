/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.WeilSheaf.Native.NativeForgetTotalTensor
import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarKFlat
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryKFlatLocalization
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryCanonicalTensorRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# The pullback of native Weil complexes preserves K-flatness

For an arbitrary morphism `p : Z ⟶ Y` of `k₀`-schemes, the pullback `p^*` of pro-étale Weil
sheaves, applied degreewise, sends complexes which are K-flat for the native tensor product
(`AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat`) to K-flat complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_mapHomologicalComplex_obj`).

Forgetting the Weil structure identifies the native K-flatness of a complex `P` with the K-flatness
of its underlying complex of `ℓ`-adic sheaves on the geometric fibre:

* if `P` is natively K-flat, then so is its underlying complex
  (`AlgebraicGeometry.ProEtaleWeilSheaf.native_two_sided_kflat_forget`);
* conversely, forgetting is exact, reflects isomorphisms and commutes with the tensor product of
  complexes, so a native tensor test may be checked after forgetting
  (`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_of_kFlat_forget`).

The underlying complex of `p^* P` is the pullback along the geometric fibre `p̄` of the underlying
complex of `P`, and the pullback of `ℓ`-adic sheaves preserves K-flat complexes
(`AlgebraicGeometry.ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory WeilConjectures

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of pro-étale Weil sheaves along an arbitrary morphism of `k₀`-schemes preserves
native K-flatness. -/
theorem nativeIsKFlat_upperStar_mapHomologicalComplex_obj
    (T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hT : NativeIsKFlat k₀ l Y T) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj T) := by
  have h₁ := kFlat_forget_of_nativeIsKFlat k₀ l Y T hT
  have h₂ := ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj l
    (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))) h₁
  apply nativeIsKFlat_of_kFlat_forget
  refine ObjectProperty.prop_of_iso _
    (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) ?_) h₂
  intro i j _
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
