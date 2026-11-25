/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativePullDerivedTensor
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatOfForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicUpperStarKFlat
public import WeilConjectures.WeilSheaf.Native.NativeForgetBaseChange

/-! # The derived balanced pullback/tensor comparison

For a morphism `p : Z ⟶ Y` of `k₀`-schemes, the pullback of pro-étale Weil sheaves preserves
native two-sided K-flat complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_mapHomologicalComplex`), so the
hypothesis of
`AlgebraicGeometry.ProEtaleWeilSheaf.exists_nativeOpenPull_nativeDerivedTensor_iso_of_nativeIsKFlat`
holds: the balanced sheaf comparison `p^*(M ⊗ N) ≅ p^* M ⊗ p^* N` descends to a natural isomorphism
`p^*(A ⊗ B) ≅ p^* A ⊗ p^* B` of native derived tensor products, for every `p`. This is the
pullback/tensor comparison entering the proper projection formula (blueprint:
`fix-prop-projection-formula`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Ordinary K-flatness of complexes of `ℓ`-adic sheaves is invariant under isomorphism. -/
theorem nativeOrdinaryKFlat_of_iso {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {P P' : CochainComplex (ProEtale.AdicSheaf l X) ℤ} (e : P ≅ P')
    (hP : NativeOrdinaryKFlat l X P) : NativeOrdinaryKFlat l X P' := fun N hN n ↦
  (hP N hN n).of_iso (((ordinaryTensorBifunctor l X).map₂CochainComplex.mapIso e).app N)

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- Pullback of pro-étale Weil sheaves preserves native two-sided K-flat complexes: forgetting
the Weil structure, native K-flatness is ordinary K-flatness
(`AlgebraicGeometry.ProEtaleWeilSheaf.native_two_sided_kflat_forget`,
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_of_nativeOrdinaryKFlat_forget`), and the
pullback of `ℓ`-adic sheaves along `p̄ : Z̄ ⟶ Ȳ` preserves ordinary K-flatness
(`AlgebraicGeometry.ProEtale.nativeOrdinaryKFlat_adicUpperStar`). -/
theorem nativeIsKFlat_upperStar_mapHomologicalComplex
    (T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hT : NativeIsKFlat k₀ l Y T) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj T) := by
  let U (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let e : ((ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap p (comp_over p _))).mapHomologicalComplex (.up ℤ)).obj
          (((U Y).mapHomologicalComplex (.up ℤ)).obj T) ≅
      ((U Z).mapHomologicalComplex (.up ℤ)).obj
        (((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj T) :=
    (Functor.mapHomologicalComplexCompIso (forgetCompAdicUpperStarIso k₀ l p) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (upperStar k₀ l p ⋙ U Z)) (.up ℤ)).symm).app T
  exact nativeIsKFlat_of_nativeOrdinaryKFlat_forget k₀ l Z _
    (nativeOrdinaryKFlat_of_iso e (ProEtale.nativeOrdinaryKFlat_adicUpperStar l
      (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))) _
      (native_two_sided_kflat_forget k₀ l Y T hT)))

end AlgebraicGeometry.ProEtaleWeilSheaf
