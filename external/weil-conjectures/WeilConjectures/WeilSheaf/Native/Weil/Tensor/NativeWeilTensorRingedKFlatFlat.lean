/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainData
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # K-flat transport for normalized native ringed tensors

The K-flat transport is the first independent field of the native ringed tensor
interface.  Its proof uses the underived tensor comparison and the additive
native equivalence. No choice of K-flat resolution is needed.
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

/--
Transport acyclic-test K-flatness through the native additive equivalence.
Source: Stacks 06YS, 06YU and 0FPT.
(blueprint: lem-sf-native-weil-tensor-ringed-kflat-flat).

Proof: identify the native tensor with the normalized ringed tensor by the
underived Hom comparison, then transport the acyclic-test condition through
`b.native`: pull an arbitrary ringed acyclic test back along the inverse
complex equivalence. Its native tensor with P is acyclic by hypothesis, and
applying the exact equivalence preserves acyclicity. The total comparison and
the counit identify this complex with the ringed tensor of the original test
and the transported P. Transport exactness across that isomorphism degreewise.
The tensor-Hom adjunction is needed to obtain the underived comparison.
-/
-- repair: pass the normalized-sign proof required by ChainData (global-build fix)
theorem native_weil_tensor_ringed_kflat_flat (adj : T ⊣₂ ihomBifunctor k₀ l X) :
    ∀ (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeTensorKFlat k₀ l X T P →
        CochainComplex.IsKFlatIndependentCoefficients (R := b.R)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨U⟩ := native_weil_tensor_ringed_underived_data b T adj
  let sign (p q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (f : Y ⟶ Z) : Y ⟶ Z :=
    letI : AddCommGroup (Y ⟶ Z) := Preadditive.homGroup Y Z
    ZSMul.zsmul ((p * q).negOnePow : ℤ) f
  obtain ⟨c⟩ := native_weil_tensor_ringed_chain_data b T adj U sign
    (fun _ _ _ _ _ ↦ rfl)
  intro P hP
  let e := b.native.mapHomologicalComplex (.up ℤ)
  intro N hN
  have hQ : (e.inverse.obj N).Acyclic := hN.map b.native.inverse
  have ht := (hP (e.inverse.obj N) hQ).map b.native.functor
  let t := coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R
  let i := c.chain P (e.inverse.obj N) ≪≫
    t.mapIso ((e.counitIso.app N).prod (Iso.refl (e.functor.obj P)))
  exact fun n ↦ (ht n).of_iso i

end AlgebraicGeometry.ProEtaleWeilSheaf
