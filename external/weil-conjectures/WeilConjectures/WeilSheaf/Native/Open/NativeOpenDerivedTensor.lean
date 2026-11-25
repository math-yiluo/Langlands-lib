/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafTensorExistence
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorLocalization
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalization

/-! # Native open derived tensor and balanced pullback composition

Source: Stacks Tags 0GL1 and 0E8I; blueprint fix-lem-tensor-adjunction.proof.md,
Step 1, second Hom bijection (blueprint: lem-sf-native-open-derived-tensor).

All functors act on the ambient derived categories of actual pro-etale Weil
module sheaves. The record retains sheaf, total-complex and derived normalization.
The ordinary inverse is pinned by the open unit, as in openTensorNormalization.

## Main definitions

* `NativeOpenTensorData`: equivariant sheaf comparison and K-flat preservation.
* `OpenTensorPresentation`: total-complex and localization normalization.
* `NativeOpenDerivedTensorData`: natural derived comparison and forgetting square.
* `nativeOpenPullComp`: localization of the canonical balanced compositor.

## Main statements

* `native_open_derived_tensor`: existence of the normalized native comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The equivariant open tensor theorem, on arbitrary unbounded ambient inputs.
Source: Stacks Tags 0E8I, 0GL1, 03D8; blueprint fix-lem-tensor-adjunction.proof.md,
Step 1, second Hom bijection (blueprint: lem-sf-native-open-derived-tensor).

Proof:
1. Geometric base change makes the open Frobenius-stable. On its localized site the
coefficient functions are the same functions, so restriction and extension are the
actual exact module functors. Their unit sends x to [x], and counit [x] to x. These
formulas commute with Frobenius, giving the lifted adjunction and invertible unit.
Use [def-sf-native-weil-derived-framework],
[lem-weil-proetale-weakly-etale-localization],
[lem-pur-site-restriction-module-adjunction-exact],
[lem-sf-native-adic-open-restrictions], and [lem-sf-fixed-pair-created-abelian-structure].
2. The balanced sheaf map sends [x] tensor y to [x tensor y|U]. Its inverse is
exactly the open-unit transpose under restriction/tensor comparison. The tensor
universal property proves they are inverse and natural; both commute with Frobenius.
Use [lem-sf-ringed-slice-tensor-generators] and
[def-sf-derived-weil-category-and-operations].
3. Apply these maps in each bidegree and take direct sums. Both differential
composites are [dx tensor y|U] + (-1)^p [x tensor dy|U]. Thus summands
specifies a chain isomorphism with precisely the recorded total-tensor convention.
Use [lem-sf-ringed-open-total-tensor-kflat] and
[lem-sf-fixed-pair-created-abelian-structure].
4. For a K-flat P, restrict a quasi-isomorphism, tensor with P and extend. The
chain comparison proves extension preserves K-flatness. Conversely extend a
quasi-isomorphism on the open and tensor with a K-flat T. Restricting back and
the invertible unit reflect acyclicity, proving restriction preserves K-flatness.
These are the two elementary tests in [def-sf-derived-weil-category-and-operations].
5. Equivariant flat-term K-flat resolutions exist on the twisted action site.
The locally finite coefficient functions agree with the finite-subextension
coefficient description: finitely many spanning values lie in a finite compositum,
and a quasi-compact test object needs only finitely many such neighborhoods.
Use [lem-sf-weil-frobenius-action-resolutions] and
[def-sf-derived-weil-category-and-operations].
6. Flat sheaves are preserved too: apply exact restriction, tensor and extension
to a short exact sequence, and use the sheaf comparison; for restriction use the
invertible unit to reflect exactness. Thus these functors preserve the resolving
subcategories. Localization of the natural chain map and its inverse gives gamma,
its naturality and the displayed representative square, independently of resolutions.
Use [lem-sf-twisted-action-ringed-site], [lem-sf-weil-frobenius-action-resolutions],
[lem-weil-pbc-site-derived-tensor-descent], and
[lem-weil-pbc-localization-universal-property].
7. Localize the unit-transpose equation through the exact derived adjunction. This
gives inverse_unit. Forgetting the maps of step 3 gives the ordinary maps, with
unchanged signs and unit. The unit-normalized ordinary theorem therefore identifies
them with gamma' and its inverse, giving compatibility. Restriction comparison
is fixed on sheaf summands, then on K-flat representatives; the ordinary comparison
agrees with it on forgotten inputs under the specified tensor comparisons.
Use [lem-sf-ringed-slice-tensor-generators],
[lem-sfb-localized-site-tensor-restriction], [def-weil-exact-derived-adjunction],
[lem-sf-weil-native-closed-forgetful], and [lem-sf-open-tensor-normalization].
8. The nativeOpenPullComp defined above localizes the existing module compositor.
On balanced tensors it multiplies b j*(c); the inverse inserts 1. Balancing proves
both inverse identities, Frobenius commutes with multiplication and fixes 1, and
termwise localization proves naturality on every derived input. No lisse,
boundedness or degree-zero restriction has entered any step.
Use [def-sf-native-weil-derived-framework] and
[lem-sf-native-adic-pullback-exact-lisse]. -/
theorem native_open_derived_tensor :
    ∃ (s : NativeOpenTensorData k₀ l j) (d : NativeOpenDerivedTensorData k₀ l j s)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)),
      NativeOpenPresentationCompatibility k₀ l j s d c := by
  obtain ⟨adj, sheafRestriction, sheafGamma, hu, hcounit, hr, hi, hE, hR⟩ :=
    native_open_sheaf_tensor_existence k₀ l j
  have hunit (M : ProEtaleWeilSheaf k₀ l U) : IsIso (adj.unit.app M) := by
    let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
    have : IsIso (F.map (adj.unit.app M)) := by
      change IsIso ((adj.unit.app M).hom.f)
      rw [hu M]
      infer_instance
    exact isIso_of_reflects_iso (adj.unit.app M) F
  let s : NativeOpenTensorData k₀ l j :=
    { adj := adj
      unit_forget := hu
      counit_forget := hcounit
      unit_iso := hunit
      sheafRestriction := sheafRestriction
      restriction_forget := hr
      sheafGamma := sheafGamma
      sheaf_inverse := hi
      extension_kflat := hE
      restriction_kflat := hR }
  obtain ⟨rho, gamma, c, hc⟩ := native_open_tensor_localization k₀ l j s
  obtain ⟨hunit, hord⟩ := native_open_tensor_normalization k₀ l j s rho gamma c hc
  refine ⟨s, ⟨gamma, rho, hunit, hord⟩, c, ?_⟩
  exact hc

end AlgebraicGeometry.ProEtaleWeilSheaf
