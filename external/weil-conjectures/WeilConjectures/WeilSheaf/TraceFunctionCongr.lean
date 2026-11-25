/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.StalkIso

/-!
# Trace functions of isomorphic Weil sheaves

Trace functions only depend on the isomorphism class of a Weil sheaf, and the trace function of
a Weil sheaf placed in degree zero is that of the sheaf.

## Main statements

- `AlgebraicGeometry.WeilSheaf.traceFunction_congr`: isomorphic Weil sheaves have the same trace
  function.
- `AlgebraicGeometry.WeilComplex.traceFunction_congr`: isomorphic Weil complexes have the same
  trace function.
- `AlgebraicGeometry.WeilComplex.traceFunction_toComplex`: the trace function of a Weil sheaf
  viewed as a complex in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- Isomorphic Weil sheaves have the same trace function: an isomorphism induces isomorphisms of
Frobenius modules between the stalks (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_of_iso`),
which preserve the characteristic polynomial, hence the trace, of the Frobenius. -/
theorem WeilSheaf.traceFunction_congr {F G : WeilSheaf k₀ l X} (e : F ≅ G) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n x = G.traceFunction n x := by
  simp only [traceFunction]
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff, LinearMap.trace_eq_neg_charpoly_nextCoeff,
    (nonempty_equiv_stalkAt_of_iso _ _ _ e).some.charpoly_frobeniusEnd]

/-- Isomorphic Weil complexes have the same trace function: their cohomology sheaves are
isomorphic. -/
theorem WeilComplex.traceFunction_congr {K L : WeilComplex k₀ l X} (e : K ≅ L) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n x = L.traceFunction n x := by
  rw [traceFunction, traceFunction]
  congr 1
  ext j
  rw [WeilSheaf.traceFunction_congr ((homologySheaf j).mapIso e)]

/-- The trace function of a Weil sheaf placed in degree zero is the trace function of the
sheaf: its only nonzero cohomology sheaf is `𝓗⁰ = F`. -/
theorem WeilComplex.traceFunction_toComplex (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (WeilSheaf.toComplex.obj F).traceFunction n x = F.traceFunction n x := by
  rw [WeilSheaf.toComplex_obj, traceFunction_eq_sum _ {0}
    (fun j hj ↦ isZero_homologySheaf_singleComplex (Finset.notMem_singleton.1 hj) F),
    Finset.sum_singleton, Int.negOnePow_zero, Units.val_one, one_smul]
  exact WeilSheaf.traceFunction_congr (WeilSheaf.toComplexCompHomologySheafIso.app F) n x

end AlgebraicGeometry
