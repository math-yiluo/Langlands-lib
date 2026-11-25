/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.HomologyShift

/-!
# Compactly supported cohomology of isomorphic and shifted Weil complexes

Isomorphic Weil complexes have isomorphic compactly supported cohomology, with its Frobenius
(`AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyEquivOfIso`), and shifting a Weil
complex shifts its compactly supported cohomology:
`H_cⁿ(X ⊗ k̄, K[a]) ≅ H_c^{a+n}(X ⊗ k̄, K)`
(`AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyShiftEquiv`), the direct image with
compact support commuting with shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Isomorphic Weil complexes have isomorphic compactly supported cohomology, with its
Frobenius. -/
noncomputable def compactlySupportedCohomologyEquivOfIso {K K' : WeilComplex k₀ l X}
    (e : K ≅ K') (r : ℤ) :
    (K.compactlySupportedCohomology r).Equiv (K'.compactlySupportedCohomology r) :=
  WeilSheaf.globalSectionsEquivOfIso ((homologySheaf r).mapIso
    ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).mapIso e))

/-- Compactly supported cohomology of a shifted Weil complex:
`H_cⁿ(X ⊗ k̄, K[a]) ≅ H_cⁿ'(X ⊗ k̄, K)` for `a + n = n'`, with its Frobenius. -/
noncomputable def compactlySupportedCohomologyShiftEquiv (K : WeilComplex k₀ l X)
    (a n n' : ℤ) (h : a + n = n') :
    ((K⟦a⟧).compactlySupportedCohomology n).Equiv (K.compactlySupportedCohomology n') :=
  WeilSheaf.globalSectionsEquivOfIso ((homologySheaf n).mapIso
      (((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).commShiftIso a).app K) ≪≫
    homologySheafShiftIso _ a n n' h)

/-- The compactly supported cohomology of a shifted Weil complex: `H_c^r(L[1]) ≅ H_c^{r+1}(L)`,
the direct image with compact support commuting with shifts. -/
theorem nonempty_equiv_compactlySupportedCohomology_shift (L : WeilComplex k₀ l X) (r : ℤ) :
    Nonempty (((L⟦(1 : ℤ)⟧).compactlySupportedCohomology r).Equiv
      (L.compactlySupportedCohomology (r + 1))) :=
  ⟨compactlySupportedCohomologyShiftEquiv L 1 r (r + 1) (add_comm 1 r)⟩

end AlgebraicGeometry.WeilComplex
