/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariant
public import WeilConjectures.SmoothPurity.Section.ProEtaleDeformation
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison

/-! # DNC invariance of the section invariant in the finite purity setting

The section invariant `C(g, s)` of the finite purity setting, with coefficients `O_E/ϖ^n` over a
finite-type scheme over the finite field `k`, is the pro-étale section invariant
`AlgebraicGeometry.ProEtale.sectionInvariant` at this coefficient ring. Hence the pro-étale
deformation to the normal cone applies to it (blueprint `lemma-section-normal-bundle`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line, in the
finite purity setting. For `g : V ⟶ B` separated, quasi-compact and smooth of pure relative
dimension `d` with a closed section `s`, over `B` separated of finite type over `k`, the section
invariant of `(g, s)` is isomorphic to that of the normal cone of `s` with its zero section. This is
`AlgebraicGeometry.ProEtale.nonempty_iso_sectionInvariant_normalConeProj` at the coefficient
ring `O_E/ϖ^n`, on which `ℓ ≠ p` is invertible. -/
theorem nonempty_iso_sectionInvariant_normalConeProj (P : PurityFiniteSetting.{u}) (d : ℕ)
    {V B : Scheme.{u}} (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) [HasCompactification (Scheme.Hom.normalConeProj g s)]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [QuasiCompact aB] :
    Nonempty (P.sectionInvariant g aB s ≅
      P.sectionInvariant (Scheme.Hom.normalConeProj g s) aB s.normalConeZeroSection) :=
  have := finiteComparedInvertibleExponent P aB
  have := QuasiCompact.compactSpace_of_compactSpace aB
  ProEtale.nonempty_iso_sectionInvariant_normalConeProj P.Coefficient d g s hs aB

end WeilConjectures.PurityFiniteSetting
