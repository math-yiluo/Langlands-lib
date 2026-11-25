/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # The canonical sections-tensor comparison commutes with shifts

Source: Stacks Project, Tag 03EK, sectionwise tensor and sheafification; blueprint
`lemma-perfect-complexes-geometric-point`, final-display argument
(blueprint: lem-weil-point-sections-tensor-shift).

The comparison itself is the existing `pointDerivedSectionsTensor`. The shift on
ordinary derived scalar extension is transported from exact termwise scalar extension
through its canonical, representative-normalized comparison, independently of theta.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures

variable (k : Type u) [Field k] [IsAlgClosed k]
  (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures
