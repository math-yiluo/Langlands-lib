/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceEquivariance
import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal

/-! # Dependency audit of the descended-trace assembly of smooth purity -/

open AlgebraicGeometry AlgebraicGeometry.WeilComplex

/-! The statement of `exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`, in the
context of `WeilConjectures.WeilSheaf.SmoothPurity`, follows from the Tate encoding `α` and the
universality of the descended trace, with no other input. -/

section Check

open CategoryTheory ProEtale

variable {k₀ : Type*} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

example (d : ℕ) [SmoothOfRelativeDimension d f] (α : TateEncoding (k₀ := k₀) (l := l) (X := X) d)
    (h : DescendedSmoothTraceUniversal f α) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj :=
  exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_descendedTrace f α h

end Check
