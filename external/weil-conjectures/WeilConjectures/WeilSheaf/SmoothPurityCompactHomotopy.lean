/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.VerdierDualLocalization
public import WeilConjectures.WeilSheaf.AffineLineBundle
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology

/-!
# Compact constant cohomology from absolute purity and homotopy invariance

Verdier exchange turns ordinary constant homotopy invariance into the compact
cohomology of the dualizing complex. Absolute purity and commutation with the
Tate twist then compute compact cohomology of the constant complex.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- The Verdier dual of the constant complex is the dualizing complex. -/
theorem nonempty_verdierDual_adicConstant_iso
    [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty ((verdierDual k₀ l X).obj
        (op (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))) ≅
      dualizingComplex k₀ l X) := by
  obtain ⟨e⟩ := nonempty_tensorLisse_dual_iso_derivedHom
    (WeilSheaf.adicConstant k₀ l X) (WeilSheaf.isLisse_adicConstant k₀ l X)
    (dualizingComplex k₀ l X)
  obtain ⟨a⟩ := nonempty_iso_tensorLisse_of_iso
    (WeilSheaf.dualAdicConstantIso (k₀ := k₀) (l := l) (X := X)) _ _
  obtain ⟨b⟩ := nonempty_iso_tensorLisse_adicConstant (k₀ := k₀) (l := l) (X := X)
  exact ⟨ObjectProperty.isoMk _ e.symm ≪≫ a.app _ ≪≫ b.app _⟩

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The Tate twist commutes with compact pushforward. This form is available
before the Fourier inversion users. -/
noncomputable def compactTateCommutationIso (m : ℤ) :
    tateTwist k₀ l X m ⋙ derivedLowerShriek k₀ l f ≅
      derivedLowerShriek k₀ l f ⋙ tateTwist k₀ l Y m := by
  let P := objectProperty k₀ l Y
  let eD : derivedLowerShriek k₀ l f ⋙ P.ι ≅
      (objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
        (HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)) :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  apply (P.fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tateTwist k₀ l X m) eD ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tateTwistCompιIso m) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso
        k₀ l f _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eD.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (tateTwistCompιIso m).symm ≪≫
    (Functor.associator _ _ _).symm

variable [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))]

/-- Ordinary homotopy invariance of the constant object computes compact
pushforward of the dualizing complex. -/
theorem nonempty_compact_dualizing_iso_of_constant_homotopy
    (h : (derivedLowerStar f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) :
    Nonempty ((derivedLowerShriek k₀ l f).obj (dualizingComplex k₀ l X) ≅
      dualizingComplex k₀ l Y) := by
  obtain ⟨e⟩ := nonempty_verdierDual_derivedLowerStar_iso f
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))
  obtain ⟨a⟩ := nonempty_verdierDual_adicConstant_iso (k₀ := k₀) (l := l) (X := X)
  obtain ⟨b⟩ := nonempty_verdierDual_adicConstant_iso (k₀ := k₀) (l := l) (X := Y)
  exact ⟨(derivedLowerShriek k₀ l f).mapIso a.symm ≪≫ e.symm ≪≫
    (verdierDual k₀ l Y).mapIso h.symm.op ≪≫ b⟩

/-- Absolute purity, ordinary constant homotopy invariance, and Verdier exchange
give compact constant cohomology, without relative smooth purity. -/
theorem nonempty_compact_constant_iso_of_absolute_purity (d : ℤ)
    (h : (derivedLowerStar f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))
    (eX : dualizingComplex k₀ l X ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))) ⟦2 * d⟧)
    (eY : dualizingComplex k₀ l Y ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) :
    Nonempty ((derivedLowerShriek k₀ l f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      ((tateTwist k₀ l Y (-d)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ⟦-(2 * d)⟧) := by
  obtain ⟨e⟩ := nonempty_compact_dualizing_iso_of_constant_homotopy f h
  let L := derivedLowerShriek k₀ l f
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)
  let V := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)
  let a : L.obj (((tateTwist k₀ l X d).obj U) ⟦2 * d⟧) ≅
      ((tateTwist k₀ l Y d).obj (L.obj U)) ⟦2 * d⟧ :=
    (L.commShiftIso (2 * d)).app _ ≪≫
      (shiftFunctor _ (2 * d)).mapIso ((compactTateCommutationIso f d).app U)
  let b : ((tateTwist k₀ l Y d).obj (L.obj U)) ⟦2 * d⟧ ≅ V :=
    a.symm ≪≫ L.mapIso eX.symm ≪≫ e ≪≫ eY
  let N := tateTwist k₀ l Y (-d) ⋙ shiftFunctor (WeilComplex k₀ l Y) (-(2 * d))
  exact ⟨((tateTwistShiftCompTateTwistShiftIso k₀ l Y d (-d)
    (2 * d) (-(2 * d)) (by omega) (by omega)).app (L.obj U)).symm ≪≫ N.mapIso b⟩

end AlgebraicGeometry.WeilComplex
