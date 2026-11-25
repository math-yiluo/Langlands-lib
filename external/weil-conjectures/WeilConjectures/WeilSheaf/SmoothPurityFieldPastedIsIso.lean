/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedUnit
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeCongr

/-! # Invertibility for the actual compactification exchange -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  (c : Compactification f.left) (c' : Compactification f'.left)
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left} {πZ : c'.Z ⟶ c.Z}
  (hi : IsPullback c'.i πX πZ c.i) (hg : IsPullback πZ c'.g c.g πY)
  [WeaklyEtale πZ] [WeaklyEtale πY]

/-- The open factor has an invertible mate, using the two fully faithful extension
functors and the pullback-composition square. -/
lemma isIso_purityFieldOpenRestrictedExchange_mate
    (N : Dᵇc(c.overObj.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((mateEquiv
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l c.overI)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l c'.overI)
      (inv (purityFieldOpenRestrictedExchange l f f' c c' hi).hom)).app N) :=
  Adjunction.isIso_mateEquiv_app_of_isIso_unit _ _ _
    (boundedConstructibleUpperStarCompUpperStarOfMapIso l c.overI c'.overI hi.flip.w) N

variable (e : (boundedConstructibleUpperStarOfMap l (X := Y) (Y := Y') πY).obj (𝟙_ _) ⟶ 𝟙_ _)

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The unit mate of the actual proper restriction is the library exceptional
base-change map, followed by the target-unit comparison. -/
lemma purityFieldProperRestrictedExchange_unitBaseChange :
    Adjunction.unitBaseChange
        (purityCompactificationProperAdjunction l f c)
        (purityCompactificationProperAdjunction l f' c')
        (purityFieldProperRestrictedExchange l f f' c c' hg).hom e =
      (upperShriekBaseChangeOfMap l (f := c.overG) (f' := c'.overG) hg).app (𝟙_ _) ≫
        (boundedConstructibleUpperShriek l c'.overG).map e := by
  have := isIso_boundedConstructibleBaseChangeOfMap l
    (f := c.overG) (f' := c'.overG) hg
  exact Adjunction.unitBaseChange_congr
    (purityCompactificationProperAdjunction l f c)
    (purityCompactificationProperAdjunction l f' c')
    (purityFieldProperRestrictedExchange_hom l f f' c c' hg) e

/-- For the actual compactification exchange, invertibility reduces to the proper
factor at the unit; the open factor is automatic. -/
theorem isIso_smoothUnitBaseChange_fieldCompactification_of_proper
    [IsIso ((upperShriekBaseChangeOfMap l (f := c.overG) (f' := c'.overG) hg).app (𝟙_ _))]
    [IsIso e] :
    IsIso (smoothUnitBaseChange l f f'
      (purityFieldLowerShriekExchange l f f' c c' hi hg) e) := by
  have := isIso_purityFieldOpenRestrictedExchange_mate l f f' c c' hi
    ((boundedConstructibleUpperShriek l c.overG).obj (𝟙_ _))
  have : IsIso (Adjunction.unitBaseChange
      (purityCompactificationProperAdjunction l f c)
      (purityCompactificationProperAdjunction l f' c')
      (purityFieldProperRestrictedExchange l f f' c c' hg).hom e) := by
    rw [purityFieldProperRestrictedExchange_unitBaseChange]
    infer_instance
  exact isIso_smoothUnitBaseChange_fieldCompactification l f f' c c' hi hg e

end AlgebraicGeometry.ProEtale.CondensedRing
