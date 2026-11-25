/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePastedAdjunction

/-! # Unit base change for the specified compactification exchange -/

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

/-- The proper factor's adjunction, with its actual lower-star left adjoint. -/
noncomputable def purityCompactificationProperAdjunction :
    boundedConstructibleLowerStar l c.overG ⊣ boundedConstructibleUpperShriek l c.overG :=
  (boundedConstructibleUpperShriekAdjunction l c.overG).ofNatIsoLeft
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l c.overG)

variable (e : (boundedConstructibleUpperStarOfMap l (X := Y) (Y := Y') πY).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- The exact compactification exchange has invertible unit base change when its
specified open mate and proper unit base change are invertible. This uses the
compactification that defines the ambient exchange, including its two comparisons. -/
theorem isIso_smoothUnitBaseChange_fieldCompactification
    [IsIso ((mateEquiv
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l c.overI)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l c'.overI)
      (inv (purityFieldOpenRestrictedExchange l f f' c c' hi).hom)).app
        ((boundedConstructibleUpperShriek l c.overG).obj (𝟙_ _)))]
    [IsIso (Adjunction.unitBaseChange
      (purityCompactificationProperAdjunction l f c)
      (purityCompactificationProperAdjunction l f' c')
      (purityFieldProperRestrictedExchange l f f' c c' hg).hom e)] :
    IsIso (smoothUnitBaseChange l f f'
      (purityFieldLowerShriekExchange l f f' c c' hi hg) e) := by
  rw [purityFieldLowerShriekExchange_eq_paste]
  have he := Adjunction.isIso_unitBaseChange_pastedAdjunction
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l c.overI)
    (purityCompactificationProperAdjunction l f c)
    (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l c'.overI)
    (purityCompactificationProperAdjunction l f' c')
    (boundedConstructibleUpperShriekAdjunction l f')
    (purityFieldOpenRestrictedExchange l f f' c c' hi)
    (purityFieldProperRestrictedExchange l f f' c c' hg)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
      (compactificationOverField f) c)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
      c' (compactificationOverField f')).symm e
  exact he

end AlgebraicGeometry.ProEtale.CondensedRing
