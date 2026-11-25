/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint
public import WeilConjectures.SmoothPurity.EtaleUpperShriek

/-!
# The exceptional base change map along étale maps and open immersions (A1', step 2)

Let `h : U ⟶ X` be a morphism over `k₁`, `h' : U' ⟶ X'` a morphism over `k₂` with
`πU ≫ h = h' ≫ πX`, and `Ex : Rh_! ⋙ πX^* ≅ πU^* ⋙ Rh'_!` a compact-support exchange (in the
local proof of `IsIso smoothUnitBaseChange`, the value at `h` of the global, composition
compatible exchange). The mate of `Ex` under `Rh_! ⊣ Rh^!` and `Rh'_! ⊣ Rh'^!` is the exceptional
base change map `πU^* Rh^! ⟶ Rh'^! πX^*` (`upperShriekMateOfMap` of
`WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp`). For `h` étale (in particular an
open immersion) it is an isomorphism at **every** object `N`:

* `Rh_!` is also left adjoint to the pullback `h^*` (for an open immersion this is
  `boundedConstructibleOpenImmersionUpperStarAdjunction`, from `Rh^! ≅ h^*`; for an étale map it
  is the named input `nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale`);
* the mate of `Ex` with respect to `Rh_! ⊣ Rh^!` is, up to the isomorphisms `Rh^! ≅ h^*`, its mate
  with respect to `Rh_! ⊣ h^*` (`CategoryTheory.Adjunction.mateEquiv_app_eq_conjugateEquiv`), so
  the two are invertible at the same objects
  (`isIso_upperShriekMate_app_iff_of_adjunction`);
* the mate of `Ex` with respect to `Rh_! ⊣ h^*` is a map `πU^* h^* ⟶ h'^* πX^*`. The
  compatibility of `Ex` with these adjunctions says that it is the composition isomorphism of the
  pullbacks `upperStarOfMapSquareIso` (equivalently, `Ex⁻¹` is the canonical exchange
  `h'_! πU^* ⟶ πX^* h_!` built from the unit and counit of `h_! ⊣ h^*` and the pullback
  composition isomorphism). Under this compatibility the exceptional base change map is invertible
  (`isIso_upperShriekMate_app_of_isOpenImmersion`, `isIso_upperShriekMate_app_of_etale`).

The compatibility is a property of the global exchange `Ex` and is stated as a hypothesis
(`hEx`); invertibility is independent of the chosen adjunctions `h_! ⊣ h^*`
(`isIso_upperShriekMate_app_iff_of_adjunction`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

/-! The lemmas `CategoryTheory.Adjunction.mateEquiv_app_eq_conjugateEquiv` and
`CategoryTheory.Adjunction.isIso_mateEquiv_app_iff` (change of right adjoints in the mates
correspondence) are in `WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale`. -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]

section OpenImmersionAdjunction

variable {U X : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The adjunction `Rj_! ⊣ j^*` of an open immersion, with `j^*` written as the pullback along
the underlying morphism of schemes: the adjunction `Rj_! ⊣ Rj^!` transported along
`Rj^! ≅ j^*` (`boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl`). -/
def boundedConstructibleOpenImmersionUpperStarAdjunction :
    boundedConstructibleLowerShriek l j ⊣
      boundedConstructibleUpperStarOfMap l (X := X) (Y := U) j.left :=
  (boundedConstructibleUpperShriekAdjunction l j).ofNatIsoRight
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl l j)

end OpenImmersionAdjunction

/-! `Rh_! ⊣ h^*` for étale `h`:
`nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale`
and `boundedConstructibleLowerShriekUpperStarAdjunctionOfEtale` in
`WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale`. -/

section Mate

variable {U X : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {U' X' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  (h : U ⟶ X) (h' : U' ⟶ X')
  {πU : U'.left ⟶ U.left} {πX : X'.left ⟶ X.left}
  (Ex : boundedConstructibleLowerShriek l h ⋙ boundedConstructibleUpperStarOfMap l πX ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l h')

/-- The composition isomorphism `πU^* h^* ≅ h'^* πX^*` of the pullbacks around a commutative
square `πU ≫ h = h' ≫ πX`. -/
def upperStarOfMapSquareIso (w : πU ≫ h.left = h'.left ≫ πX) :
    boundedConstructibleUpperStarOfMap l (X := X) (Y := U) h.left ⋙
        boundedConstructibleUpperStarOfMap l πU ≅
      boundedConstructibleUpperStarOfMap l πX ⋙
        boundedConstructibleUpperStarOfMap l (X := X') (Y := U') h'.left :=
  (boundedConstructibleUpperStarOfMapComp l h.left πU).symm ≪≫ eqToIso (by rw [w]) ≪≫
    boundedConstructibleUpperStarOfMapComp l πX h'.left

/-- The exceptional base change map `πU^* Rh^! N ⟶ Rh'^! πX^* N` (the mate of `Ex` under
`Rh_! ⊣ Rh^!` and `Rh'_! ⊣ Rh'^!`) is invertible exactly when the mate of `Ex` with respect to any
other adjunctions `Rh_! ⊣ R`, `Rh'_! ⊣ R'` is. -/
theorem isIso_upperShriekMate_app_iff_of_adjunction
    {R : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧ ⥤
      Dᵇc(U.left)⟦Profinite.padicAlgClRingObj l⟧}
    {R' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj l⟧ ⥤
      Dᵇc(U'.left)⟦Profinite.padicAlgClRingObj l⟧}
    (adj : boundedConstructibleLowerShriek l h ⊣ R)
    (adj' : boundedConstructibleLowerShriek l h' ⊣ R')
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction l h)
        (boundedConstructibleUpperShriekAdjunction l h') (inv Ex.hom)).app N) ↔
      IsIso ((mateEquiv adj adj' (inv Ex.hom)).app N) :=
  Adjunction.isIso_mateEquiv_app_iff _ _ _ _ _ N

/-- **The exceptional base change map along a map with `Rh_! ⊣ h^*`**: if the mate of `Ex` under
adjunctions `Rh_! ⊣ h^*` and `Rh'_! ⊣ h'^*` is the composition isomorphism of the pullbacks, then
the exceptional base change map `πU^* Rh^! N ⟶ Rh'^! πX^* N` is invertible for every `N`. -/
theorem isIso_upperShriekMate_app_of_adjunction
    (adj : boundedConstructibleLowerShriek l h ⊣
      boundedConstructibleUpperStarOfMap l (X := X) (Y := U) h.left)
    (adj' : boundedConstructibleLowerShriek l h' ⊣
      boundedConstructibleUpperStarOfMap l (X := X') (Y := U') h'.left)
    (w : πU ≫ h.left = h'.left ≫ πX)
    (hEx : (mateEquiv adj adj' (inv Ex.hom)) = (upperStarOfMapSquareIso l h h' w).hom)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction l h)
      (boundedConstructibleUpperShriekAdjunction l h') (inv Ex.hom)).app N) := by
  rw [isIso_upperShriekMate_app_iff_of_adjunction l h h' Ex adj adj', hEx]
  infer_instance

/-- **Step 2 for open immersions**: if `Ex` is compatible with the adjunctions `Rj_! ⊣ j^*`
(its mate under them is the composition isomorphism of the pullbacks), the exceptional base
change map `πU^* Rh^! N ⟶ Rh'^! πX^* N` is invertible for every `N`. -/
theorem isIso_upperShriekMate_app_of_isOpenImmersion [IsOpenImmersion h.left]
    [IsOpenImmersion h'.left] (w : πU ≫ h.left = h'.left ≫ πX)
    (hEx : (mateEquiv (boundedConstructibleOpenImmersionUpperStarAdjunction l h)
        (boundedConstructibleOpenImmersionUpperStarAdjunction l h') (inv Ex.hom)) =
      (upperStarOfMapSquareIso l h h' w).hom)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction l h)
      (boundedConstructibleUpperShriekAdjunction l h') (inv Ex.hom)).app N) :=
  isIso_upperShriekMate_app_of_adjunction l h h' Ex _ _ w hEx N

/-- **Step 2 for étale maps**: if `Ex` is compatible with some adjunctions `Rh_! ⊣ h^*` and
`Rh'_! ⊣ h'^*` (its mate under them is invertible, e.g. the composition isomorphism of the
pullbacks), the exceptional base change map `πU^* Rh^! N ⟶ Rh'^! πX^* N` is invertible for every
`N`. Such adjunctions exist by
`nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale`, and the hypothesis does not
depend on their choice (`isIso_upperShriekMate_app_iff_of_adjunction`). -/
theorem isIso_upperShriekMate_app_of_etale
    (hEx : ∃ (adj : boundedConstructibleLowerShriek l h ⊣
        boundedConstructibleUpperStarOfMap l (X := X) (Y := U) h.left)
      (adj' : boundedConstructibleLowerShriek l h' ⊣
        boundedConstructibleUpperStarOfMap l (X := X') (Y := U') h'.left),
        IsIso (mateEquiv adj adj' (inv Ex.hom)))
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction l h)
      (boundedConstructibleUpperShriekAdjunction l h') (inv Ex.hom)).app N) := by
  obtain ⟨adj, adj', hiso⟩ := hEx
  rw [isIso_upperShriekMate_app_iff_of_adjunction l h h' Ex adj adj']
  infer_instance

end Mate

end AlgebraicGeometry.ProEtale.CondensedRing
