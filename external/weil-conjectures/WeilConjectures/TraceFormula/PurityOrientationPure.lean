/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.SmoothPurity.OrientationBaseChange
public import WeilConjectures.SmoothPurity.TateTwistDualizable
public import WeilConjectures.SmoothPurity.UpperShriekUnitDualizable
public import WeilConjectures.TraceFormula.DualizableShift
public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeDualizable

/-!

# The orientation of a morphism smooth of pure relative dimension

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`. The trace isomorphism
`ℚ̄_ℓ(d)[2d] ≅ Rf^! ℚ̄_ℓ` (`ProEtale.CondensedRing.isIso_smoothPurityMap`, built from the smooth
trace `ProEtale.CondensedRing.smoothTrace` of `WeilConjectures.SmoothPurity.Defs`) gives the two
properties of the relative dualizing complex `ω_f = Rf^! ℚ̄_ℓ` used by the proof of smooth purity
for `ℚ̄_ℓ`-coefficients:

- `ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smoothOfRelativeDimension`: `ω_f` is
  dualizable, the Tate twists being invertible;
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_unit_of_smoothOfRelativeDimension`: the
  formation of `ω_f` commutes with base change, the orientation being compatible with base change.

## Inputs

- `ProEtale.CondensedRing.isDualizable_boundedConstructibleTateTwist`: the Tate twist
  `ℚ̄_ℓ,X(d)` is invertible (blueprint `definition-tate-twists` (3), subsection
  `proposition-purity-vector-bundles`).
- `ProEtale.CondensedRing.smoothOrientation_baseChange`: the compatibility of the orientation
  `γ_f` with base change (SGA 4, Exposé XVIII, Théorème 2.9 (Var 4); blueprint
  `proposition-compatibility-purity-base-change` at the unit), required from the smooth purity
  section. Since the purity map is the orientation, this is
  `ProEtale.CondensedRing.exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The purity map is compatible with base change** (SGA 4, Exposé XVIII, Théorème 2.9
(Var 4); blueprint `proposition-compatibility-purity-base-change` at the unit): for a cartesian
square with `f` (hence `f'`) smooth of pure relative dimension `d`, the pullback of the purity map
`ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ`, followed by the exceptional base change map at the unit, is the purity
map of `f'` up to an isomorphism of the Tate twists. The purity map is the orientation
(`smoothPurityMap_eq_smoothOrientation`), so this is `smoothOrientation_baseChange`. -/
theorem exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothPurityMap ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)) =
        τ.hom ≫ smoothPurityMap ℓ f' d := by
  simpa only [smoothPurityMap_eq_smoothOrientation] using smoothOrientation_baseChange ℓ sq d

/-- **The formation of the relative dualizing complex of a morphism smooth of pure relative
dimension commutes with base change**: the exceptional base change map at the unit is an
isomorphism, since, through the trace isomorphisms, it is an isomorphism of Tate twists
(`exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange`). -/
theorem isIso_upperShriekBaseChange_unit_of_smoothOfRelativeDimension (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    IsIso (upperShriekBaseChange ℓ sq (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  obtain ⟨τ, hτ⟩ := exists_iso_map_smoothPurityMap_comp_upperShriekBaseChange ℓ sq d
  have h : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
      (smoothPurityMap ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
        (boundedConstructibleUpperShriek ℓ f').map
          (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g))) := by
    rw [hτ]
    infer_instance
  have h' := IsIso.of_isIso_comp_left ((boundedConstructibleUpperStar
    (Profinite.padicAlgClRingObj ℓ) ℓ g').map (smoothPurityMap ℓ f d))
    (upperShriekBaseChange ℓ sq (𝟙_ _) ≫
      (boundedConstructibleUpperShriek ℓ f').map
        (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)))
  exact IsIso.of_isIso_comp_right _ ((boundedConstructibleUpperShriek
    ℓ f').map
      (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)))

end AlgebraicGeometry.ProEtale.CondensedRing
