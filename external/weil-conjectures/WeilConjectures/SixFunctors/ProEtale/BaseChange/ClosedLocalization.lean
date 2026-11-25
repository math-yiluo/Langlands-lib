/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Closed-site operations under weakly étale localization

Let `i : Z ⟶ X` be a closed immersion, `w : W ⟶ X` weakly étale, and
`Z_W = W ×_X Z` with projections `i_W : Z_W ⟶ W` and `w_Z : Z_W ⟶ Z`. Restriction to `W`
commutes with the closed direct image, `w^* i_* ≅ i_W* w_Z^*`
(`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isClosedImmersion`), and the two composites
of inverse images agree, `i_W^* w^* ≅ w_Z^* i^*`
(`AlgebraicGeometry.ProEtale.upperStarSquareIso`). The first isomorphism is the mate of the
square of direct images, hence compatible with the units and counits of `i^* ⊣ i_*` and
`i_W^* ⊣ i_W*` (blueprint `proposition-extension-zero-restriction-closed-subscheme`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z X W ZW : Scheme.{u}} {i : Z ⟶ X} {w : W ⟶ X} {iW : ZW ⟶ W} {wZ : ZW ⟶ Z}

/-- The two composites of inverse images around a commutative square `iW ≫ w = wZ ≫ i`
agree: `w^* ⋙ iW^* ≅ i^* ⋙ wZ^*`. -/
noncomputable def upperStarSquareIso (sq : CommSq iW wZ w i) :
    (w)^*[A] ⋙ (iW)^*[A] ≅ (i)^*[A] ⋙ (wZ)^*[A] :=
  (upperStarComp A iW w).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫ upperStarComp A wZ i

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`proposition-extension-zero-restriction-closed-subscheme`): for the cartesian square of a closed
immersion `i : Z ⟶ X` and a weakly étale `w : W ⟶ X`, restriction to `W` commutes with the underived
closed direct image: the base change map `i_* ⋙ w^* ⟶ w_Z^* ⋙ i_W*`
(`AlgebraicGeometry.ProEtale.baseChangeMap`) is an isomorphism. This is the weakly étale base change
theorem `AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback` applied to `i`; that `i` is a
closed immersion is not used. The two composites of inverse images agree by
`AlgebraicGeometry.ProEtale.upperStarSquareIso`. -/
theorem isIso_baseChangeMap_of_isClosedImmersion [WeaklyEtale w] [WeaklyEtale wZ]
    (hsq : IsPullback iW wZ w i) :
    IsIso (baseChangeMap A hsq.toCommSq) :=
  isIso_baseChangeMap_of_isPullback A hsq

end ProEtale

end AlgebraicGeometry
