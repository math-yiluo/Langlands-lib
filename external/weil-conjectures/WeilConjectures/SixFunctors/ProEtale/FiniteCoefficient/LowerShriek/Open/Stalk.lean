/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

/-!
# The pointwise description of the pro-étale extension by zero

Let `j : U ⟶ X` be an open immersion. The extension by zero `j_!` on sheaves for the small
pro-étale sites is the exact left adjoint of `j^*`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`,
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`), so it acts
degreewise on complexes, as `D(j_!)`. This file proves the stalk prescription of blueprint
`proposition-extension-zero-restriction-closed-subscheme`, in the form of the pullback along an
arbitrary morphism `s : T ⟶ X` (for instance a geometric point `Spec k̄ ⟶ X`, along which the
pullback computes the stalk):

* if `s = t ≫ j` factors through `U`, then `s^* j_! K ≅ t^* K`
  (`AlgebraicGeometry.ProEtale.openImmersionLowerShriekCompUpperStarIsoOfFac`), by base change
  for the extension by zero along the cartesian square `t ≫ j = 𝟙 ≫ s`;
* if the range of `s` misses `U`, then `s^* j_! K = 0`
  (`AlgebraicGeometry.ProEtale.isZero_upperStar_openImmersionLowerShriek`).

Both statements are also given for complexes.

## Main definitions

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekIdIso`: `(𝟙 X)_! ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekCompUpperStarIsoOfFac`: `s^* j_! ≅ t^*`
  for `s = t ≫ j`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The extension by zero along the identity is the identity: `(𝟙 X)_! ≅ 𝟭`, both being left
adjoint to `(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def openImmersionLowerShriekIdIso (X : Scheme.{u}) :
    (𝟙 X)_!open[A] ≅ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction A (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (upperStarId A X).symm)

variable {U X T : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j` and `t : T ⟶ U`, the square `t ≫ j = 𝟙 ≫ (t ≫ j)` is cartesian,
`j` being a monomorphism. -/
lemma isPullback_id_of_fac (t : T ⟶ U) (s : T ⟶ X) (h : t ≫ j = s) :
    IsPullback t (𝟙 T) j s :=
  IsPullback.of_vert_isIso_mono ⟨by rw [h, id_comp]⟩

/-- **The extension by zero pulled back along a morphism factoring through `U`**: for an open
immersion `j : U ⟶ X` and `s = t ≫ j`, `s^* j_! ≅ t^*`. It is the base change isomorphism of
the extension by zero for the cartesian square `t ≫ j = 𝟙 ≫ s`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekBaseChangeIso`), with `(𝟙 T)_! ≅ 𝟭`. -/
noncomputable def openImmersionLowerShriekCompUpperStarIsoOfFac (t : T ⟶ U) (s : T ⟶ X)
    (h : t ≫ j = s) :
    (j)_!open[A] ⋙ (s)^*[A] ≅ (t)^*[A] :=
  (openImmersionLowerShriekBaseChangeIso A (isPullback_id_of_fac j t s h)).symm ≪≫
    Functor.isoWhiskerLeft _ (openImmersionLowerShriekIdIso A T) ≪≫ Functor.rightUnitor _

/-- The derived counterpart of
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekCompUpperStarIsoOfFac`: for an open
immersion `j` and `s = t ≫ j`, `D(s^*) D(j_!) ≅ D(t^*)` on complexes. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekCompUpperStarIsoOfFac
    (t : T ⟶ U) (s : T ⟶ X) (h : t ≫ j = s) :
    D((j)_!open[A]) ⋙ D((s)^*[A]) ≅ D((t)^*[A]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekCompUpperStarIsoOfFac A j t s h)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: Extension by zero on the
pro-etale site.

The extension by zero `j_!` along an open immersion `j : U ⟶ X` on the small pro-étale sites is
the exact left adjoint of `j^*`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`,
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`), it acts degreewise
on complexes, as `D(j_!)`, and it has the stalk prescription of the étale extension by zero:
for a complex `K` on `U` and a morphism `s : T ⟶ X` (e.g. a geometric point of `X`),

* if `s = t ≫ j` factors through `U`, then `s^* j_! K ≅ t^* K` (this statement);
* if the range of `s` misses `U`, then `s^* j_! K = 0`
  (`AlgebraicGeometry.ProEtale.isZero_mapDerivedCategory_upperStar_openImmersionLowerShriek`).
-/
theorem nonempty_iso_mapDerivedCategory_upperStar_openImmersionLowerShriek (t : T ⟶ U)
    (s : T ⟶ X) (h : t ≫ j = s) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
    Nonempty (D((s)^*[A]).obj (D((j)_!open[A]).obj K) ≅ D((t)^*[A]).obj K) :=
  ⟨(mapDerivedCategoryOpenImmersionLowerShriekCompUpperStarIsoOfFac A j t s h).app K⟩

/-- The pullback of a complex `D(j_!) K` along a morphism `s` missing the range of the open
immersion `j` vanishes (blueprint `proposition-extension-zero-restriction-closed-subscheme`, the
stalks outside `U`). -/
theorem isZero_mapDerivedCategory_upperStar_openImmersionLowerShriek (s : T ⟶ X)
    (hjs : Set.range j.base ∩ Set.range s.base = ∅)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
    IsZero (D((s)^*[A]).obj (D((j)_!open[A]).obj K)) :=
  ((j)_!open[A] ⋙ (s)^*[A]).isZero_mapDerivedCategory_obj K
      (fun _ ↦ ProEtale.isZero_upperStar_openImmersionLowerShriek A j s hjs _) |>.of_iso
    ((Functor.mapDerivedCategoryCompIso _ _).app K)

end ProEtale

end AlgebraicGeometry
