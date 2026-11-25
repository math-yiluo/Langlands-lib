/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The composition law for `Rf_!` and its mate

Two statements of the six-functor bookkeeping that the purity chapter uses: the
identification `Rf_! ≅ Rf_*` for proper `f`, and the mate of the composition isomorphism,
`R(g ∘ f)^! ≅ Rf^! Rg^!`. The composition isomorphism `R(g ∘ f)_! ≅ Rf_! ⋙ Rg_!` itself is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.

The compactification-independence that makes `Rf_!` well defined is already in the
repository, as
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`
together with its identity and composition coherences; it is not restated here.

## Implementation notes

On the unbounded derived categories the composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` is
only stated to exist, so the mate statement
`AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq` is existential in it;
being formal, it holds for every such isomorphism. The canonical composition isomorphism on the
bounded below derived categories, with its unit and associativity laws, is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y S : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- Blueprint `proposition-forgetting-supports-composition--3`: Proper coincidence

**Proper coincidence.** For `f : X ⟶ Y` proper the identity is a compactification of `f`, and
the resulting canonical identification

`Rf_! ≅ Rf_*`

is independent of the compactification.

At the level of sheaves this is `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`, which
states that the *canonical comparison* `f_! ⟶ f_*` is an isomorphism; the derived comparison
map has not been constructed, so only the existence of the derived isomorphism is recorded
here. -/
theorem nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar (f : X ⟶ Y)
    [HasCompactification f] [IsProper f] :
    Nonempty (R(f)_![A] ≅ R((f)_*[A])) := by
  let c := HasCompactification.compactification f
  -- the open immersion of the compactification is proper, so it has closed range and `j_! ≅ j_*`
  have := Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  let ι := asIso (Etale.openImmersionLowerShriekToLowerStar A c.i)
  have : PreservesFiniteColimits (c.i)_*[A] := preservesFiniteColimits_of_natIso ι
  have : PreservesFiniteLimits (c.i)_*[A] := preservesFiniteLimits_of_natIso ι
  exact ⟨Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso ι) R((c.g)_*[A]) ≪≫
    Functor.isoWhiskerRight ((c.i)_*[A].rightDerivedFunctorIsoMapDerivedCategory).symm
      R((c.g)_*[A]) ≪≫ rightDerivedLowerStarComp A c.i c.g ≪≫
    rightDerivedLowerStarCongr A c.comm.symm⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`: Mate calculus for a
pasted adjunction

Clause (b), étale form: for composable `f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications
and torsion coefficients, there is a composition isomorphism `e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
(`proposition-composition-base-change-rf-shriek--1`) whose mate `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!` under the
adjunctions `Rf_! ⊣ Rf^!` on the unbounded derived categories of the small étale sites carries the
adjunction `R(f ≫ g)_! ⊣ R(f ≫ g)^!` to the composite adjunction `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`:
the unit and counit of the composite adjunction are the pasted ones. The mate statement is
formal (`CategoryTheory.Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv`); the
composition isomorphism is `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`.
The constructible form, on the small pro-étale sites, is
`AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq`. -/
theorem exists_rightDerivedUpperShriekAdjunction_comp_eq (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    ∃ e : R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
        R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
      ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft e).ofNatIsoRight
        (conjugateIsoEquiv
          ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))
          (rightDerivedUpperShriekAdjunction _ (f ≫ g)) e).symm =
        (rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨e, Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ e⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`: Mate calculus for a
pasted adjunction

**The mate of the composition isomorphism.** For composable `f : X ⟶ Y` and `g : Y ⟶ S` and
torsion coefficients,

```
  R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!           (left adjoints,
  proposition-composition-base-change-rf-shriek--1)
        ⊣              ⊣
  R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!           (right adjoints, the mate)
```

the mate of the composition isomorphism is an isomorphism `R(g ∘ f)^! ≅ Rf^! ∘ Rg^!`: right
adjoints of isomorphic functors are isomorphic, and the right adjoint of a composite is the
composite of the right adjoints. The composition isomorphism of the lower shrieks is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, which needs torsion
coefficients.

This is clause (b) of `proposition-composition-open-restriction-compactifications-f--1` in its étale
form, for morphisms admitting a compactification (`theorem-existence-exceptional-inverse-image`(a));
that it is the mate, with the pasted unit and counit, is
`AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq`. Clause (a), the
pro-étale ambient form, is the theorem `ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv` in the
namespace `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`.
The hypothesis `HasCompactification (f ≫ g)` is redundant over a quasi-compact
quasi-separated base, by Nagata's theorem; it is kept because no composition instance for
`HasCompactification` is available in general. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    Nonempty (R(f ≫ g)^![Λ] ≅
      R(g)^![Λ] ⋙ R(f)^![Λ]) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨Adjunction.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft e)
    ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))⟩

end Etale

end AlgebraicGeometry
