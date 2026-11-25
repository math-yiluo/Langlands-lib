/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint

/-!

# The exceptional inverse image on bounded constructible module objects

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
separated and of finite type over `Spec k`, and all morphisms are morphisms of
`Over (Spec (.of k))`.

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is constructed on the bounded
constructible derived categories directly, out of the two halves of the derived lower shriek
attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
```
Rf_!(c) := i_! ⋙ Rg_*,      Rf^!(c) := Rg^! ⋙ i^*,
```
where `i_! ⊣ i^*` is the adjunction along the open immersion `i` on bounded constructible
complexes (`boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction`) and `Rg^!` is a
chosen right adjoint of the bounded constructible pushforward `Rg_*` along the proper `g`. The
adjunction `Rf_!(c) ⊣ Rf^!(c)` is the composite of these two adjunctions.

The only input is that `Rg_*` on bounded constructible complexes is a left adjoint for proper `g`
(`isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`,
`isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`,
`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`; see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint`). As the
pushforward on bounded constructible complexes, everything is stated for each of the `ℓ`-adic
coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` (in the namespaces `ProEtale.CondensedRing`,
`ProEtale.CondensedRing.ContinuousMapRingObj` and `ProEtale.CondensedRing.PadicIntegersRingObj`).

Exactly as the lower shriek `boundedConstructibleLowerShriek`, the functor `Rf^!` is `Rf^!(c)`
for the compactification `c = compactificationOverField f` chosen by Nagata's theorem, and the
adjunction `Rf_! ⊣ Rf^!` is the adjunction `Rf_!(c) ⊣ Rf^!(c)`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification`: `Rf^!(c)` on
  bounded constructible complexes, right adjoint to the lower shriek
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction`: the
  adjunction `Rf_!(c) ⊣ Rf^!(c)`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriek`:
  `Rf^! : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for the chosen compactification, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`: the adjunction
  `Rf_! ⊣ Rf^!`.

## The input

- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`,
  `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj` and
  `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `ℚ̄_ℓ`-, `E`- and `𝒪_E`-sheaves is a left
  adjoint, over any field (in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint`).

## Implementation notes

`Rg^!` for proper `g` is `Functor.rightAdjoint`, an arbitrary choice of right adjoint extracted
from the instance, not a construction. Only the adjunction `Adjunction.ofIsLeftAdjoint` should be
used about it.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The adjunction along a compactification -/

section OfCompactification

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` attached to a
compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen
right adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the
pullback `i^*` along the open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleLowerStar ℓ c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f` (`ℚ̄_ℓ`-coefficient): the composite of the
adjunction `i_! ⊣ i^*` along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the
proper `g`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⊣
      boundedConstructibleUpperShriekOfCompactification ℓ c :=
  -- on the general `Rg_*` (as `boundedConstructibleUpperShriekOfCompactification`): from the
  -- expected type the implicit functors would be the proper-only ones, which costs every user
  ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ c.overI).comp
    (Adjunction.ofIsLeftAdjoint (boundedConstructibleLowerStar ℓ c.overG)) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        c.overI ⋙ boundedConstructibleLowerStar ℓ c.overG ⊣
      (boundedConstructibleLowerStar ℓ c.overG).rightAdjoint ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)

/-- The lower shriek `Rf_!(c)` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperShriekOfCompactification` (`ℚ̄_ℓ`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleLowerShriekOfCompactification :
    (boundedConstructibleLowerShriekOfCompactification ℓ c).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ c).isLeftAdjoint

/-- The exceptional inverse image `Rf^!(c)` on bounded constructible complexes is a right
adjoint, its left adjoint being `boundedConstructibleLowerShriekOfCompactification`
(`ℚ̄_ℓ`-coefficient). -/
instance isRightAdjoint_boundedConstructibleUpperShriekOfCompactification :
    (boundedConstructibleUpperShriekOfCompactification ℓ c).IsRightAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ c).isRightAdjoint

end OfCompactification

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

section OfCompactification

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` attached to a
compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen right
adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the pullback
`i^*` along the open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  (boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f` (`E`-coefficient): the composite of the adjunction
`i_! ⊣ i^*` along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`.
-/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⊣
      boundedConstructibleUpperShriekOfCompactification ℓ E c :=
  -- on the general `Rg_*` (as `boundedConstructibleUpperShriekOfCompactification`): from the
  -- expected type the implicit functors would be the proper-only ones, which costs every user
  ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.continuousMapRingObj E) ℓ
    c.overI).comp
    (Adjunction.ofIsLeftAdjoint (boundedConstructibleLowerStar ℓ E c.overG)) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ c.overI ⋙
        boundedConstructibleLowerStar ℓ E c.overG ⊣
      (boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ c.overI)

/-- The lower shriek `Rf_!(c)` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperShriekOfCompactification` (`E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleLowerShriekOfCompactification :
    (boundedConstructibleLowerShriekOfCompactification ℓ E c).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c).isLeftAdjoint

/-- The exceptional inverse image `Rf^!(c)` on bounded constructible complexes is a right
adjoint, its left adjoint being `boundedConstructibleLowerShriekOfCompactification`
(`E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleUpperShriekOfCompactification :
    (boundedConstructibleUpperShriekOfCompactification ℓ E c).IsRightAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c).isRightAdjoint

end OfCompactification

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

section OfCompactification

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` attached to a
compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen
right adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the
pullback `i^*` along the open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  (boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f` (`𝒪_E`-coefficient): the composite of the adjunction
`i_! ⊣ i^*` along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`.
-/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⊣
      boundedConstructibleUpperShriekOfCompactification ℓ E c :=
  -- on the general `Rg_*` (as `boundedConstructibleUpperShriekOfCompactification`): from the
  -- expected type the implicit functors would be the proper-only ones, which costs every user
  ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicIntegersRingObj ℓ E) ℓ
    c.overI).comp
    (Adjunction.ofIsLeftAdjoint (boundedConstructibleLowerStar ℓ E c.overG)) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI ⋙
        boundedConstructibleLowerStar ℓ E c.overG ⊣
      (boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI)

/-- The lower shriek `Rf_!(c)` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperShriekOfCompactification` (`𝒪_E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleLowerShriekOfCompactification :
    (boundedConstructibleLowerShriekOfCompactification ℓ E c).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c).isLeftAdjoint

/-- The exceptional inverse image `Rf^!(c)` on bounded constructible complexes is a right
adjoint, its left adjoint being `boundedConstructibleLowerShriekOfCompactification`
(`𝒪_E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleUpperShriekOfCompactification :
    (boundedConstructibleUpperShriekOfCompactification ℓ E c).IsRightAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c).isRightAdjoint

end OfCompactification

end PadicIntegersRingObj

/-! ### The adjunction `Rf_! ⊣ Rf^!` -/

section Chosen

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification`
attached to the chosen compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperShriekOfCompactification ℓ (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes (`ℚ̄_ℓ`-coefficient): the
adjunction `Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek ℓ f ⊣ boundedConstructibleUpperShriek ℓ f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek` (`ℚ̄_ℓ`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).isLeftAdjoint

/-- `Rf^!` on bounded constructible complexes is a right adjoint (`ℚ̄_ℓ`-coefficient). -/
instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).isRightAdjoint

end Chosen

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

section Chosen

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification`
attached to the chosen compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek :
    Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleUpperShriekOfCompactification ℓ E (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes (`E`-coefficient): the
adjunction `Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek ℓ E f ⊣ boundedConstructibleUpperShriek ℓ E f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek` (`E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek ℓ E f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction ℓ E f).isLeftAdjoint

/-- `Rf^!` on bounded constructible complexes is a right adjoint (`E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek ℓ E f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction ℓ E f).isRightAdjoint

end Chosen

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

section Chosen

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification`
attached to the chosen compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek :
    Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleUpperShriekOfCompactification ℓ E (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes (`𝒪_E`-coefficient): the
adjunction `Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek ℓ E f ⊣ boundedConstructibleUpperShriek ℓ E f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek` (`𝒪_E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek ℓ E f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction ℓ E f).isLeftAdjoint

/-- `Rf^!` on bounded constructible complexes is a right adjoint (`𝒪_E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek ℓ E f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction ℓ E f).isRightAdjoint

end Chosen

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
