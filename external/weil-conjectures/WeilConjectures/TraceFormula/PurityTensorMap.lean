/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported

/-!

# The purity map and the exceptional base change map

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type. On the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` this file defines the two canonical maps through
which smooth purity is expressed (blueprint `proposition-exceptional-inverse-image-smooth-morphism`,
maps (G11) and (G12)):

- the *purity map* (or tensor map) `γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K`, the exceptional
  adjoint of the projection formula followed by the counit at the unit
  (`ProEtale.CondensedRing.upperShriekUnitTensorMap`);
- for a cartesian square, the *exceptional base change map* `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L`, the
  exceptional adjoint of the inverse of compact-support base change followed by the pulled-back
  counit (`ProEtale.CondensedRing.upperShriekBaseChange`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The *purity map* `γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K` of a morphism `f : X ⟶ Y`: the
exceptional adjoint of
```
Rf_! (Lf^* K ⊗ Rf^! ℚ̄_ℓ) ≅ Rf_! (Rf^! ℚ̄_ℓ ⊗ Lf^* K) ≅ Rf_! Rf^! ℚ̄_ℓ ⊗ K --ε ⊗ 1--> ℚ̄_ℓ ⊗ K ≅ K,
```
built from the tensor symmetry, the inverse of the projection formula for `f` and the counit of
`Rf_! ⊣ Rf^!`. -/
noncomputable def upperShriekUnitTensorMap (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ f).obj K ⊗
        (boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj K :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _
    ((boundedConstructibleLowerShriek ℓ f).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection ℓ f).app
        ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _))).app K) ≫
      ((boundedConstructibleUpperShriekAdjunction ℓ f).counit.app (𝟙_ _) ▷ K) ≫ (λ_ K).hom)

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *exceptional base change map* `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` of a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
(blueprint `proposition-exceptional-inverse-image-smooth-morphism`): the exceptional adjoint of
`Rf'_! Lg'^* Rf^! L ≅ Lg^* Rf_! Rf^! L --Lg^* ε--> Lg^* L`, the inverse of compact-support base
change followed by the pulled-back counit of `Rf_! ⊣ Rf^!`. -/
noncomputable def upperShriekBaseChange (sq : IsPullback g' f' f g)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ g').obj ((boundedConstructibleUpperShriek ℓ f).obj L) ⟶
      (boundedConstructibleUpperShriek ℓ f').obj
        ((boundedConstructibleUpperStar _ ℓ g).obj L) :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  (boundedConstructibleUpperShriekAdjunction ℓ f').homEquiv _ _
    (inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        ((boundedConstructibleUpperShriek ℓ f).obj L)) ≫
      (boundedConstructibleUpperStar _ ℓ g).map
        ((boundedConstructibleUpperShriekAdjunction ℓ f).counit.app L))

end AlgebraicGeometry.ProEtale.CondensedRing
