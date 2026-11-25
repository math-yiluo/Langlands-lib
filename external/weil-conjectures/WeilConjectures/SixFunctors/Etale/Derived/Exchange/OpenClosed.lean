/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Exchange morphisms for open immersions and open-closed immersions

Two elementary facts used in the proof of the Künneth formula:

- for an immersion `j : U ⟶ X` which is both open and closed and any `g : Y ⟶ X`, the base
  change map `g⁻¹ j_* F ⟶ h_* p⁻¹ F` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isOpenImmersion_of_isClosedImmersion`,
  blueprint `lem-kun-base-change-open-closed`). Such a `j` is finite, so this is the finite base
  change theorem `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`;
- for an open immersion `j : U ⟶ X`, `j⁻¹ j_* = id` (the counit of `j^* ⊣ j_*` is an
  isomorphism) and the Leray morphism `RΓ(X, Rj_* K) ⟶ RΓ(U, K)` is an isomorphism
  (`AlgebraicGeometry.Etale.isOpenImmersion_restriction_lowerStar`, blueprint
  `lem-kun-open-immersion-restriction`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section OpenClosed

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

/-- Blueprint `lem-kun-base-change-open-closed`: base change for open-closed immersions.

Let `j : U ⟶ X` be both an open and a closed immersion and `g : Y ⟶ X` a morphism, with
cartesian square

```
  W --p--> U
  |        |
  h        j
  v        v
  Y --g--> X
```

(`W = Y ×_X U`). Then for every sheaf `F` on `U_ét` the base change map `g⁻¹ j_* F ⟶ h_* p⁻¹ F`
of `AlgebraicGeometry.Etale.baseChangeMap` is an isomorphism. Since `j` is a closed immersion it
is finite, and this is the finite base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`, proved by comparing geometric stalks
as in the blueprint. -/
theorem isIso_baseChangeMap_of_isOpenImmersion_of_isClosedImmersion {U X Y W : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] (g : Y ⟶ X) (p : W ⟶ U)
    (h : W ⟶ Y) [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (sq : IsPullback p h j g) (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.baseChangeMap A sq.toCommSq).app F) :=
  have := Etale.isIso_baseChangeMap_of_isFinite A sq
  inferInstance

end OpenClosed

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lem-kun-open-immersion-restriction`: inverse image along an open immersion is a
left inverse of direct image.

For an open immersion `j : U ⟶ X`:
- the counit `j^* j_* F ⟶ F` of `j^* ⊣ j_*` is an isomorphism, i.e. `j⁻¹ j_* = id` on sheaves
  on `U_ét` (the pushforward along `j` is fully faithful,
  `AlgebraicGeometry.Etale.fullyFaithfulLowerStarOfIsOpenImmersion`);
- for every `K` in `D(U_ét)` the canonical (Leray) morphism `RΓ(X, Rj_* K) ⟶ RΓ(U, K)` of
  `AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` is an
  isomorphism. -/
theorem isOpenImmersion_restriction_lowerStar :
    IsIso (Etale.upperStarLowerStarAdjunction A j).counit ∧
      ∀ K : DerivedCategory (Sheaf U.smallEtaleTopology A),
        IsIso ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A j).hom.app K) :=
  ⟨(Etale.upperStarLowerStarAdjunction A j).counit_isIso_of_R_fully_faithful,
    fun _ ↦ inferInstance⟩

end OpenImmersion

end Etale

end AlgebraicGeometry
