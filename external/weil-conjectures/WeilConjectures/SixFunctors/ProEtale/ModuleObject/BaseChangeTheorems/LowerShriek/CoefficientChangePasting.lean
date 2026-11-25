/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!
# Coefficient changes and the base change morphisms for a compactification

Let `C` be a coefficient change `Λ ⟶ Λ'` of the bounded constructible six functors
(`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`). This file shows that the
exchange morphisms entering the compact-support base change are compatible with the coefficient
comparisons of `C`:

* the proper base change morphism `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`
  (`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange.squareCompatible_baseChange`);
* the exchange `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for extension by zero and its inverse
  (`...squareCompatible_openImmersionLowerShriekBaseChange`,
  `...squareCompatible_openImmersionLowerShriekBaseChangeIso`);
* the compact-support base change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` for a
  compactification `c` (`...squareCompatible_lowerShriekOfCompactificationBaseChangePasting`),
  for the coefficient comparisons `Rf_!^c ⋙ T ≅ T ⋙ Rf_!^c` pasted from (Shriek) and (Push)
  (`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange.shriekOfCompactification`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleCoefficientChange

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {ℓ : ℕ} [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {P : BoundedConstructiblePushforwardData Λ ℓ k}
  {P' : BoundedConstructiblePushforwardData Λ' ℓ k}
  {T : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom], Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧}
  {pull : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T X ≅ T Y ⋙ boundedConstructibleUpperStar Λ' ℓ f}
  (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The proper base change morphism `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is compatible with the
coefficient comparisons. -/
lemma squareCompatible_baseChange {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [IsProper f.left] [IsProper f'.left] (sq : CommSq g' f' f g) :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.push f) (pull g))
      (Functor.pasteSquareIso (pull g') (C.push f'))
      (P.baseChange sq) (P'.baseChange sq) :=
  NatTrans.SquareCompatible.exchangeRight (C.isMateSquare_pull_push f)
    (C.isMateSquare_pull_push f') (C.squareCompatible_pullbackSquareComparison sq)

section OpenImmersion

variable {j : X ⟶ Y} {g : Y' ⟶ Y} {j' : X' ⟶ Y'} {g' : X' ⟶ X} [IsOpenImmersion j.left]
  [IsOpenImmersion j'.left]

/-- The exchange `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for extension by zero is compatible with the
coefficient comparisons. -/
lemma squareCompatible_openImmersionLowerShriekBaseChange (sq : CommSq g' j' j g) :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (pull g') (C.shriek j'))
      (Functor.pasteSquareIso (C.shriek j) (pull g))
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq)
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ' ℓ sq) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
    boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft]
  exact NatTrans.SquareCompatible.exchangeLeft (C.isMateSquare_shriek_pull j)
    (C.isMateSquare_shriek_pull j') (C.squareCompatible_pullbackSquareComparison sq.flip)

/-- The base change isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` for extension by zero is compatible
with the coefficient comparisons. -/
lemma squareCompatible_openImmersionLowerShriekBaseChangeIso (sq : IsPullback g' j' j g) :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.shriek j) (pull g))
      (Functor.pasteSquareIso (pull g') (C.shriek j'))
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ' ℓ sq).hom := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ' ℓ sq
  exact (C.squareCompatible_openImmersionLowerShriekBaseChange sq.toCommSq).isIso_inv

end OpenImmersion

section Compactification

variable {f : X ⟶ Y}

/-- **(Shriek)** along a compactification `c = (X ⟶[i] Z ⟶[p] Y)`: the commutation
`Rf_!^c ⋙ T ≅ T ⋙ Rf_!^c` pasted from (Shriek) for `i` and (Push) for `p`. -/
noncomputable def shriekOfCompactification (c : Compactification f.left) :
    P.lowerShriekOfCompactification c ⋙ T Y ≅ T X ⋙ P'.lowerShriekOfCompactification c :=
  Functor.pasteSquareIso (C.shriek c.overI) (C.push c.overG)

variable {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The compact-support base change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` for a
compactification `c` of `f` and its base change `c'` is compatible with the coefficient
comparisons. -/
lemma squareCompatible_lowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.shriekOfCompactification c) (pull g))
      (Functor.pasteSquareIso (pull g')
        (C.shriekOfCompactification (c.ofIsPullback sq.overLeft)))
      (P.lowerShriekOfCompactificationBaseChangePasting c sq)
      (P'.lowerShriekOfCompactificationBaseChangePasting c sq) :=
  (NatTrans.SquareCompatible.associator_hom _ _ _).comp
    ((NatTrans.SquareCompatible.whiskerLeft _
      (C.squareCompatible_baseChange (c.overBaseChange_isPullback_g sq).toCommSq)).comp
    ((NatTrans.SquareCompatible.associator_inv _ _ _).comp
    ((NatTrans.SquareCompatible.whiskerRight _
      (C.squareCompatible_openImmersionLowerShriekBaseChangeIso
        (c.overBaseChange_isPullback_i sq))).comp
    (NatTrans.SquareCompatible.associator_hom _ _ _))))

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleCoefficientChange
