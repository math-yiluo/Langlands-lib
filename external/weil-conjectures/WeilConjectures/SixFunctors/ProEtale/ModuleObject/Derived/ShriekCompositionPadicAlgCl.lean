/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange

/-!
# Composition of the derived lower shriek on bounded constructible `ℚ̄_ℓ`-complexes

The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square of an open immersion and
a proper morphism, and, for the coefficient ring `ℚ̲̄_ℓ`, the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`. The construction is explained in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`, which also treats
the coefficient rings `E̲` and the upper shriek.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`: the
  exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`:
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The exchange morphism -/

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k

/-- The *unit insertion* step of the exchange morphism (`ℚ̄_ℓ`-coefficient): the natural
transformation `Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the
adjunction `Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ p').unit

/-- The *square transport* step of the exchange morphism (`ℚ̄_ℓ`-coefficient):
`Functor.squareTransport` applied to the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅
Lp^* ⋙ i'_!` of the cartesian square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ p') ≅
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ p') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ p)
    (boundedConstructibleLowerStar ℓ p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ) ℓ sq)

/-- The *counit contraction* step of the exchange morphism (`ℚ̄_ℓ`-coefficient): the natural
transformation `(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of
the adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep :
    (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ p') ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions (`ℚ̄_ℓ`-coefficient): the mate, under the adjunctions `Lp^* ⊣
Rp_*` and `Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙
i'_!` (`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of
the unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep ℓ ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep ℓ sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep ℓ

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` is the exchange morphism
`boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`: the two
extension-by-zero base-change morphisms they are built from are the same exchange morphism. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq =
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq := by
  have e : boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
      (Profinite.padicAlgClRingObj ℓ) ℓ sq =
      boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
        (Profinite.padicAlgClRingObj ℓ) ℓ sq := by
    refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
    change boundedConstructibleOpenImmersionLowerShriekBaseChange
        (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq =
      boundedConstructibleOpenImmersionLowerShriekBaseChange'
        (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq
    rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
      boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]
  unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
  rw [e]
  rfl

end Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExchangeIsIso

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

/-- For bounded constructible `ℚ̄_ℓ`-sheaves, the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq) := by
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq]
  exact isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ sq

end ExchangeIsIso

/-! ### The composition isomorphisms -/

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `ℚ̄_ℓ`-sheaves: for the chosen compactifications `c = (X
⟶[i] Z ⟶[p] Y)` of `f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W
⟶[p'] Z')` of `p ≫ j` with cartesian square (`Compactification.exists_isPullback_overG_overI`), the
composite of the independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`) for the composite
compactification `X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of `j_!`
and `Rf_*`, and of the inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
noncomputable irreducible_def boundedConstructibleLowerShriekComp_padicAlgCl :
    boundedConstructibleLowerShriek ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleLowerShriek ℓ g :=
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The isomorphism `R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}` attached to compactifications `c` of `f` and
`c'` of `g` and a compactification `d` of `p ≫ j` with cartesian square `hd`, as in the definition
of `boundedConstructibleLowerShriekComp_padicAlgCl`. -/
noncomputable def boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl
    (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left)
    (hd : IsPullback c.overG d.overI c'.overI d.overG) :
    boundedConstructibleLowerShriek ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c' :=
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (Compactification.overCompObjIso c c' d).hom.left := by
    simp only [Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI)
      (Compactification.overCompObjIso c c' d).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ hd
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ hd)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism of the lower shriek is the isomorphism attached to the chosen
compactifications. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_eq :
    boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g =
      boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g
        (compactificationOverField f) (compactificationOverField g)
        (Compactification.exists_isPullback_overG_overI (compactificationOverField f)
          (compactificationOverField g)).choose
        (Compactification.exists_isPullback_overG_overI (compactificationOverField f)
          (compactificationOverField g)).choose_spec := by
  simp only [boundedConstructibleLowerShriekComp_padicAlgCl_def,
    boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl]

end AlgebraicGeometry.ProEtale.CondensedRing
