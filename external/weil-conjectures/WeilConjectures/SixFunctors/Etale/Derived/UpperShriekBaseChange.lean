/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Base change for the exceptional inverse image against an open immersion

For a cartesian square of schemes
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
with `f`, `f'` admitting compactifications, and torsion coefficients `Λ`, the compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), and the exceptional
inverse images `Rf^!`, `Rf'^!` are right adjoints of `Rf_!`, `Rf'_!`. The *base-change
comparison* of the exceptional inverse image is the mate of `Ex_!⁻¹`,
```
  β : Lg'^* Rf^! ⟶ Rf'^! Lg^*,
```
whose transpose under `Rf'_! ⊣ Rf'^!` is `Rf'_! Lg'^* Rf^! ≅ Lg^* Rf_! Rf^! ⟶ Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). It is not an isomorphism for
an arbitrary `g`; it is one when `g` is an open immersion
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`,
blueprint `proposition-composition-open-restriction-compactifications-f--5` and
`proposition-composition-open-restriction-compactifications-f--5`).

## The argument

For an open immersion `g` the pullbacks `Lg^*`, `Lg'^*` are themselves right adjoints, of the
extensions by zero `g_!`, `g'_!`. The iterated mate of a square of left adjoints is its
conjugate (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), so `β` is the conjugate of the
transformation
```
  γ : g_! Rf'_! ⟶ Rf_! g'_!
```
between the left adjoints of `Rf'^! Lg^*` and `Lg'^* Rf^!`, and `β` is invertible if and only if
`γ` is. Invertibility of `γ` is tested on the open `Y'` and on its closed complement `Z`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_closedComplement_map`):

* over `Y'`, `Lg^* γ` is a composite of the invertible units `𝟭 ≅ Lg^* g_!`, `𝟭 ≅ Lg'^* g'_!`
  and of `Ex_!⁻¹`;
* over `Z`, both sides vanish: `Li^* g_! = 0`, and `Li^* Rf_! g'_! ≅ Rf_{Z,!} Li'^* g'_! = 0` by
  compact-support base change along `i` and since the ranges of `i'` and `g'` are disjoint.

This is a different route from the blueprint proof of
`proposition-composition-open-restriction-compactifications-f--5` (closed support triangle and dual
base change), and it does not need `f` to be proper.

## Main definitions and statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`: `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- Whether the mate of a 2-square is invertible does not depend on the choice of the left
adjoints up to isomorphism, nor on the choice of their right adjoints: transporting the square
along isomorphisms `L₁ ≅ L₁'` and `L₂ ≅ L₂'` changes its mate by whiskering with the invertible
conjugates (`CategoryTheory.conjugateEquiv_mateEquiv_vcomp`,
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`). -/
lemma isIso_mateEquiv_whiskerLeft_whiskerRight (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁')
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂') (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁ L₂ H) [IsIso (mateEquiv adj₁ adj₂ α)] :
    IsIso (mateEquiv adj₁' adj₂' ((α.whiskerLeft e₁.hom).whiskerRight e₂.inv)) := by
  rw [mateEquiv_conjugateEquiv_vcomp adj₁' adj₂ adj₂', conjugateEquiv_mateEquiv_vcomp adj₁' adj₁]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- For an open immersion `g`, the derived extension by zero `D(g_!)` is left adjoint to the
derived pullback `Lg^*`: the adjunction `D(g_!) ⊣ D(g^*)` transported along `Lg^* ≅ D(g^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction {V T : Scheme.{u}}
    (j : V ⟶ T) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} Λ]) ⊣ L((j)^*[ModuleCat.{u + 1} Λ]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm

instance isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_unit
    {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).unit := by
  simp only [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction]
  rw [Adjunction.ofNatIsoRight_unit]
  infer_instance

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--5`: Base change for a
proper morphism, against an open immersion.

Blueprint `proposition-composition-open-restriction-compactifications-f--5`: Base change for an
arbitrary morphism, against an open immersion.

For a cartesian square `g' ≫ f = f' ≫ g` with `g` an open immersion, `f`, `f'` admitting
compactifications and torsion coefficients `Λ`, the base-change comparison
`β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`)
is an isomorphism. The ambient right adjoints `Rf^!`, `Rf'^!` of the blueprint's datum are the
exceptional inverse images, which exist for torsion coefficients
(`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`, blueprint
`theorem-existence-exceptional-inverse-image--1`). In particular this applies to the passage from an
affine open of the base to the base.

`f` need not be proper: `β` is the conjugate of `γ : g_! Rf'_! ⟶ Rf_! g'_!`, which is checked to
be invertible on the open `Y'` and on its closed complement; see the module docstring. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f] [QuasiCompact f'] [IsOpenImmersion g]
    (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  set adjG' := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ g'
  set adjG := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ g
  set adjf := rightDerivedUpperShriekAdjunction Λ f
  set adjf' := rightDerivedUpperShriekAdjunction Λ f'
  set Ex := rightDerivedLowerShriekBaseChangeMap Λ sq
  let γ := (mateEquiv adjG' adjG).symm (TwoSquare.mk _ _ _ _ (inv Ex))
  have hβ : rightDerivedUpperShriekBaseChangeMap Λ sq =
      conjugateEquiv (adjG'.comp adjf) (adjf'.comp adjG) γ := by
    rw [← iterated_mateEquiv_conjugateEquiv]
    simp only [γ, Equiv.apply_symm_apply]
    rfl
  rw [hβ]
  suffices IsIso γ by infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hγ : γ.app M = D((g)_!open[ModuleCat.{u + 1} Λ]).map
      ((R(f')_![ModuleCat.{u + 1} Λ]).map (adjG'.unit.app M)) ≫
      D((g)_!open[ModuleCat.{u + 1} Λ]).map ((inv Ex).app _) ≫ adjG.counit.app _ := by
    simp [γ]
  refine isIso_of_isIso_leftDerivedUpperStar_closedComplement_map _ g _ ?_ ?_
  · -- over the open `Y'`
    rw [hγ, Functor.map_comp, Functor.map_comp]
    have : IsIso (L((g)^*[ModuleCat.{u + 1} Λ]).map (adjG.counit.app
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M)))) := by
      have h := adjG.right_triangle_components
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M))
      have : IsIso (adjG.unit.app (L((g)^*[ModuleCat.{u + 1} Λ]).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M)))) :=
        inferInstance
      have : IsIso (adjG.unit.app (L((g)^*[ModuleCat.{u + 1} Λ]).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M))) ≫
          L((g)^*[ModuleCat.{u + 1} Λ]).map (adjG.counit.app
            ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M)))) := by
        rw [h]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adjG.unit.app _) _
    infer_instance
  · -- over the closed complement `Z` both sides vanish
    have hsrc : IsZero ((L((g.closedComplement)^*[ModuleCat.{u + 1} Λ])).obj
        ((D((g)_!open[ModuleCat.{u + 1} Λ])).obj ((R(f')_![ModuleCat.{u + 1} Λ]).obj M))) :=
      isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek _ g _
    have sqi := IsPullback.of_hasPullback f g.closedComplement
    have : HasCompactification (pullback.snd f g.closedComplement) :=
      ((HasCompactification.compactification f).ofIsPullback sqi).hasCompactification
    have : QuasiCompact (pullback.snd f g.closedComplement) :=
      MorphismProperty.of_isPullback sqi ‹QuasiCompact f›
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqi
    have hdisj : Disjoint (Set.range (pullback.fst f g.closedComplement).base)
        (Set.range g'.base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x', hx'⟩
      have h1 : f.base (g'.base x') = g.base (f'.base x') := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]
      have h2 : f.base ((pullback.fst f g.closedComplement).base z) =
          g.closedComplement.base ((pullback.snd f g.closedComplement).base z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have h3 : g.closedComplement.base ((pullback.snd f g.closedComplement).base z) ∈
          Set.range g.closedComplement.base := ⟨_, rfl⟩
      rw [g.range_closedComplement, ← h2, ← hx', h1] at h3
      exact h3 ⟨_, rfl⟩
    have hz :=
      isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
        (ModuleCat.{u + 1} Λ) g' (pullback.fst f g.closedComplement) hdisj M
    have htgt : IsZero ((L((g.closedComplement)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((D((g')_!open[ModuleCat.{u + 1} Λ])).obj M))) :=
      (Functor.map_isZero (R(pullback.snd f g.closedComplement)_![ModuleCat.{u + 1} Λ]) hz).of_iso
        ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sqi)).app _)
    exact ⟨⟨0, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

section ReductionToProper

variable [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
  (sq : IsPullback g' f' f g)

omit [Finite Λ] [HasCompactification f] [HasCompactification f'] [QuasiCompact f'] in
/-- The inverse of the compact-support base change `Ex_!(c)` along a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)` of `f` is the vertical pasting of the base change isomorphism of the
extension by zero `Lg'^* j'_! ≅ j_! Lḡ^*` with the inverse of the derived base change `Ex_*` of
the proper part `p`. -/
lemma inv_rightDerivedLowerShriekOfCompactificationBaseChangeMap (c : Compactification f)
    [IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback c.g g).toCommSq)]
    [IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c)] :
    inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c) =
      (TwoSquare.vComp (TwoSquare.mk _ _ _ _
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
          (c.isPullback_i_ofIsPullback sq)).hom)
        (TwoSquare.mk _ _ _ _ (inv (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback c.g g).toCommSq)))) := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  ext M
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc, NatTrans.id_app, Functor.comp_obj]
  erw [Category.id_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- The inverse of the compact-support base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`, as a
2-square: the vertical pasting of the base change isomorphism of the extension by zero with the
inverse of the derived base change `Ex_*` of the proper part of the chosen compactification
`c` of `f`, transported along the comparison `Rf'_!(c') ≅ Rf'_!` for the base-changed
compactification `c'`. -/
lemma twoSquare_inv_rightDerivedLowerShriekBaseChangeMap
    [IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback (HasCompactification.compactification f).g g).toCommSq)]
    [IsIso (rightDerivedLowerShriekBaseChangeMap Λ sq)] :
    TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) =
      (((TwoSquare.vComp (TwoSquare.mk _ _ _ _
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
          ((HasCompactification.compactification f).isPullback_i_ofIsPullback sq)).hom)
        (TwoSquare.mk _ _ _ _ (inv (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback (HasCompactification.compactification f).g
            g).toCommSq)))).whiskerLeft
        (Iso.refl (R(f)_![ModuleCat.{u + 1} Λ])).hom).whiskerRight
        (rightDerivedLowerShriekIso Λ
          ((HasCompactification.compactification f).ofIsPullback sq)).inv) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
    (HasCompactification.compactification f)
  have hinv : inv (rightDerivedLowerShriekBaseChangeMap Λ sq) =
      Functor.whiskerLeft _ (rightDerivedLowerShriekIso Λ
        ((HasCompactification.compactification f).ofIsPullback sq)).inv ≫
      inv (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        (HasCompactification.compactification f)) := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [rightDerivedLowerShriekBaseChangeMap, Category.assoc,
      ← Category.assoc (Functor.whiskerLeft _ _),
      ← Functor.whiskerLeft_comp, Iso.hom_inv_id, Functor.whiskerLeft_id', Category.id_comp,
      IsIso.hom_inv_id]
  rw [hinv, inv_rightDerivedLowerShriekOfCompactificationBaseChangeMap]
  ext K
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Blueprint `cor-exc-base-change-reduces-to-proper`: Base change for a general morphism
reduces to the proper part.

Let `X ⟶[j] X̄ ⟶[p] Y` be the chosen compactification of `f`, and let `X' ⟶[j'] X̄' ⟶[p'] Y'`
be its base change along `g`, with `ḡ : X̄' ⟶ X̄`. Let `Rp_* ⊣ Gp` and `Rp'_* ⊣ Gp'` be right
adjoints of the compact-support functors `Rp_! = Rp_*`, `Rp'_! = Rp'_*` of the proper parts
(the ambient datum for `p` and `p'`). If the base-change comparison `Lḡ^* Gp ⟶ Gp' Lg^*` of `p`,
the mate of the inverse of the proper base change `Ex_*`, is an isomorphism, then so is the
base-change comparison `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` of `f`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). So the comparison for a
general separated finite-type morphism reduces to its proper part, the open part being free.

As in the blueprint, `Rf_! = Rp_* j_!`, so the composite `Gp ⋙ j^*` is a right adjoint of
`Rf_!`, and the mate of `Ex_!⁻¹` for these composite adjunctions is the horizontal pasting of
the comparison for `p` with the mate `j^* Lg'^* ⟶ Lḡ^* j'^*` of the extension-by-zero base
change (`CategoryTheory.mateEquiv_hcomp`); the latter is invertible, being identified through
the pullback composition `L(j' ≫ ḡ)^* = L(g' ≫ j)^*` with `Lg'^*` of the invertible
`j^* (j_! j^* ⟶ 𝟭)`. Changing the right adjoints and the compactification of `f'` to the chosen
ones does not affect invertibility of mates
(`CategoryTheory.isIso_mateEquiv_whiskerLeft_whiskerRight`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso_mateEquiv
    {Gp : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (HasCompactification.compactification f).Z.smallEtaleTopology
        (ModuleCat.{u + 1} Λ))}
    {Gp' : _root_.DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (pullback (HasCompactification.compactification f).g
        g).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adjp : R(((HasCompactification.compactification f).g)_*[ModuleCat.{u + 1} Λ]) ⊣ Gp)
    (adjp' : R((pullback.snd (HasCompactification.compactification f).g g)_*[ModuleCat.{u + 1} Λ])
      ⊣ Gp')
    [IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback (HasCompactification.compactification f).g g).toCommSq)]
    [IsIso (mateEquiv adjp adjp' (TwoSquare.mk _ _ _ _ (inv (derivedBaseChangeMap
      (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback (HasCompactification.compactification f).g
        g).toCommSq))))] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  set c := HasCompactification.compactification f
  set c' := c.ofIsPullback sq
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsOpenImmersion c'.i := c'.isOpenImmersion
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c
  set adjJ := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i
  set adjJ' := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c'.i
  set α := TwoSquare.mk _ _ _ _ (derivedOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} Λ) (c.isPullback_i_ofIsPullback sq)).hom
  set β' := TwoSquare.mk _ _ _ _ (inv (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback c.g g).toCommSq))
  -- the mate of the extension-by-zero square is invertible
  have hθ : IsIso (mateEquiv adjJ adjJ' α) := by
    let τ : L((pullback.fst c.g g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c'.i)^*[ModuleCat.{u + 1} Λ]) ≅
        L((c.i)^*[ModuleCat.{u + 1} Λ]) ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) :=
      (leftDerivedUpperStarComp _ c'.i (pullback.fst c.g g) (g' ≫ c.i)
        (by simp [c'])).symm ≪≫ leftDerivedUpperStarComp _ g' c.i
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    have hε : IsIso ((L((pullback.fst c.g g)^*[ModuleCat.{u + 1} Λ]) ⋙
        L((c'.i)^*[ModuleCat.{u + 1} Λ])).map (adjJ.counit.app N)) := by
      have hj : IsIso (L((c.i)^*[ModuleCat.{u + 1} Λ]).map (adjJ.counit.app N)) := by
        have h := adjJ.right_triangle_components N
        have : IsIso (adjJ.unit.app (L((c.i)^*[ModuleCat.{u + 1} Λ]).obj N) ≫
            L((c.i)^*[ModuleCat.{u + 1} Λ]).map (adjJ.counit.app N)) := by
          rw [h]
          exact IsIso.id _
        exact IsIso.of_isIso_comp_left (adjJ.unit.app _) _
      have h := τ.hom.naturality (adjJ.counit.app N)
      simp only [Functor.id_obj] at h
      have : IsIso ((L((pullback.fst c.g g)^*[ModuleCat.{u + 1} Λ]) ⋙
          L((c'.i)^*[ModuleCat.{u + 1} Λ])).map (adjJ.counit.app N) ≫ τ.hom.app N) := by
        rw [h, Functor.comp_map]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (τ.hom.app N)
    simp only [mateEquiv_apply]
    dsimp
    simp only [Category.id_comp, Category.comp_id]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hε)
  -- the mate of `Ex_!(c)⁻¹` for the composite adjunctions is invertible
  have hc : IsIso (mateEquiv (adjJ.comp adjp) (adjJ'.comp adjp')
      (TwoSquare.vComp α β')) := by
    rw [mateEquiv_hcomp]
    dsimp only [TwoSquare.hComp]
    infer_instance
  -- transport to the chosen compactification of `f'` and the chosen right adjoints
  have := isIso_mateEquiv_whiskerLeft_whiskerRight (adjJ.comp adjp)
    (rightDerivedUpperShriekAdjunction _ f) (adjJ'.comp adjp')
    (rightDerivedUpperShriekAdjunction _ f') (Iso.refl (R(f)_![ModuleCat.{u + 1} Λ]))
    (rightDerivedLowerShriekIso Λ c') (TwoSquare.vComp α β')
  have hEx := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  change IsIso (mateEquiv (rightDerivedUpperShriekAdjunction _ f)
    (rightDerivedUpperShriekAdjunction _ f')
    (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))))
  rw [twoSquare_inv_rightDerivedLowerShriekBaseChangeMap]
  exact this

end ReductionToProper

end Etale

end AlgebraicGeometry
