/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!
# The constructible exceptional inverse image on the pro-étale site

Blueprint `theorem-f-shriek-finite-coefficients` (and `theorem-f-shriek-ell-adic-coefficients--4`
(vi)) defines, at a finite stage `A = A_{E,n}`, the exceptional inverse image on the pro-étale site
as the étale right adjoint transported along the comparison,
`Rf^! := ν_X^* ∘ f^× ∘ Rν_{Y,*}` (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`), and
asserts as theorems:

* on objects of étale origin `L ≅ ν_Y^* G` it is `ν_X^* f^× G`
  (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekComparisonIso`);
* it carries `Dᵇc(Y, A)` into `Dᵇc(X, A)` and `Dctf(Y, A)` into `Dctf(X, A)`, with a shift of the
  constructible intervals independent of the interval (and of the stage);
* it is right adjoint to `Rf_!` on `Dctf`
  (`AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`);
* when an ambient right adjoint `Rf^×` of `Rf_!` exists and carries `Dctf(Y, A)` into objects
  bounded below of étale origin, its values on `Dctf(Y, A)` agree with `Rf^!` by uniqueness of
  adjoints (`AlgebraicGeometry.ProEtale.nonempty_iso_rightDerivedUpperShriek_of_adjunction`).

All of these are transported from the étale statements of
`WeilConjectures.SixFunctors.Etale.Derived.Stability` along the full faithfulness of `ν^*` on
bounded below complexes.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedUpperShriek`
- `AlgebraicGeometry.ProEtale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedUpperShriek`
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerShriek`
- `AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`
- `AlgebraicGeometry.ProEtale.nonempty_iso_rightDerivedUpperShriek_of_adjunction`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [CompactSpace Y]

/-- On a bounded below complex of étale origin `ν_Y^* G`, the pro-étale exceptional inverse
image is `ν_X^* f^× G`: the unit `G ⟶ Rν_* ν^* G` is an isomorphism on bounded below `G`
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`). This is the formula
`Rf^! L = ν_X^* f^× G` of blueprint `theorem-f-shriek-finite-coefficients`. -/
noncomputable def rightDerivedUpperShriekComparisonIso
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus G) :
    (rightDerivedUpperShriek Λ f).obj
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj G) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
        ((Etale.rightDerivedUpperShriek Λ f).obj G) :=
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) Y G hG
  D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso ((Etale.rightDerivedUpperShriek _ f).mapIso
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app G)).symm)

end Comparison

omit [Finite Λ] in
/-- A fully faithful exact functor reflects homology concentration. -/
lemma homologyConcentratedIn_of_mapDerivedCategory_comparisonUpperStar {X : Scheme.{u}}
    {a b : ℤ} {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : _root_.DerivedCategory.homologyConcentratedIn a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G)) :
    _root_.DerivedCategory.homologyConcentratedIn a b G := by
  have hz : ∀ i : ℤ, IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G)) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj G) := fun i hi ↦
    IsZero.of_full_of_faithful_of_isZero (ν^*(X)[ModuleCat.{u + 1} Λ]) _
      (hi.of_iso
        (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso i).app G))
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨(_root_.DerivedCategory.isGE_iff G a).2 fun i hi ↦
      hz i ((_root_.DerivedCategory.isGE_iff _ a).1 h₁ i hi),
    (_root_.DerivedCategory.isLE_iff G b).2 fun i hi ↦
      hz i ((_root_.DerivedCategory.isLE_iff _ b).1 h₂ i hi)⟩

/-- `ν^*` carries `D_c^[a, b]` with Tor amplitude in `[a, b]` on the étale site to the same on
the pro-étale site. -/
lemma constructibleTorAmplitudeIn_mapDerivedCategory_comparisonUpperStar {X : Scheme.{u}}
    {a b : ℤ} {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hG : Etale.DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b G) :
    DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) :=
  ⟨⟨DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hG.1.1,
    (ν^*(X)[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hG.1.2⟩,
    DerivedCategory.torAmplitudeIn_mapDerivedCategory Λ hG.2⟩

/-- Conversely, if `ν^* G` lies in `D_c^[a, b]` with Tor amplitude in `[a, b]` and `G` is
bounded constructible, then so does `G`. -/
lemma constructibleTorAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar {X : Scheme.{u}}
    {a b : ℤ} {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X G)
    (h : DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G)) :
    Etale.DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b G :=
  ⟨⟨hbc, homologyConcentratedIn_of_mapDerivedCategory_comparisonUpperStar Λ h.1.2⟩,
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1 h.2⟩

/-- Blueprint `theorem-f-shriek-ell-adic-coefficients--4`, the comparison of (v) and (vi): if `G` is
a right adjoint of `Rf_!` on the ambient derived categories (the ambient exceptional right adjoint
`Rf^×`, which need not exist) and `G L` is bounded below of étale origin for a bounded below `L` (as
the preservation clauses of `sk-def-sf-admissible` guarantee on `Dctf`), then `G L ≅ Rf^! L`, by
uniqueness of adjoints on the bounded below objects of étale origin. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_adjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y]
    {G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⊣ G)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hGL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X (G.obj L)) :
    Nonempty (G.obj L ≅ (rightDerivedUpperShriek Λ f).obj L) := by
  have hR := plusEtaleOrigin_rightDerivedUpperShriek_obj f hL
  refine ⟨⟨rightDerivedUpperShriekHomEquiv f hGL hL (adj.counit.app L),
    adj.homEquiv _ _ (rightDerivedUpperShriekCounit f L hL), ?_, ?_⟩⟩
  · apply (adj.homEquiv _ _).symm.injective
    rw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
      ← rightDerivedUpperShriekHomEquiv_symm_apply f hGL hL, Equiv.symm_apply_apply,
      Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  · apply (rightDerivedUpperShriekHomEquiv f hR hL).symm.injective
    rw [rightDerivedUpperShriekHomEquiv_naturality_left_symm f hR hGL, Equiv.symm_apply_apply,
      rightDerivedUpperShriekHomEquiv_symm_id, ← Adjunction.homEquiv_counit,
      Equiv.symm_apply_apply]

/-- Lying in `D_c^[a, b]` with Tor amplitude in `[a, b]` is invariant under isomorphism. -/
instance (X : Scheme.{u}) (a b : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b) :=
  have : (_root_.DerivedCategory.homologyConcentratedIn (C := Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)) a b).IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨_, _⟩ ↦ ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e a,
      _root_.DerivedCategory.TStructure.t.isLE_of_iso e b⟩⟩
  inferInstanceAs (DerivedCategory.boundedConstructible _ X ⊓
    _root_.DerivedCategory.homologyConcentratedIn a b ⊓
    DerivedCategory.torAmplitudeIn _ X a b).IsClosedUnderIsomorphisms

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent Λ Y]
  (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [CompactSpace Y]

include aY

omit [CompactSpace Y] in
/-- Blueprint `theorem-f-shriek-finite-coefficients`: the pro-étale exceptional inverse image
carries `Dᵇc(Y, A)` into `Dᵇc(X, A)`, for a separated finite-type `f` over a finite-type
`k`-scheme `Y` and a finite `Λ` whose exponent is invertible on `Y`. -/
theorem boundedConstructible_rightDerivedUpperShriek
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y L) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((rightDerivedUpperShriek Λ f).obj L) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := hL
  exact (DerivedCategory.boundedConstructible _ X).prop_of_iso
    (((rightDerivedUpperShriek _ f).mapIso e).symm ≪≫ rightDerivedUpperShriekComparisonIso Λ f G
      hG.1.1).symm
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      (Etale.boundedConstructible_rightDerivedUpperShriek Λ aY f hG))

omit [CompactSpace Y] in
/-- Blueprint `theorem-f-shriek-finite-coefficients`: the explicit interval bounds. There is a
shift `c`, depending only on `f`, such that `Rf^!` carries `D_c^[a, b](Y, A)` with Tor amplitude
in `[a, b]` into `D_c^[a - c, b + c](X, A)` with Tor amplitude in `[a - c, b + c]`, for all
`a, b` and independently of the finite coefficient ring (the étale bound `c = 2D + 2 dim Y + 1`
of `AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`). -/
theorem exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek :
    ∃ c : ℤ, ∀ (a b : ℤ)
      (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - c) (b + c)
          ((rightDerivedUpperShriek Λ f).obj L) := by
  obtain ⟨c, hc⟩ := Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek Λ aY f
  refine ⟨c, fun a b L hL ↦ ?_⟩
  obtain ⟨G, hG, ⟨e⟩⟩ := hL.1.1
  have hG' : Etale.DerivedCategory.constructibleTorAmplitudeIn _ Y a b G :=
    constructibleTorAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar Λ hG
      ((DerivedCategory.constructibleTorAmplitudeIn _ Y a b).prop_of_iso e.symm hL)
  exact (DerivedCategory.constructibleTorAmplitudeIn _ X (a - c) (b + c)).prop_of_iso
    (((rightDerivedUpperShriek _ f).mapIso e).symm ≪≫ rightDerivedUpperShriekComparisonIso Λ f G
      hG.1.1).symm
    (constructibleTorAmplitudeIn_mapDerivedCategory_comparisonUpperStar Λ (hc a b G hG'))

omit [CompactSpace Y] in
/-- Blueprint `theorem-f-shriek-finite-coefficients`: the pro-étale exceptional inverse image
carries `Dctf(Y, A)` into `Dctf(X, A)`. -/
theorem constructibleFiniteTor_rightDerivedUpperShriek
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((rightDerivedUpperShriek Λ f).obj L) := by
  obtain ⟨c, hc⟩ := exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek Λ aY f
  obtain ⟨a, b, hab⟩ :=
    (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor L).2 hL
  exact (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).1
    ⟨a - c, b + c, hc a b L hab⟩

omit [CompactSpace Y] in
/-- The pro-étale compact-support direct image carries `Dctf(X, A)` into `Dctf(Y, A)`: on
`ν^* G` it is `ν^* Rf_!^{ét} G` (`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`)
and the étale `Rf_!` preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek`). -/
theorem constructibleFiniteTor_rightDerivedLowerShriek
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, hab⟩ := hK
  have hGt : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X G :=
    ⟨hG, a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩
  exact (DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso
    (((rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} Λ) f).app ⟨G, hG.1.1⟩).symm ≪≫
      (rightDerivedLowerShriek _ f).mapIso e)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hGt))

/-- Blueprint `theorem-f-shriek-finite-coefficients`: the adjunction
`Hom_Y(Rf_! K, L) ≅ Hom_X(K, Rf^! L)` on the small categories `Dctf`, a theorem: the pro-étale
exceptional adjunction on bounded below objects of étale origin
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction`), restricted to `Dctf`, which
both functors preserve. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f)
        (fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f K.property) ⊣
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙
          rightDerivedUpperShriek Λ f)
        (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f L.property) :=
  rightDerivedUpperShriekAdjunction f _ _
    (fun _ hK ↦ DerivedCategory.constructibleFiniteTor.plusEtaleOrigin hK)
    (fun _ hL ↦ DerivedCategory.constructibleFiniteTor.plus hL)
    (fun _ hK ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK)
    (fun _ hL ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hL)


end AlgebraicGeometry.ProEtale
