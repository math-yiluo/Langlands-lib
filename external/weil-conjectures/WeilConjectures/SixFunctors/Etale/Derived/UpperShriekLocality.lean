/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Open restriction and compactifications for `Rf^!`

For torsion coefficients `Λ`, the exceptional inverse image `Rf^!` on the unbounded derived
categories of étale sheaves is the right adjoint of `Rf_!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`). This file proves the two
lemmas of blueprint `proposition-composition-open-restriction-compactifications-f--1` about its
behaviour under open immersions and compactifications:

* `proposition-composition-open-restriction-compactifications-f`: for a quasi-compact open immersion
`j`, the extension by
  zero `Dj_!` is left adjoint to `Dj^*` and `Rj^! ≅ Dj^*` is the unique isomorphism compatible
  with the adjunctions; consequently `u^* Rf^! ≅ Rf_V^! v^*` for an open `v : V ⟶ Y` with
  preimage `u : X_V ⟶ X`, and `j^* Rf^! ≅ R(j ≫ f)^!`; and isomorphisms of `D(X_ét, Λ)` are
  detected on an open covering.
* `proposition-composition-open-restriction-compactifications-f--6`: for a compactification
`f = i ≫ p`, the composite
  `Rp^! ⋙ Di^*` is right adjoint to `Rf_!(c) = Di_! ⋙ Rp_*`, with counit the composite of the
  two counits, and `Rf^! ≅ Rp^! ⋙ Di^*` is the unique isomorphism compatible with the
  adjunctions.

The blueprint states these on the localizing subcategories `Loc(Dctf)`; on the étale sites
with finite coefficients they hold on the whole unbounded derived categories.

## Main statements

- `AlgebraicGeometry.Etale.existsUnique_rightDerivedUpperShriekOpenImmersionIso`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_upperStar`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_openImmersion`
- `AlgebraicGeometry.Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective`
- `AlgebraicGeometry.Etale.existsUnique_rightDerivedUpperShriekOfCompactificationIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Conservative

/-- Blueprint `proposition-composition-open-restriction-compactifications-f`, part
(3): **isomorphisms are detected on an open covering** (more generally, along any jointly surjective
family `a_i : U_i ⟶ X`): a morphism `φ` of `D(X_ét, Λ)` whose restrictions `D(a_i^*) φ` are all
isomorphisms is an isomorphism. The pullbacks are exact, so they commute with the cohomology
sheaves, and the restrictions along a jointly surjective family reflect isomorphisms of sheaves. -/
theorem isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective {X : Scheme.{u}}
    {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L)
    (hφ : ∀ i, IsIso (D((a i)^*[ModuleCat.{u + 1} Λ]).map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective _ a ha _ fun i ↦ ?_
  exact (NatIso.isIso_map_iff
    (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (DerivedCategory.homologyFunctor _ n)
      (D((a i)^*[ModuleCat.{u + 1} Λ]).map φ))

end Conservative

variable [Finite Λ]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j]
  [QuasiCompact j]

/-- The adjunction `Rj_! ⊣ Dj^*` for a quasi-compact open immersion `j`: the adjunction
`Dj_! ⊣ Dj^*` transported along `Rj_! ≅ Dj_!`. -/
noncomputable def rightDerivedLowerShriekOpenImmersionAdjunction :
    R(j)_![ModuleCat.{u + 1} Λ] ⊣ D((j)^*[ModuleCat.{u + 1} Λ]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).ofNatIsoLeft
    (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).symm

/-- The isomorphism `Rj^! ≅ Dj^*` for a quasi-compact open immersion `j`, compatible with the
adjunctions `Rj_! ⊣ Rj^!` and `Rj_! ⊣ Dj^*`. -/
noncomputable def rightDerivedUpperShriekOpenImmersionIso :
    R(j)^![Λ] ≅ D((j)^*[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedUpperShriekAdjunction _ j).rightAdjointUniq
    (rightDerivedLowerShriekOpenImmersionAdjunction Λ j)

/-- Blueprint `proposition-composition-open-restriction-compactifications-f`, part (1): Open
immersions and open restriction for `f^!`.

For a quasi-compact open immersion `j : U ⟶ X` and finite `Λ`, the extension by zero
`Dj_!` is left adjoint to `Dj^*`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`),
`Rj_! ≅ Dj_!` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion`), and
there is a unique isomorphism `Rj^! ≅ Dj^*` compatible with the adjunctions `Rj_! ⊣ Rj^!` and
`Rj_! ⊣ Dj^*`, namely `AlgebraicGeometry.Etale.rightDerivedUpperShriekOpenImmersionIso`. -/
theorem existsUnique_rightDerivedUpperShriekOpenImmersionIso :
    ∃! e : R(j)^![Λ] ≅ D((j)^*[ModuleCat.{u + 1} Λ]),
      (rightDerivedUpperShriekAdjunction _ j).ofNatIsoRight e =
        rightDerivedLowerShriekOpenImmersionAdjunction Λ j :=
  Adjunction.existsUnique_ofNatIsoRight_eq _ _

end OpenImmersion

section Locality

/-- The isomorphism `R(g)_! ≅ R(g')_!` for `g = g'`, comparing the chosen compactifications of
`g` and `g'` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). -/
noncomputable def rightDerivedLowerShriekCongr {X Y : Scheme.{u}} {g g' : X ⟶ Y}
    [HasCompactification g] [HasCompactification g'] [QuasiCompact g'] (h : g = g') :
    R(g)_![ModuleCat.{u + 1} Λ] ≅ R(g')_![ModuleCat.{u + 1} Λ] :=
  rightDerivedLowerShriekIso Λ ((HasCompactification.compactification g).copy h.symm)

/-- The isomorphism `R(g)^! ≅ R(g')^!` for `g = g'`, the right adjoint of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCongr`. -/
noncomputable def rightDerivedUpperShriekCongr {X Y : Scheme.{u}} {g g' : X ⟶ Y}
    [HasCompactification g] [HasCompactification g'] [QuasiCompact g'] (h : g = g') :
    R(g)^![Λ] ≅ R(g')^![Λ] :=
  ((rightDerivedUpperShriekAdjunction _ g).ofNatIsoLeft
    (rightDerivedLowerShriekCongr Λ h)).rightAdjointUniq (rightDerivedUpperShriekAdjunction _ g')

/-- Blueprint `proposition-composition-open-restriction-compactifications-f`, part (2): **`Rf^!`
commutes with restriction to an open of the target**. Let `v : V ⟶ Y` and `u : X_V ⟶ X` be
quasi-compact open immersions and `f_V : X_V ⟶ V` with `u ≫ f = f_V ≫ v` (e.g. `X_V = f⁻¹(V)`). Then
`u^* Rf^! ≅ Rf_V^! v^*`: by the composition law for `R(-)^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`) and part (1),
`u^* Rf^! ≅ Ru^! Rf^! ≅ R(u ≫ f)^! = R(f_V ≫ v)^! ≅ Rf_V^! Rv^! ≅ Rf_V^! v^*`. -/
theorem nonempty_iso_rightDerivedUpperShriek_upperStar {X Y V XV : Scheme.{u}} (f : X ⟶ Y)
    (v : V ⟶ Y) (u : XV ⟶ X) (fV : XV ⟶ V) [IsOpenImmersion u] [IsOpenImmersion v]
    (w : u ≫ f = fV ≫ v) [HasCompactification f] [HasCompactification fV]
    [HasCompactification u] [HasCompactification v] [HasCompactification (u ≫ f)]
    [HasCompactification (fV ≫ v)] [QuasiCompact u] [QuasiCompact v] [QuasiCompact (u ≫ f)]
    [QuasiCompact (fV ≫ v)] :
    Nonempty (R(f)^![Λ] ⋙ D((u)^*[ModuleCat.{u + 1} Λ]) ≅
      D((v)^*[ModuleCat.{u + 1} Λ]) ⋙ R(fV)^![Λ]) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ u f
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ fV v
  exact ⟨Functor.isoWhiskerLeft _ (rightDerivedUpperShriekOpenImmersionIso Λ u).symm ≪≫
    e₁.symm ≪≫ rightDerivedUpperShriekCongr Λ w ≪≫ e₂ ≪≫
    Functor.isoWhiskerRight (rightDerivedUpperShriekOpenImmersionIso Λ v) _⟩

/-- Blueprint `proposition-composition-open-restriction-compactifications-f`, part (2): **`Rf^!`
commutes with restriction to an open of the source**: for a quasi-compact open immersion
`j : U ⟶ X`, `j^* Rf^! ≅ Rj^! Rf^! ≅ R(j ≫ f)^!`, by part (1) and the composition law. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_openImmersion {U X Y : Scheme.{u}}
    (j : U ⟶ X) (f : X ⟶ Y) [IsOpenImmersion j] [HasCompactification j] [HasCompactification f]
    [HasCompactification (j ≫ f)] [QuasiCompact j] [QuasiCompact (j ≫ f)] :
    Nonempty (R(f)^![Λ] ⋙ D((j)^*[ModuleCat.{u + 1} Λ]) ≅
      R(j ≫ f)^![Λ]) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j f
  exact ⟨Functor.isoWhiskerLeft _ (rightDerivedUpperShriekOpenImmersionIso Λ j).symm ≪≫ e.symm⟩

end Locality

section Proper

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]

/-- The adjunction `Rp_* ⊣ Rp^!` for a proper `p`: the adjunction `Rp_! ⊣ Rp^!` transported
along `Rp_! ≅ Rp_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
noncomputable def rightDerivedLowerStarUpperShriekAdjunctionOfIsProper :
    R((p)_*[ModuleCat.{u + 1} Λ]) ⊣ R(p)^![Λ] :=
  (rightDerivedUpperShriekAdjunction _ p).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) p)

end Proper

section Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The adjunction `Rf_!(c) = Di_! ⋙ Rp_* ⊣ Rp^! ⋙ Di^*` attached to a compactification
`c = (X ⟶[i] Z ⟶[p] Y)`: the composite of the adjunctions `Di_! ⊣ Di^*` and `Rp_* ⊣ Rp^!`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationUpperShriekAdjunction :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⊣ R(c.g)^![Λ] ⋙
      D((c.i)^*[ModuleCat.{u + 1} Λ]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction _ c.i).comp
    (rightDerivedLowerStarUpperShriekAdjunctionOfIsProper Λ c.g)

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--6`: the counit of
`Rf_!(c) ⊣ Rp^! ⋙ Di^*` is the composite `Rp_* i_! i^* Rp^! N ⟶ Rp_* Rp^! N ⟶ N` of the
counits of `Di_! ⊣ Di^*` and `Rp_* ⊣ Rp^!`. -/
lemma rightDerivedLowerShriekOfCompactificationUpperShriekAdjunction_counit_app
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationUpperShriekAdjunction Λ c).counit.app N =
      R((c.g)_*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ c.i).counit.app
            (R(c.g)^![Λ].obj N)) ≫
        (rightDerivedLowerStarUpperShriekAdjunctionOfIsProper Λ c.g).counit.app N := by
  simp [rightDerivedLowerShriekOfCompactificationUpperShriekAdjunction]

variable [HasCompactification f] [QuasiCompact f]

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--6`: The exceptional
inverse image through a compactification.

For finite `Λ`, a quasi-compact `f : X ⟶ Y` and a compactification
`c = (X ⟶[i] Z ⟶[p] Y)` of `f`, the composite `Rp^! ⋙ Di^*` is right adjoint to
`Rf_!(c) = Di_! ⋙ Rp_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationUpperShriekAdjunction`,
whose counit is the composite of the two counits), hence to `R(f)_! ≅ Rf_!(c)`, and there is a
unique isomorphism `Rf^! ≅ Rp^! ⋙ Di^*` compatible with the adjunctions. -/
theorem existsUnique_rightDerivedUpperShriekOfCompactificationIso :
    ∃! e : R(f)^![Λ] ≅
        R(c.g)^![Λ] ⋙ D((c.i)^*[ModuleCat.{u + 1} Λ]),
      (rightDerivedUpperShriekAdjunction _ f).ofNatIsoRight e =
        (rightDerivedLowerShriekOfCompactificationUpperShriekAdjunction Λ c).ofNatIsoLeft
          (rightDerivedLowerShriekIso Λ c) :=
  Adjunction.existsUnique_ofNatIsoRight_eq _ _

end Compactification

end Etale

end AlgebraicGeometry
