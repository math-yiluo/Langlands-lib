/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!
# The mate of the composition law for the constructible `Rf^!`

Let `X ⟶[f] Y ⟶[g] Z` be morphisms admitting compactifications. The constructible exceptional
inverse image `Rf^! = ν_X^* f^× Rν_{Y,*}` of the small pro-étale sites
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`) is right adjoint to `Rf_!` on the bounded
below objects of étale origin (blueprint `theorem-existence-exceptional-inverse-image` (c),
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction`). This file proves clause (b) of
blueprint `proposition-composition-open-restriction-compactifications-f--1` in its constructible
form: the mate of the composition isomorphism `R(g ∘ f)_! ≅ Rg_! Rf_!` under these adjunctions is an
isomorphism `R(g ∘ f)^! ≅ Rf^! Rg^!` of functors `D⁺(Z_proét) ⥤ D⁺(X_proét)`, the unit and counit of
the composite adjunction being the pasted ones; and it restricts to `Dctf` as soon as the three
functors preserve `Dctf`. It also records the formal clause (a), for the ambient right adjoints, and
that the constructible adjunction is the restriction of any ambient one.

## Main definitions

- `AlgebraicGeometry.ProEtale.comparisonUpperStarPlusEtaleOrigin`: `ν^*` as a functor from
  `D⁺(X_ét)` to the bounded below objects of étale origin in `D(X_proét)`; it is an equivalence.

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_iso_ι_comp_rightDerivedLowerShriek_comp`: the composition
  law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the pro-étale `Rf_!` on objects bounded below of étale
  origin, transported from the étale one (blueprint
  `proposition-composition-base-change-rf-shriek--1`).
- `AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq`: the mate
  statement on any full subcategories preserved by the six functors involved.
- `AlgebraicGeometry.ProEtale.nonempty_iso_rightDerivedUpperShriekPlus_comp`:
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` on `D⁺(Z_proét)`.
- `AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq_of_finiteTor`: the
  restriction to `Dctf`.
- `HasAmbientExceptionalRightAdjoint.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv` (in the
  namespace `AlgebraicGeometry.ProEtale`): clause (a), the ambient form.
- `HasAmbientExceptionalRightAdjoint.compIso`: clause (a), the isomorphism of ambient functors
  `Rg^× ⋙ Rf^× ≅ R(f ≫ g)^×` mate to an ambient composition isomorphism, with its unit and counit
  lemmas; `HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_iff`: it exists exactly when the
  ambient composition law does.
- `HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_yoneda_comp_whiskeringLeft`: clause (a)
  with the composition law of `proposition-composition-base-change-rf-shriek--1`.
- `AlgebraicGeometry.ProEtale.exists_bijective_comp_and_homEquiv_symm_comp_eq`: under the ambient
  datum, the constructible adjunction is the restriction of the ambient one.

## Implementation notes

The composition law of the pro-étale `Rf_!` is only available through the étale one
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, which asserts that *some*
isomorphism exists; this is why the mate statements are existential in the isomorphism of left
adjoints. Being formal, they hold for every such isomorphism.

Clause (a) of `proposition-composition-open-restriction-compactifications-f--1` takes the mate of
"the composition isomorphism `R(gf)_! ≅ Rg_! Rf_!` of
`proposition-composition-base-change-rf-shriek--1`" on the *ambient* functors, but that node only
gives the composition law on bounded below objects of étale origin. So clause (a) is stated for a
given ambient composition isomorphism (`HasAmbientExceptionalRightAdjoint.compIso`), and
`HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_iff` records that the ambient isomorphism
`R(f ≫ g)^× ≅ Rg^× ⋙ Rf^×` exists exactly when the ambient composition law does. The ambient
composition law on all of `D(X_proét)` is not stated. Comparing the chosen compactifications needs
proper base change at the boundary for arbitrary unbounded pro-étale sheaves, which is not known.
The datum `FullCD` does not help: it bounds only the proper parts of the three chosen
compactifications, not those of the auxiliary compactifications used in the comparison.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section EtaleOrigin

variable (X : Scheme.{u})

/-- An object bounded below of étale origin is bounded below. -/
lemma DerivedCategory.plusEtaleOrigin_le_plus :
    DerivedCategory.plusEtaleOrigin A X ≤ DerivedCategory.TStructure.t.plus :=
  fun _ hK ↦ hK.plus

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The comparison functor `ν^* : D⁺(X_ét) ⥤ D(X_proét)`, corestricted to the full subcategory of
objects bounded below of étale origin. It is an equivalence
(`AlgebraicGeometry.ProEtale.isEquivalence_comparisonUpperStarPlusEtaleOrigin`): full and faithful
by blueprint `theorem-bounded-below-cohomology-comparison`, and essentially surjective by
definition. -/
noncomputable def comparisonUpperStarPlusEtaleOrigin :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      (DerivedCategory.plusEtaleOrigin A X).FullSubcategory :=
  ObjectProperty.lift _ (DerivedCategory.Plus.ι ⋙ D(ν^*(X)[A]))
    (fun K ↦ DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property)

instance : (comparisonUpperStarPlusEtaleOrigin A X).Faithful where
  map_injective {K L} φ ψ h := by
    ext
    exact (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).1
      (congrArg (fun φ ↦ φ.hom) h)

instance : (comparisonUpperStarPlusEtaleOrigin A X).Full where
  map_surjective {K L} φ := by
    obtain ⟨ψ, hψ⟩ :=
      (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).2 φ.hom
    exact ⟨ObjectProperty.homMk ψ, by ext; exact hψ⟩

instance : (comparisonUpperStarPlusEtaleOrigin A X).EssSurj where
  mem_essImage K := by
    obtain ⟨K', hK', ⟨e⟩⟩ := K.property
    exact ⟨⟨K', hK'⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

instance isEquivalence_comparisonUpperStarPlusEtaleOrigin :
    (comparisonUpperStarPlusEtaleOrigin A X).IsEquivalence where

end EtaleOrigin

section Composition

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y)
  (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`, on the pro-étale site: the
composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the pro-étale derived lower shriek, as functors on the
objects of `D(X_proét)` bounded below of étale origin, for finite coefficients. It is transported
from the étale composition law `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`
along the compact-support comparison `Rf_! ν^* ≅ ν^* Rf^{ét}_!`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`) and the equivalence
`AlgebraicGeometry.ProEtale.comparisonUpperStarPlusEtaleOrigin`. -/
theorem nonempty_iso_ι_comp_rightDerivedLowerShriek_comp :
    Nonempty ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) := by
  obtain ⟨e⟩ := Etale.nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X
  let ι := DerivedCategory.Plus.ι (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let ιY := DerivedCategory.Plus.ι (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let Ef := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f
  let Eg := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g
  let νY := D(ν^*(Y)[ModuleCat.{u + 1} Λ])
  let νZ := D(ν^*(Z)[ModuleCat.{u + 1} Λ])
  let compat := Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} Λ) f
  -- the composition law after precomposition with the equivalence `Φ`
  let e' : Φ ⋙ (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      Φ ⋙ (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
    rightDerivedLowerShriekComparisonIso _ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft ι (Functor.isoWhiskerRight e νZ) ≪≫
      Functor.isoWhiskerLeft ι (Functor.associator Ef Eg νZ) ≪≫
      (Functor.associator ι Ef (Eg ⋙ νZ)).symm ≪≫
      Functor.isoWhiskerRight compat.symm (Eg ⋙ νZ) ≪≫
      Functor.associator _ ιY (Eg ⋙ νZ) ≪≫
      Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
        (rightDerivedLowerShriekComparisonIso _ g).symm ≪≫
      (Functor.associator _ ιY (νY ⋙ R(g)_![ModuleCat.{u + 1} Λ])).symm ≪≫
      Functor.isoWhiskerRight compat (νY ⋙ R(g)_![ModuleCat.{u + 1} Λ]) ≪≫
      Functor.associator ι Ef (νY ⋙ R(g)_![ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft ι (Functor.associator Ef νY R(g)_![ModuleCat.{u + 1} Λ]).symm ≪≫
      (Functor.associator ι (Ef ⋙ νY) R(g)_![ModuleCat.{u + 1} Λ]).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedLowerShriekComparisonIso _ f).symm
        R(g)_![ModuleCat.{u + 1} Λ] ≪≫
      Functor.associator _ _ _
  exact ⟨(Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso e'⟩

variable {Λ}

variable [CompactSpace Y] [CompactSpace Z]

variable (PX : ObjectProperty (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
  (PY : ObjectProperty (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))))
  (PZ : ObjectProperty (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))))
  (hPX : PX ≤ DerivedCategory.plusEtaleOrigin _ X)
  (hPY : PY ≤ DerivedCategory.plusEtaleOrigin _ Y) (hPZ : PZ ≤ DerivedCategory.TStructure.t.plus)
  (hf₁ : ∀ K, PX K → PY ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))
  (hf₂ : ∀ L, PY L → PX ((R(f)^![Λ]).obj L))
  (hg₁ : ∀ K, PY K → PZ ((R(g)_![ModuleCat.{u + 1} Λ]).obj K))
  (hg₂ : ∀ L, PZ L → PY ((R(g)^![Λ]).obj L))
  (hfg₁ : ∀ K, PX K → PZ ((R(f ≫ g)_![ModuleCat.{u + 1} Λ]).obj K))
  (hfg₂ : ∀ L, PZ L → PX ((R(f ≫ g)^![Λ]).obj L))

omit [CompactSpace Y] [CompactSpace Z] in
include hPX in
/-- The composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of
`AlgebraicGeometry.ProEtale.nonempty_iso_ι_comp_rightDerivedLowerShriek_comp`, restricted to full
subcategories `PX`, `PY`, `PZ` preserved by the lower shrieks, `PX` consisting of objects bounded
below of étale origin. -/
theorem nonempty_iso_lift_rightDerivedLowerShriek_comp :
    Nonempty (PZ.lift (PX.ι ⋙ R(f ≫ g)_![ModuleCat.{u + 1} Λ]) (fun K ↦ hfg₁ _ K.property) ≅
      PY.lift (PX.ι ⋙ R(f)_![ModuleCat.{u + 1} Λ]) (fun K ↦ hf₁ _ K.property) ⋙
        PZ.lift (PY.ι ⋙ R(g)_![ModuleCat.{u + 1} Λ]) (fun K ↦ hg₁ _ K.property)) := by
  obtain ⟨e⟩ := nonempty_iso_ι_comp_rightDerivedLowerShriek_comp Λ f g
  exact ⟨(PZ.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ObjectProperty.ιOfLE hPX) e)⟩

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (b),
constructible form, on full subcategories: let `PX`, `PY` be full subcategories of objects bounded
below of étale origin and `PZ` one of bounded below objects, preserved by `Rf_!`, `Rg_!`,
`R(f ≫ g)_!` and by `Rf^!`, `Rg^!`, `R(f ≫ g)^!`, so that the exceptional adjunctions of blueprint
`theorem-existence-exceptional-inverse-image` (c) restrict to them
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction`). Then there is a composition
isomorphism `e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of left adjoints whose mate `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!`
carries the adjunction `R(f ≫ g)_! ⊣ R(f ≫ g)^!` to the composite adjunction
`Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`: the unit and counit of the composite adjunction are the pasted ones. -/
theorem exists_rightDerivedUpperShriekAdjunction_comp_eq :
    ∃ e : PZ.lift (PX.ι ⋙ R(f ≫ g)_![ModuleCat.{u + 1} Λ]) (fun K ↦ hfg₁ _ K.property) ≅
        PY.lift (PX.ι ⋙ R(f)_![ModuleCat.{u + 1} Λ]) (fun K ↦ hf₁ _ K.property) ⋙
          PZ.lift (PY.ι ⋙ R(g)_![ModuleCat.{u + 1} Λ]) (fun K ↦ hg₁ _ K.property),
      ((rightDerivedUpperShriekAdjunction (f ≫ g) PX PZ hPX hPZ hfg₁ hfg₂).ofNatIsoLeft
          e).ofNatIsoRight
        (conjugateIsoEquiv
          ((rightDerivedUpperShriekAdjunction f PX PY hPX
              (hPY.trans (DerivedCategory.plusEtaleOrigin_le_plus _ Y)) hf₁ hf₂).comp
            (rightDerivedUpperShriekAdjunction g PY PZ hPY hPZ hg₁ hg₂))
          (rightDerivedUpperShriekAdjunction (f ≫ g) PX PZ hPX hPZ hfg₁ hfg₂) e).symm =
        (rightDerivedUpperShriekAdjunction f PX PY hPX
            (hPY.trans (DerivedCategory.plusEtaleOrigin_le_plus _ Y)) hf₁ hf₂).comp
          (rightDerivedUpperShriekAdjunction g PY PZ hPY hPZ hg₁ hg₂) := by
  obtain ⟨e⟩ := nonempty_iso_lift_rightDerivedLowerShriek_comp f g PX PY PZ hPX hf₁ hg₁ hfg₁
  exact ⟨e, Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ e⟩

end Composition

section LowerShriek

variable {A} {Λ} {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The pro-étale `Rf_!` carries an object bounded below of étale origin to an object bounded
below of étale origin, by the compact-support comparison `Rf_! ν^* ≅ ν^* Rf^{ét}_!` on `D⁺`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`). -/
lemma DerivedCategory.plusEtaleOrigin.rightDerivedLowerShriek_obj
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K) :
    DerivedCategory.plusEtaleOrigin A Y ((R(f)_![A]).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  refine (DerivedCategory.plusEtaleOrigin A Y).prop_of_iso
    (((rightDerivedLowerShriekComparisonIso A f).app ⟨K', hK'⟩).symm ≪≫
      (R(f)_![A]).mapIso e) ?_
  exact DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
    (DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.rightDerivedLowerShriekPlusCompatibility A f).app ⟨K', hK'⟩)
      ((Etale.rightDerivedLowerShriekPlus A f).obj ⟨K', hK'⟩).property)

end LowerShriek

section BoundedBelow

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y)
  (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [CompactSpace Y] [CompactSpace Z]

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (b),
constructible form: the mate of the composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on the
bounded below objects of étale origin, under the exceptional adjunctions of blueprint
`theorem-existence-exceptional-inverse-image` (c), is an isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` of
functors `D⁺(Z_proét) ⥤ D⁺(X_proét)`, for finite coefficients. That it is the mate, with the pasted
unit and counit, is `AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq`
for the objects of étale origin over `X` and `Y` and the bounded below objects over `Z`. -/
theorem nonempty_iso_rightDerivedUpperShriekPlus_comp :
    Nonempty (R(f ≫ g)^![Λ]+ ≅
      R(g)^![Λ]+ ⋙ R(f)^![Λ]+) := by
  have hle := DerivedCategory.plusEtaleOrigin_le_plus (ModuleCat.{u + 1} Λ)
  have hf₁ : ∀ K, DerivedCategory.plusEtaleOrigin _ X K →
      DerivedCategory.plusEtaleOrigin _ Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
    fun _ hK ↦ hK.rightDerivedLowerShriek_obj f
  have hg₁ : ∀ K, DerivedCategory.plusEtaleOrigin _ Y K →
      DerivedCategory.TStructure.t.plus ((R(g)_![ModuleCat.{u + 1} Λ]).obj K) :=
    fun _ hK ↦ (hK.rightDerivedLowerShriek_obj g).plus
  have hfg₁ : ∀ K, DerivedCategory.plusEtaleOrigin _ X K →
      DerivedCategory.TStructure.t.plus ((R(f ≫ g)_![ModuleCat.{u + 1} Λ]).obj K) :=
    fun _ hK ↦ (hK.rightDerivedLowerShriek_obj (f ≫ g)).plus
  obtain ⟨e⟩ := nonempty_iso_lift_rightDerivedLowerShriek_comp f g _ _ _ le_rfl hf₁ hg₁ hfg₁
  let adjf := rightDerivedUpperShriekAdjunction f _ _ le_rfl (hle Y) hf₁
    (fun _ hL ↦ plusEtaleOrigin_rightDerivedUpperShriek_obj f hL.plus)
  let adjg := rightDerivedUpperShriekAdjunction g _ _ le_rfl le_rfl hg₁
    (fun _ hL ↦ plusEtaleOrigin_rightDerivedUpperShriek_obj g hL)
  let adjfg := rightDerivedUpperShriekAdjunction (f ≫ g) _ _ le_rfl le_rfl hfg₁
    (fun _ hL ↦ plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL)
  exact ⟨Functor.isoWhiskerRight (conjugateIsoEquiv (adjf.comp adjg) adjfg e).symm
    (ObjectProperty.ιOfLE (hle X))⟩

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (b),
restriction to `Dctf`: as soon as `Rf_!`, `Rg_!`, `R(f ≫ g)_!` and `Rf^!`, `Rg^!`, `R(f ≫ g)^!`
preserve the bounded constructible objects of finite Tor amplitude, the exceptional adjunctions
restrict to `Dctf`, and the mate of a composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the
restricted functors is an isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` of functors `Dctf(Z) ⥤ Dctf(X)`
carrying the adjunction of `f ≫ g` to the composite adjunction. -/
theorem exists_rightDerivedUpperShriekAdjunction_comp_eq_of_finiteTor
    (hf₁ : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor _ Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))
    (hf₂ : ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
      DerivedCategory.constructibleFiniteTor _ X ((R(f)^![Λ]).obj L))
    (hg₁ : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor _ Z ((R(g)_![ModuleCat.{u + 1} Λ]).obj K))
    (hg₂ : ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z L →
      DerivedCategory.constructibleFiniteTor _ Y ((R(g)^![Λ]).obj L))
    (hfg₁ : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor _ Z ((R(f ≫ g)_![ModuleCat.{u + 1} Λ]).obj K))
    (hfg₂ : ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z L →
      DerivedCategory.constructibleFiniteTor _ X ((R(f ≫ g)^![Λ]).obj L)) :
    ∃ e : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).lift
          ((DerivedCategory.constructibleFiniteTor _ X).ι ⋙ R(f ≫ g)_![ModuleCat.{u + 1} Λ])
          (fun K ↦ hfg₁ _ K.property) ≅
        (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).lift
            ((DerivedCategory.constructibleFiniteTor _ X).ι ⋙ R(f)_![ModuleCat.{u + 1} Λ])
            (fun K ↦ hf₁ _ K.property) ⋙
          (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).lift
            ((DerivedCategory.constructibleFiniteTor _ Y).ι ⋙ R(g)_![ModuleCat.{u + 1} Λ])
            (fun K ↦ hg₁ _ K.property),
      ((rightDerivedUpperShriekAdjunction (f ≫ g) _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
          (fun _ hK ↦ hK.plus) hfg₁ hfg₂).ofNatIsoLeft e).ofNatIsoRight
        (conjugateIsoEquiv
          ((rightDerivedUpperShriekAdjunction f _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
              (fun _ hK ↦ hK.plus) hf₁ hf₂).comp
            (rightDerivedUpperShriekAdjunction g _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
              (fun _ hK ↦ hK.plus) hg₁ hg₂))
          (rightDerivedUpperShriekAdjunction (f ≫ g) _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
            (fun _ hK ↦ hK.plus) hfg₁ hfg₂) e).symm =
        (rightDerivedUpperShriekAdjunction f _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
            (fun _ hK ↦ hK.plus) hf₁ hf₂).comp
          (rightDerivedUpperShriekAdjunction g _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
            (fun _ hK ↦ hK.plus) hg₁ hg₂) :=
  exists_rightDerivedUpperShriekAdjunction_comp_eq f g _ _ _ _ _ _ hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂

end BoundedBelow

section Ambient

variable {A} {Λ} {X Y Z : Scheme.{u}}

/-- The ambient adjunction `Rf_! ⊣ Rf^×` on the unbounded derived categories of the small
pro-étale sites, which the ambient exceptional right adjoint datum supplies
(blueprint `theorem-existence-exceptional-inverse-image` (b),
`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`). -/
noncomputable def HasAmbientExceptionalRightAdjoint.adjunction {f : X ⟶ Y}
    [HasCompactification f] (h : HasAmbientExceptionalRightAdjoint A f) :
    R(f)_![A] ⊣ @Functor.rightAdjoint _ _ _ _ (R(f)_![A]) h.isLeftAdjoint :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ _ h.isLeftAdjoint

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (a), the
ambient form: if `f`, `g` and `f ≫ g` carry the ambient exceptional right adjoint datum of blueprint
`sk-def-sf-admissible` (1), then the mate of any composition isomorphism
`e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the ambient functors is an isomorphism `Rg^× ⋙ Rf^× ≅ R(f ≫ g)^×`,
which carries the adjunction `R(f ≫ g)_! ⊣ R(f ≫ g)^×` to the composite adjunction
`Rf_! ⋙ Rg_! ⊣ Rg^× ⋙ Rf^×`: the unit and counit of the composite adjunction are the pasted ones.
Nothing here uses constructibility; the datum is only used through the adjunctions it supplies. The
datum fails in general (`sk-rem-sf-fullcd-scope`), and the constructible form of clause (b) does not
assume it. -/
theorem HasAmbientExceptionalRightAdjoint.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] (hf : HasAmbientExceptionalRightAdjoint A f)
    (hg : HasAmbientExceptionalRightAdjoint A g)
    (hfg : HasAmbientExceptionalRightAdjoint A (f ≫ g))
    (e : R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) :
    (hfg.adjunction.ofNatIsoLeft e).ofNatIsoRight
        (conjugateIsoEquiv (hf.adjunction.comp hg.adjunction) hfg.adjunction e).symm =
      hf.adjunction.comp hg.adjunction :=
  Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ e

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (a): the
isomorphism of ambient functors `Rg^× ⋙ Rf^× ≅ R(f ≫ g)^× : D(Z_proét) ⥤ D(X_proét)`. If `f`, `g`
and `f ≫ g` carry the ambient exceptional right adjoint datum, it is the mate of a composition
isomorphism `e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the ambient functors under the ambient adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^×` and `Rf_! ⋙ Rg_! ⊣ Rg^× ⋙ Rf^×`. The second adjunction is the composite
one, whose unit and counit are the pasted ones. -/
noncomputable def HasAmbientExceptionalRightAdjoint.compIso {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : HasAmbientExceptionalRightAdjoint A f) (hg : HasAmbientExceptionalRightAdjoint A g)
    (hfg : HasAmbientExceptionalRightAdjoint A (f ≫ g))
    (e : R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) :
    @Functor.rightAdjoint _ _ _ _ (R(g)_![A]) hg.isLeftAdjoint ⋙
        @Functor.rightAdjoint _ _ _ _ (R(f)_![A]) hf.isLeftAdjoint ≅
      @Functor.rightAdjoint _ _ _ _ (R(f ≫ g)_![A]) hfg.isLeftAdjoint :=
  conjugateIsoEquiv (hf.adjunction.comp hg.adjunction) hfg.adjunction e

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (a), units:
under the isomorphism `HasAmbientExceptionalRightAdjoint.compIso`, the pasted unit
`K ⟶ Rf^× Rg^× Rg_! Rf_! K` of `Rf_! ⋙ Rg_! ⊣ Rg^× ⋙ Rf^×` corresponds to the unit of
`R(f ≫ g)_! ⊣ R(f ≫ g)^×`. -/
lemma HasAmbientExceptionalRightAdjoint.unit_comp_compIso_hom_app {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : HasAmbientExceptionalRightAdjoint A f) (hg : HasAmbientExceptionalRightAdjoint A g)
    (hfg : HasAmbientExceptionalRightAdjoint A (f ≫ g))
    (e : R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A])
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (hf.adjunction.comp hg.adjunction).unit.app K ≫ (hf.compIso hg hfg e).hom.app _ =
      hfg.adjunction.unit.app K ≫
        (@Functor.rightAdjoint _ _ _ _ (R(f ≫ g)_![A]) hfg.isLeftAdjoint).map (e.hom.app K) :=
  unit_conjugateEquiv _ _ e.hom K

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (a),
counits: under the isomorphism `HasAmbientExceptionalRightAdjoint.compIso`, the counit of
`R(f ≫ g)_! ⊣ R(f ≫ g)^×` corresponds to the pasted counit `Rg_! Rf_! Rf^× Rg^× L ⟶ L` of
`Rf_! ⋙ Rg_! ⊣ Rg^× ⋙ Rf^×`. -/
lemma HasAmbientExceptionalRightAdjoint.map_compIso_hom_app_counit {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : HasAmbientExceptionalRightAdjoint A f) (hg : HasAmbientExceptionalRightAdjoint A g)
    (hfg : HasAmbientExceptionalRightAdjoint A (f ≫ g))
    (e : R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A])
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (R(f ≫ g)_![A]).map ((hf.compIso hg hfg e).hom.app L) ≫ hfg.adjunction.counit.app L =
      e.hom.app _ ≫ (hf.adjunction.comp hg.adjunction).counit.app L :=
  conjugateEquiv_counit _ _ e.hom L

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (a): if `f`,
`g` and `f ≫ g` carry the ambient exceptional right adjoint datum, the ambient right adjoints
satisfy `R(f ≫ g)^× ≅ Rg^× ⋙ Rf^×` exactly when the ambient left adjoints satisfy the composition
law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`. The forward direction is
`HasAmbientExceptionalRightAdjoint.compIso`, the mate of the composition isomorphism. -/
theorem HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_iff {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : HasAmbientExceptionalRightAdjoint A f) (hg : HasAmbientExceptionalRightAdjoint A g)
    (hfg : HasAmbientExceptionalRightAdjoint A (f ≫ g)) :
    Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) ↔
      Nonempty (@Functor.rightAdjoint _ _ _ _ (R(f ≫ g)_![A]) hfg.isLeftAdjoint ≅
        @Functor.rightAdjoint _ _ _ _ (R(g)_![A]) hg.isLeftAdjoint ⋙
          @Functor.rightAdjoint _ _ _ _ (R(f)_![A]) hf.isLeftAdjoint) :=
  ⟨fun ⟨e⟩ ↦ ⟨(hf.compIso hg hfg e).symm⟩,
    fun ⟨r⟩ ↦ ⟨(conjugateIsoEquiv (hf.adjunction.comp hg.adjunction) hfg.adjunction).symm r.symm⟩⟩

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`: when the ambient
datum of clause (a) holds, clause (b) is its restriction. For any right adjoint `G` of the pro-étale
`Rf_!` (for instance the ambient `Rf^×` of clause (a)) and a bounded below `L`, the transpose
`φ : Rf^! L ⟶ G L` of the counit `Rf_! Rf^! L ⟶ L` of blueprint
`theorem-existence-exceptional-inverse-image` (c) identifies the two adjunctions on the objects `K`
bounded below of étale origin: composing with `φ` is a bijection `Hom(K, Rf^! L) ≃ Hom(K, G L)`,
under which the adjunction `Rf_! ⊣ G` restricts to the exceptional adjunction of
`theorem-existence-exceptional-inverse-image` (c). -/
theorem exists_bijective_comp_and_homEquiv_symm_comp_eq {f : X ⟶ Y} [HasCompactification f]
    [CompactSpace Y]
    {G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (adj : R(f)_![ModuleCat.{u + 1} Λ] ⊣ G) {L : _root_.DerivedCategory (Sheaf
        (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    ∃ φ : (R(f)^![Λ]).obj L ⟶ G.obj L,
      ∀ {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
        (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K),
        Function.Bijective (fun a : K ⟶ (R(f)^![Λ]).obj L ↦ a ≫ φ) ∧
          ∀ a : K ⟶ (R(f)^![Λ]).obj L,
            (adj.homEquiv _ _).symm (a ≫ φ) = (rightDerivedUpperShriekHomEquiv f hK hL).symm a := by
  refine ⟨adj.homEquiv _ _ (rightDerivedUpperShriekCounit f L hL), fun {K} hK ↦ ?_⟩
  have h : ∀ a : K ⟶ (R(f)^![Λ]).obj L, (adj.homEquiv _ _).symm
      (a ≫ adj.homEquiv _ _ (rightDerivedUpperShriekCounit f L hL)) =
        (rightDerivedUpperShriekHomEquiv f hK hL).symm a := by
    intro a
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
      rightDerivedUpperShriekHomEquiv_symm_apply]
  refine ⟨?_, h⟩
  have hc : (fun a : K ⟶ (R(f)^![Λ]).obj L ↦
      a ≫ adj.homEquiv _ _ (rightDerivedUpperShriekCounit f L hL)) =
      ⇑(adj.homEquiv K L) ∘ ⇑(rightDerivedUpperShriekHomEquiv f hK hL).symm := by
    ext a : 1
    simp only [Function.comp_apply, ← h, Equiv.apply_symm_apply]
  rw [hc]
  exact (adj.homEquiv K L).bijective.comp (rightDerivedUpperShriekHomEquiv f hK hL).symm.bijective

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- Blueprint `proposition-composition-open-restriction-compactifications-f--1`, clause (a), with
the composition law of `proposition-composition-base-change-rf-shriek--1`: if `f`, `g` and `f ≫ g`
carry the ambient exceptional right adjoint datum, the mate of the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on the objects bounded below of étale origin
(`nonempty_iso_ι_comp_rightDerivedLowerShriek_comp`, which is where blueprint
`proposition-composition-base-change-rf-shriek--1` provides it) under the ambient adjunctions is a
natural isomorphism `Hom(K, R(f ≫ g)^× L) ≅ Hom(K, Rf^× Rg^× L)`, natural in `L ∈ D(Z_proét)` and in
`K` bounded below of étale origin. It is the composite of the adjunction bijection of
`R(f ≫ g)_! ⊣ R(f ≫ g)^×`, the composition isomorphism, and the adjunction bijection of the pasted
adjunction `Rf_! ⋙ Rg_! ⊣ Rg^× ⋙ Rf^×`. -/
theorem HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_yoneda_comp_whiskeringLeft
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)]
    (hf : HasAmbientExceptionalRightAdjoint (ModuleCat.{u + 1} Λ) f)
    (hg : HasAmbientExceptionalRightAdjoint (ModuleCat.{u + 1} Λ) g)
    (hfg : HasAmbientExceptionalRightAdjoint (ModuleCat.{u + 1} Λ) (f ≫ g)) :
    Nonempty ((@Functor.rightAdjoint _ _ _ _ (R(f ≫ g)_![ModuleCat.{u + 1} Λ])
          hfg.isLeftAdjoint ⋙ yoneda) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι.op ≅
      ((@Functor.rightAdjoint _ _ _ _ (R(g)_![ModuleCat.{u + 1} Λ]) hg.isLeftAdjoint ⋙
          @Functor.rightAdjoint _ _ _ _ (R(f)_![ModuleCat.{u + 1} Λ]) hf.isLeftAdjoint) ⋙
          yoneda) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι.op) := by
  obtain ⟨e⟩ := nonempty_iso_ι_comp_rightDerivedLowerShriek_comp Λ f g
  exact ⟨Functor.isoWhiskerRight hfg.adjunction.compYonedaIso _ ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    Functor.isoWhiskerLeft yoneda ((Functor.whiskeringLeft _ _ _).mapIso (NatIso.op e)).symm ≪≫
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) : _ ≅ (yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
      (R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]).op) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι.op) ≪≫
    (Functor.isoWhiskerRight (hf.adjunction.comp hg.adjunction).compYonedaIso _).symm⟩
end Ambient

end AlgebraicGeometry.ProEtale
