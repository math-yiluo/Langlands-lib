/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.AlgebraicGeometry.ChowLemma.Graph
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Mathlib.Topology.Sober
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Field

/-!
# Étale base change for the derived pushforward

For a cartesian square of schemes whose pullback side `g` is étale, the derived base change map
`g^* Rf_* ⟶ Rf'_* g'^*` of `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`): restriction to an étale
scheme commutes with derived pushforward.

## References

- Stacks Project, Lemma 21.20.4, <https://stacks.math.columbia.edu/tag/0D6G>
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Étale base change for the derived pushforward.** For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` étale, the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on the bounded below derived
categories of sheaves of `Λ`-modules is an isomorphism. Represent a complex by a bounded below
complex `I` of injectives: the derived base change map at `I` is computed by the underived one,
which is an isomorphism by étale base change for the pushforward
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`), followed by the unit
`f'_* g'^* I ⟶ Rf'_* g'^* I`, which is an isomorphism since the pullback along the étale
morphism `g'` preserves injectives (`AlgebraicGeometry.Etale.injective_upperStar_obj_of_etale`).
This is the compatibility of the higher direct images with étale localisation used in blueprint
`prose-08-06` (Stacks 0D6G). -/
theorem Etale.isIso_derivedBaseChangeMapPlus_of_etale (sq : IsPullback g' f' f g) [Etale g] :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : Etale g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ) sq.flip
  have hK : ∀ K, IsIso
      ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
    intro K
    obtain ⟨n, hn⟩ := K.2
    have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
    let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
    let P := (HomotopyCategory.Plus.quotient _).obj M
    suffices IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (DerivedCategory.Plus.Qh.obj P)) by
      rw [← NatTrans.isIso_app_iff_of_iso _
        ((DerivedCategory.Plus.quotientCompQhIso _).app M ≪≫ e)]
      exact this
    have hM : ∀ m, (f')_*[ModuleCat.{u + 1} Λ].rightAcyclic
        ((((g')^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M).obj.X m) := fun m ↦
      have : Injective (M.obj.X m) := (L.obj.X m).2
      have : Injective ((((g')^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M).obj.X m) :=
        Etale.injective_upperStar_obj_of_etale Λ g' (M.obj.X m)
      (f')_*[ModuleCat.{u + 1} Λ].rightAcyclic_of_injective _
    have h₁ : IsIso ((f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
        (((g')^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj P)) :=
      (f')_*[ModuleCat.{u + 1} Λ].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
        (((g')^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M) hM
    have h₂ : IsIso ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) := by
      dsimp only [P, M]
      infer_instance
    have hfac := Etale.derivedBaseChangeMapPlus_fac_app (ModuleCat.{u + 1} Λ) sq.toCommSq P
    have : IsIso (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) ≫
        (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          (DerivedCategory.Plus.Qh.obj P)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P)) _
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry
