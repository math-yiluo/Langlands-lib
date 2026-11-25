/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Base change along a universal homeomorphism

For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

in which `g` is a universal homeomorphism, the base change map `g^* f_* ⟶ f'_* g'^*` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isUniversalHomeomorphism`), and so
is the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on the bounded below derived categories
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism`), with no
hypothesis on `f`.

Both `g^*` and `g'^*` are equivalences of categories of étale sheaves (topological invariance of
the étale site, `AlgebraicGeometry.Etale.isEquivalence_upperStar`). The adjoint of the base
change map under `g^* ⊣ g_*` is `f_* ⟶ f_* g'_* g'^* ≅ g_* f'_* g'^*`
(`AlgebraicGeometry.Etale.unit_map_baseChangeMap_app`), whose first arrow is `f_*` of the unit
of `g'^* ⊣ g'_*`, an isomorphism. For the derived statement represent an object by a bounded
below complex `I` of injective sheaves: its pullback `g'^* I` is again a complex of injective
sheaves, as `g'^*` is an equivalence, so the derived base change map at `I` is the underived one.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Derived base change along a universal homeomorphism**: for a cartesian square whose
horizontal arrow `g` is a universal homeomorphism, the derived base change map
`g^* Rf_* ⟶ Rf'_* g'^*` on the bounded below derived categories is an isomorphism. -/
theorem isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism (sq : IsPullback g' f' f g)
    [IsUniversalHomeomorphism g] : IsIso (derivedBaseChangeMapPlus A sq.toCommSq) := by
  have : IsUniversalHomeomorphism g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isEquivalence_upperStar A g'
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K ↦ ?_
  obtain ⟨n, hn⟩ := K.2
  have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
  let P := (HomotopyCategory.Plus.quotient _).obj M
  suffices IsIso ((derivedBaseChangeMapPlus A sq.toCommSq).app (DerivedCategory.Plus.Qh.obj P)) by
    rw [← NatTrans.isIso_app_iff_of_iso _
      ((DerivedCategory.Plus.quotientCompQhIso _).app M ≪≫ e)]
    exact this
  have hM : ∀ m, (f')_*[A].rightAcyclic
      ((((g')^*[A]).mapCochainComplexPlus.obj M).obj.X m) := fun m ↦
    have : Injective (M.obj.X m) := (L.obj.X m).2
    have : Injective (((g')^*[A]).obj (M.obj.X m)) :=
      ((g')^*[A]).injective_obj_of_injective inferInstance
    (f')_*[A].rightAcyclic_of_injective (((g')^*[A]).obj (M.obj.X m))
  have h₁ : IsIso ((f')_*[A].rightDerivedFunctorPlusUnith.app
      (((g')^*[A]).mapHomotopyCategoryPlus.obj P)) :=
    (f')_*[A].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
      (((g')^*[A]).mapCochainComplexPlus.obj M) hM
  have h₂ : IsIso ((f)_*[A].rightDerivedFunctorPlusUnith.app P) := by
    dsimp only [P, M]
    infer_instance
  have hfac := derivedBaseChangeMapPlus_fac_app A sq.toCommSq P
  have : IsIso (((g)^*[A]).mapDerivedCategoryPlus.map
      ((f)_*[A].rightDerivedFunctorPlusUnith.app P) ≫
      (derivedBaseChangeMapPlus A sq.toCommSq).app (DerivedCategory.Plus.Qh.obj P)) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left (((g)^*[A]).mapDerivedCategoryPlus.map
      ((f)_*[A].rightDerivedFunctorPlusUnith.app P)) _

end Etale

end AlgebraicGeometry
