/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap

/-!
# The Leray edge maps and base change

For a commutative square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
and an abelian étale sheaf `G` on `X`, the edge maps `E_f : Hⁿ(Y, f_* G) ⟶ Hⁿ(X, G)` and
`E_{f'} : Hⁿ(Y', f'_* g'^* G) ⟶ Hⁿ(X', g'^* G)` (`AlgebraicGeometry.Etale.cohomologyMap` followed
by the counit) are compatible with the pullback maps along `g`, `g'` and the base change map
`g^* f_* ⟶ f'_* g'^*`, up to an automorphism of the constant sheaf `ℤ_{X'}`. This is what is needed
to transport the bijectivity of the edge maps for finite morphisms along a base change.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap`: pulling back along `b` and then along
  `a` is pushing forward along `b^* ⋙ a^*`.
- `AlgebraicGeometry.Etale.exists_edgeMap_baseChangeMap_cohomologyMap`: the compatibility of
  the edge maps with base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
/-- Pulling back an étale cohomology class along `b` and then along `a` is pushing it forward
along `b^* ⋙ a^*`, up to the comparison of constant sheaves. -/
lemma cohomologyMap_cohomologyMap {W Z Y : Scheme.{u}} (a : W ⟶ Z) (b : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n) :
    have := comp_preservesFiniteLimits ((b)^*[AddCommGrpCat.{u + 1}]) ((a)^*[AddCommGrpCat.{u + 1}])
    have := comp_preservesFiniteColimits ((b)^*[AddCommGrpCat.{u + 1}])
      ((a)^*[AddCommGrpCat.{u + 1}])
    cohomologyMap a _ n (cohomologyMap b F n x) =
      (Ext.mk₀ ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} a).symm.app
          (AddCommGrpCat.of (ULift ℤ)) ≪≫ ((a)^*[AddCommGrpCat.{u + 1}]).mapIso
          ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} b).symm.app
            (AddCommGrpCat.of (ULift ℤ)))).hom).comp
        (x.mapExactFunctor ((b)^*[AddCommGrpCat.{u + 1}] ⋙ (a)^*[AddCommGrpCat.{u + 1}]))
        (zero_add n) := by
  intro _ _
  rw [cohomologyMap_apply, cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mapExactFunctor,
    ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  rfl

/-- **The edge maps commute with base change**, up to an automorphism `α` of the constant
sheaf `ℤ_{X'}`: `E_{f'} ∘ (g^* f_* ⟶ f'_* g'^*) ∘ g^* = α^* ∘ g'^* ∘ E_f`. -/
theorem exists_edgeMap_baseChangeMap_cohomologyMap (sq : CommSq g' f' f g)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ∃ α : (constantSheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
        (constantSheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ)),
      ∀ x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) n,
        Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
            (((g')^*[AddCommGrpCat.{u + 1}]).obj G)) n
          (cohomologyMap f' _ n (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq).app G) n
            (cohomologyMap g _ n x))) =
        (Ext.mk₀ α.hom).comp (cohomologyMap g' _ n
          (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) n
            (cohomologyMap f _ n x))) (zero_add n) := by
  have := comp_preservesFiniteLimits ((g)^*[AddCommGrpCat.{u + 1}]) ((f')^*[AddCommGrpCat.{u + 1}])
  have := comp_preservesFiniteColimits ((g)^*[AddCommGrpCat.{u + 1}])
    ((f')^*[AddCommGrpCat.{u + 1}])
  have := comp_preservesFiniteLimits ((f)^*[AddCommGrpCat.{u + 1}]) ((g')^*[AddCommGrpCat.{u + 1}])
  have := comp_preservesFiniteColimits ((f)^*[AddCommGrpCat.{u + 1}])
    ((g')^*[AddCommGrpCat.{u + 1}])
  let ℤY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let σ := squareUpperStarIso AddCommGrpCat.{u + 1} sq
  let P := ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f').symm.app
      (AddCommGrpCat.of (ULift ℤ)) ≪≫ ((f')^*[AddCommGrpCat.{u + 1}]).mapIso
      ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
        (AddCommGrpCat.of (ULift ℤ))))
  let Q := ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g').symm.app
      (AddCommGrpCat.of (ULift ℤ)) ≪≫ ((g')^*[AddCommGrpCat.{u + 1}]).mapIso
      ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift ℤ))))
  refine ⟨P ≪≫ σ.app ℤY ≪≫ Q.symm, fun x ↦ ?_⟩
  have h₁ := cohomologyMap_map (f := f') (n := n)
    ((baseChangeMap AddCommGrpCat.{u + 1} sq).app G) (cohomologyMap g _ n x)
  have h₂ := cohomologyMap_map (f := g') (n := n)
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) (cohomologyMap f _ n x)
  have h₃ := upperStar_map_baseChangeMap_app_counit AddCommGrpCat.{u + 1} sq G
  dsimp only [Functor.comp_obj, Functor.id_obj] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, ← Sheaf.H.map_comp_apply, h₃, Sheaf.H.map_comp_apply]
  rw [cohomologyMap_cohomologyMap, cohomologyMap_cohomologyMap]
  rw [Ext.mapExactFunctor_eq_of_iso σ x]
  simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [← Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  congr 2
  simp [P, Q, σ, ℤY]

end AlgebraicGeometry.Etale
