/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The low-degree edge maps of the Leray spectral sequence in étale cohomology

For a morphism of schemes `f : X ⟶ Y` and an abelian étale sheaf `G` on `X`, the edge map
`H^n(Y, f_* G) ⟶ H^n(X, G)` of the Leray spectral sequence
`E₂^{p,q} = H^p(Y, R^q f_* G) ⇒ H^{p+q}(X, G)` is the pullback map
`AlgebraicGeometry.Etale.cohomologyMap f (f_* G) n` followed by the counit `f^* f_* G ⟶ G`.
We prove the injectivity statements of the five-term exact sequence that we need, without
constructing the spectral sequence: the edge map is injective in degree `1`, and in degree `2`
as soon as `R¹f_* G = 0`.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_eq_map_counit_comp`: the pullback map on cohomology
  factors through the unit `F ⟶ f_* f^* F` and the edge map.
- `AlgebraicGeometry.Etale.injective_edgeMap_one`: the edge map is injective in degree `1`.
- `AlgebraicGeometry.Etale.injective_edgeMap_two`: the edge map is injective in degree `2` if
  `f_*` maps the cokernel of a monomorphism `G ⟶ I` into an injective sheaf to an epimorphism,
  that is, if `R¹f_* G = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The edge map `H^n(Y, f_* G) ⟶ H^n(X, G)` is, up to the isomorphism `ℤ_X ≅ f^* ℤ_Y` of
constant sheaves, the map `CategoryTheory.Adjunction.mapExtCounit` of the adjunction
`f^* ⊣ f_*`. -/
lemma map_counit_cohomologyMap (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) n) :
    Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) n
        (cohomologyMap f _ n x) =
      Ext.precompAddEquiv ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
          (AddCommGrpCat.of (ULift ℤ))) G n
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).mapExtCounit _ G n x) := by
  rw [Sheaf.H.map_apply, cohomologyMap_apply, Ext.precompAddEquiv_apply,
    Adjunction.mapExtCounit_apply]
  exact Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)

/-- **Injectivity of the edge map in degree `1`**: for every morphism of schemes `f : X ⟶ Y`
and every abelian étale sheaf `G` on `X`, the edge map `H¹(Y, f_* G) ⟶ H¹(X, G)` is injective.
This is the first map of the five-term exact sequence of the Leray spectral sequence. -/
theorem injective_edgeMap_one (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Injective fun x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) 1 ↦
      Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) 1
        (cohomologyMap f _ 1 x) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  have := Adjunction.mapExtCounit_one_injective
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) G
  intro x y h
  dsimp only at h
  rw [map_counit_cohomologyMap, map_counit_cohomologyMap] at h
  exact this ((Ext.precompAddEquiv _ G 1).injective h)

/-- **Injectivity of the edge map in degree `2`**: for a morphism of schemes `f : X ⟶ Y` and
an abelian étale sheaf `G` on `X` with `R¹f_* G = 0`, the edge map `H²(Y, f_* G) ⟶ H²(X, G)` is
injective. The vanishing of `R¹f_* G` is phrased as: for some monomorphism `ι : G ⟶ I` into an
injective sheaf, `f_*` maps the cokernel map of `ι` to an epimorphism. -/
theorem injective_edgeMap_two {G I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : G ⟶ I) [Mono ι] [Injective I]
    (hι : Epi (((f)_*[AddCommGrpCat.{u + 1}]).map (cokernel.π ι))) :
    Function.Injective fun x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) 2 ↦
      Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) 2
        (cohomologyMap f _ 2 x) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  have := Adjunction.mapExtCounit_two_injective
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) ι hι
  intro x y h
  dsimp only at h
  rw [map_counit_cohomologyMap, map_counit_cohomologyMap] at h
  exact this ((Ext.precompAddEquiv _ G 2).injective h)

/-- The pullback map on étale cohomology factors through the unit `F ⟶ f_* f^* F` and the edge
map of `f_*`:

```
  H^n(Y, F) ──unit──▶ H^n(Y, f_* f^* F) ──cohomologyMap──▶ H^n(X, f^* f_* f^* F) ──counit──▶
    H^n(X, f^* F)
```
-/
lemma cohomologyMap_eq_map_counit_comp (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H F n) :
    cohomologyMap f F n x =
      Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app
          (((f)^*[AddCommGrpCat.{u + 1}]).obj F)) n
        (cohomologyMap f _ n (Sheaf.H.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F) n x)) := by
  have h := cohomologyMap_map f n
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F) x
  have h' := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).left_triangle_components F
  simp only [Functor.id_obj, Functor.comp_obj] at h h'
  refine Eq.trans ?_ (congrArg (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    f).counit.app (((f)^*[AddCommGrpCat.{u + 1}]).obj F)) n) h).symm
  refine Eq.trans ?_ (Sheaf.H.map_comp_apply ..)
  rw [h']
  exact (Sheaf.H.map_id_apply _).symm

end AlgebraicGeometry.Etale
