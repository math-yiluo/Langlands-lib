/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The supported localization triangle

For complementary immersions `i : Z ⟶ X` and `j : U ⟶ X` the two adjunction maps of the
exceptional formalism assemble into the *supported localization triangle*

`Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ [1]`,

the derived counterpart of the open–closed short exact sequence
`AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`. Its first term is
cohomology-with-supports along `Z`; applied to the closed–open pair `(s, j)` on the affine
line it is what computes the fundamental class of the zero section.

The triangle rests on the *closed-immersion unit*: for a closed immersion `i` the exceptional
adjunction unit `Q ⟶ Ri^! Ri_! Q` is an isomorphism, and `Ri_!` is `Ri_*` because `i` is
proper.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`
- `AlgebraicGeometry.Etale.isZero_upperStar_rightDerivedLowerShriek`: `j^* Ri_! = 0` for an
  open immersion `j` whose range is disjoint from the range of `i`.
- `AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`
- `AlgebraicGeometry.Etale.supportedLocalizationBoundary`: the boundary of the triangle.
- `AlgebraicGeometry.Etale.exists_triangleHom_supportedLocalization`
- `AlgebraicGeometry.Etale.triangleHom_supportedLocalization_ext`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U Z X : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--1`: Closed-immersion unit

For a closed immersion `i : Z ⟶ X` and `Q ∈ D^b_{ctf}(Z, Λ)` the unit

`Q ⟶ Ri^! Ri_! Q`

of the exceptional adjunction `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` is
an isomorphism; since a closed immersion is proper, `Ri_!` is `Ri_*`, so this says that `Ri_*`
is fully faithful on the exceptional side. It is the derived counterpart of the full
faithfulness of `i_*` recorded in `AlgebraicGeometry.Etale.fullyFaithfulLowerStar`.

The unit is invertible for every `Q ∈ D(Z_ét, Λ)` because `Ri_!` is fully
faithful. Write
`Ri_! = D(k_!) ⋙ Rg_*` for the chosen compactification `Z ⟶[k] Z̄ ⟶[g] X` of `i`. As `i` is
proper, `k` has closed range, so `k_! ≅ k_*`
(`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range`); hence
`k_!` preserves K-injective complexes and `Ri_! ≅ R(k_! ⋙ g_*)`. On sheaves `k_! ⋙ g_* ≅ i_*`
(`AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`), which is fully faithful for any
coefficients (`AlgebraicGeometry.Etale.full_lowerStar_of_isClosedImmersion`), and the right
derived functor of a fully faithful functor preserving K-injective complexes is fully faithful
(`CategoryTheory.Functor.full_rightDerivedFunctor`). -/
theorem isIso_rightDerivedUpperShriekAdjunction_unit_app (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i]
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedUpperShriekAdjunction Λ i).unit.app Q) := by
  let c := HasCompactification.compactification i
  -- `k_! ≅ k_*` for the open immersion `k` of the compactification, whose range is closed
  have : IsIso (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) c.i) :=
    Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range (ModuleCat.{u + 1} Λ) c.i
      (c.isClopen_range_openImmersion inferInstance).isClosed
  have : ((c.i)_!open[ModuleCat.{u + 1} Λ]).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso
      (asIso (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) c.i)).symm
  -- on sheaves, `k_! ⋙ g_* ≅ i_*` is fully faithful
  let e : (c.i)_!open[ModuleCat.{u + 1} Λ] ⋙ (c.g)_*[ModuleCat.{u + 1} Λ] ≅ (i)_*[ModuleCat.{u + 1}
      Λ] := asIso (Etale.lowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i)
  have : ((c.i)_!open[ModuleCat.{u + 1} Λ] ⋙ (c.g)_*[ModuleCat.{u + 1} Λ]).Full :=
      Functor.Full.of_iso e.symm
  have : ((c.i)_!open[ModuleCat.{u + 1} Λ] ⋙ (c.g)_*[ModuleCat.{u + 1} Λ]).Faithful :=
      Functor.Faithful.of_iso e.symm
  -- hence so is `Ri_! = D(k_!) ⋙ Rg_* ≅ R(k_! ⋙ g_*)`
  let e' : R(i)_![ModuleCat.{u + 1} Λ] ≅ R((c.i)_!open[ModuleCat.{u + 1} Λ] ⋙ (c.g)_*[ModuleCat.{u +
      1} Λ]) :=
    Functor.isoWhiskerRight ((c.i)_!open[ModuleCat.{u + 1}
        Λ]).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
      (Functor.rightDerivedFunctorCompIso _ _).symm
  have : (R(i)_![ModuleCat.{u + 1} Λ]).Full := Functor.Full.of_iso e'.symm
  have : (R(i)_![ModuleCat.{u + 1} Λ]).Faithful := Functor.Faithful.of_iso e'.symm
  infer_instance

/-- **Étale base change kills what the pullback kills.** Let `g : W ⟶ X` be a morphism and
`j : U ⟶ X` an open immersion, with base change `j' : W ×_X U ⟶ W`. If `D(j'^*) M = 0`, then
`D(j^*) Rg_* M = 0`.

Represent `M` by a K-injective complex `I`. Then `Rg_* M` is `g_* I`, and étale base change for
the pushforward (`AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`) identifies
`j^* g_* I` with `g'_* j'^* I`. The complex `j'^* I` is K-injective, `j'^*` being right adjoint
to the exact `j'_!`, so `g'_* j'^* I` is `Rg'_*` of `D(j'^*) M = 0`. -/
lemma isZero_upperStar_rightDerivedLowerStar {W : Scheme.{u}} (g : W ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    (hM : IsZero (D((pullback.fst g j)^*[A]).obj M)) :
    IsZero (D((j)^*[A]).obj (R((g)_*[A]).obj M)) := by
  obtain ⟨I, _, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have hsq : IsPullback (pullback.snd g j) (pullback.fst g j) j g :=
    (IsPullback.of_hasPullback g j).flip
  have := Etale.isIso_baseChangeMap_flip_of_isPullback A hsq
  have : ((pullback.fst g j)^*[A]).PreservesKInjectiveComplexes :=
    (Etale.openImmersionLowerShriekUpperStarAdjunction A _).preservesKInjectiveComplexes
  let J := (((pullback.fst g j)^*[A]).mapHomologicalComplex _).obj I
  have hJ : IsZero (R(((pullback.snd g j))_*[A]).obj (_root_.DerivedCategory.Q.obj J)) :=
    Functor.isZero_rightDerivedFunctor_obj _
      (hM.of_iso ((D((pullback.fst g j)^*[A]).mapIso e ≪≫
        ((pullback.fst g j)^*[A]).mapDerivedCategoryFactors.app I).symm))
  exact hJ.of_iso
    (D((j)^*[A]).mapIso (R((g)_*[A]).mapIso e ≪≫ ((g)_*[A]).rightDerivedFunctorObjQIso I) ≪≫
      ((j)^*[A]).mapDerivedCategoryFactors.app _ ≪≫
      _root_.DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (asIso (Etale.baseChangeMap A hsq.toCommSq.flip)) _).app I) ≪≫
      (((pullback.snd g j)_*[A]).rightDerivedFunctorObjQIso J).symm)

/-- **`j^* Ri_!` vanishes** for an open immersion `j` whose range is disjoint from the range of
`i`. Write `Ri_! = Rg_* D(i'_!)` for the chosen compactification `Z ⟶[i'] Z̄ ⟶[g] X` of `i`.
By étale base change along `j`
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerivedLowerStar`) it suffices that the
restriction of `D(i'_!) B` to the open `g⁻¹(U)` vanishes, and it does termwise because
`g⁻¹(U)` misses the range of `i'`
(`AlgebraicGeometry.Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek`). -/
lemma isZero_upperStar_rightDerivedLowerShriek (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero (D((j)^*[A]).obj ((R(i)_![A]).obj B)) := by
  let c := HasCompactification.compactification i
  have : IsOpenImmersion c.i := c.isOpenImmersion
  refine isZero_upperStar_rightDerivedLowerStar A c.g j _ ?_
  have hd : Disjoint (Set.range c.i.base) (Set.range (pullback.fst c.g j).base) := by
    rw [Scheme.Pullback.range_fst, Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ hz
    refine Set.disjoint_left.mp hij ⟨z, ?_⟩ hz
    exact (congrArg (fun f ↦ f.base z) c.comm).trans rfl
  refine (Functor.isZero_mapDerivedCategory_obj ((c.i)_!open[A] ⋙ (pullback.fst c.g j)^*[A]) B
    fun n ↦ ?_).of_iso ((((c.i)_!open[A]).mapDerivedCategoryCompIso _).app B)
  exact ((Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek A c.i _ hd
    _).isZero).of_iso ((Etale.upperStarIsoOpenImmersionRestriction A _).app _)

section Localization

/- The closed symmetric preadditive monoidal structure on the coefficient category: it is
what `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction`, the source of the second
map of the triangle, is stated under. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
/-- The *supported localization triangle* of `L` with connecting map `w`:

```
  Ri_! Ri^! L --ε_L--> L --η_L--> Rj_* Lj^* L --w--> (Ri_! Ri^! L)[1]
```

where `ε` is the counit of `Ri_! ⊣ Ri^!` and `η` the unit of `Lj^* ⊣ Rj_*`. -/
noncomputable abbrev supportedLocalizationTriangle (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (w : (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) ⟶
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦(1 : ℤ)⟧) :
    Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  Triangle.mk ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app L) w

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Supported localization

**No maps from the closed side to the open side.** Let `i : Z ⟶ X` be compactifiable and let
`j : U ⟶ X` be an open immersion, with disjoint ranges. Then `Hom((Ri_! B)[n], Rj_* C) = 0` for
all `B ∈ D(Z_ét, A)`, `C ∈ D(U_ét, A)` and `n`. By `j^* ⊣ Rj_*`,

```
  Hom((Ri_! B)[n], Rj_* C) ≅ Hom(j^* ((Ri_! B)[n]), C) ≅ Hom((j^* Ri_! B)[n], C),
```

and `j^* Ri_! = 0` by base change of `Ri_!` along `j`, since the fibre product of the square

```
  Z ×_X U ---> U
     |         | j
     v         v
     Z ---i--> X
```

is empty (`AlgebraicGeometry.Etale.isZero_upperStar_rightDerivedLowerShriek`).

`j` has to be an open immersion: for an arbitrary `j`, base change of `Ri_!` along `j` is
proper base change, which fails for coefficients that are not torsion. -/
theorem subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (i : Z ⟶ X)
    [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (C : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) (n : ℤ) :
    Subsingleton (((R(i)_![A]).obj B)⟦n⟧ ⟶ (R((j)_*[A])).obj C) := by
  have hz : IsZero (D((j)^*[A]).obj (((R(i)_![A]).obj B)⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero (isZero_upperStar_rightDerivedLowerShriek A i j hij B)).of_iso
      ((D((j)^*[A]).commShiftIso n).app _)
  have : Subsingleton (D((j)^*[A]).obj (((R(i)_![A]).obj B)⟦n⟧) ⟶ C) :=
    ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
  exact ((mapDerivedUpperStarLowerStarAdjunction A j).homEquiv _ _).symm.subsingleton

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Supported localization

**The supported localization triangle.** Let `i : Z ⟶ X` be a closed immersion with
complementary open `j : U ⟶ X`. For `L ∈ D(X_ét, A)` the *adjunction maps*

```
  Ri_! Ri^! L --ε_L--> L --η_L--> Rj_* Lj^* L --w--> (Ri_! Ri^! L)[1]
```

— `ε` the counit of `Ri_! ⊣ Ri^!` and `η` the unit of `Lj^* ⊣ Rj_*` — extend to a
distinguished triangle `supportedLocalizationTriangle A i j L w`, and the connecting map `w` is
*unique*. Under the closed-immersion unit `Ri_! Ri^! L` is cohomology with supports along `Z`.

Existence: complete `η_L` to a distinguished triangle `K ⟶ L ⟶ Rj_* Lj^* L ⟶ K[1]`. As `Rj_*`
is fully faithful, `j^* η_L` is invertible and `j^* K = 0`, so the open–closed triangle of `K`
(`AlgebraicGeometry.Etale.exists_distTriang_openClosed`) gives `K ≅ Ri_* i^* K ≅ Ri_! i^* K`.
Since `Ri_!` is fully faithful (`isIso_rightDerivedUpperShriekAdjunction_unit_app`) and
`Hom((Ri_! M)[n], Rj_* Lj^* L) = 0`, the map `Ri_! Ri^! L ⟶ K` through which `ε_L` factors is an
isomorphism (`CategoryTheory.Pretriangulated.exists_distTriang_counit_of_subsingleton`).

Uniqueness is [BBD, 1.1.9] applied to two such triangles and the identity of `L`: as
`Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L) = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`), the morphism of
triangles extending `𝟙 L` (`CategoryTheory.Pretriangulated.exists_triangleHom_of_comp_eq_zero`)
has components `(𝟙, 𝟙, 𝟙)`, so the two connecting maps agree. -/
theorem existsUnique_distTriang_supportedLocalization (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃! w, supportedLocalizationTriangle Λ i j L w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ : ∃ w, supportedLocalizationTriangle Λ i j L w ∈ distTriang _ := by
    obtain ⟨K, a, δ, hT⟩ :=
      distinguished_cocone_triangle₁ ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          j).unit.app L)
    -- `j^*` kills the fibre `K` of `η_L`, since `Rj_*` is fully faithful
    have hK : IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj K) := by
      have : IsIso (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit :=
        (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1}
            Λ) j)
          (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              j)).isIso_unit_iff_isIso_counit.1
          inferInstance
      have hff := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          j).fullyFaithfulROfIsIsoCounit
      have := hff.full
      have := hff.faithful
      have : IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit :=
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            j).counit_isIso_of_R_fully_faithful
      have h := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          j).left_triangle_components L
      have : IsIso (L((j)^*[ModuleCat.{u + 1} Λ]).map ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app L)) := by
        rw [IsIso.eq_inv_of_inv_hom_id h]
        infer_instance
      exact (Triangle.isZero₁_iff_isIso₂ _ (D((j)^*[ModuleCat.{u + 1} Λ]).map_distinguished _ hT)).2
        ((NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j)
            _).1 this)
    -- so `K` is supported on `Z`, by the open–closed triangle of `K`
    have hKi : (R(i)_![ModuleCat.{u + 1} Λ]).essImage K := by
      obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij K
      have : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K) :=
        (Triangle.isZero₁_iff_isIso₂ _ hw).1 (D((j)_!open[ModuleCat.{u + 1} Λ]).map_isZero hK)
      exact ⟨D((i)^*[ModuleCat.{u + 1} Λ]).obj K, ⟨(rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} Λ) i).app _ ≪≫
        (asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K)).symm⟩⟩
    have := isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i
    have : IsIso (rightDerivedUpperShriekAdjunction Λ i).unit := NatIso.isIso_of_isIso_app _
    exact exists_distTriang_counit_of_subsingleton (rightDerivedUpperShriekAdjunction Λ i)
      (rightDerivedUpperShriekAdjunction Λ i).fullyFaithfulLOfIsIsoUnit hT
      (fun M n ↦ subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (ModuleCat.{u
          + 1} Λ) i j
        (hij ▸ disjoint_compl_left) M _ n) hKi
  refine ⟨w, hw, fun w' hw' ↦ ?_⟩
  have : Subsingleton ((supportedLocalizationTriangle Λ i j L w').obj₁⟦(1 : ℤ)⟧ ⟶
      (supportedLocalizationTriangle Λ i j L w).obj₃) :=
    subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (ModuleCat.{u + 1} Λ) i j
      (hij ▸ disjoint_compl_left) _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw' hw (𝟙 _)
    (by rw [Category.id_comp]; exact comp_distTriang_mor_zero₁₂ _ hw')
  have h₁ : τ.hom₁ = 𝟙 _ := Triangle.cancel_mor₁_of_subsingleton hw
    (by rw [← τ.comm₁, hτ, Category.comp_id, Category.id_comp]; rfl)
  have h₃ : τ.hom₃ = 𝟙 _ := Triangle.cancel_mor₂_of_subsingleton hw'
    (by rw [τ.comm₂, hτ, Category.id_comp, Category.comp_id]; rfl)
  have h := τ.comm₃
  rw [h₁, h₃] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  exact h

/-- The *boundary* `δ : Rj_* Lj^* L ⟶ (Ri_! Ri^! L)[1]` of the supported localization triangle
of `L`: the unique connecting map making `supportedLocalizationTriangle A i j L δ`
distinguished.

It is *defined* as `Classical.choose` of the existence half of
`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`; uniqueness is what makes
the choice canonical. The supported term is
`Ri_!`, which for a closed immersion is `Ri_*`. -/
noncomputable def supportedLocalizationBoundary (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) ⟶
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦(1 : ℤ)⟧ :=
  (existsUnique_distTriang_supportedLocalization Λ i j hij L).exists.choose

/-- The supported localization triangle with its boundary
`AlgebraicGeometry.Etale.supportedLocalizationBoundary` is distinguished. -/
theorem supportedLocalizationTriangle_mem_distTriang (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L) ∈
      distTriang _ :=
  (existsUnique_distTriang_supportedLocalization Λ i j hij L).exists.choose_spec

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Supported localization

**Naturality of the supported localization triangle.** Let `i : Z ⟶ X` be compactifiable and
`j : U ⟶ X` an open immersion, with disjoint images. For `φ : L ⟶ L'` and distinguished
supported localization triangles of `L` and `L'`, the triple `(Ri_! Ri^! φ, φ, Rj_* Lj^* φ)`
is a morphism of triangles:

```
  Ri_! Ri^! L  --ε_L-->  L  --η_L-->  Rj_* Lj^* L  --w-->  (Ri_! Ri^! L)[1]
       |                 |                |                     |
   Ri_!Ri^!φ             φ           Rj_*Lj^*φ           (Ri_!Ri^!φ)[1]
       v                 v                v                     v
  Ri_! Ri^! L' --ε_L'--> L' --η_L'--> Rj_* Lj^* L' --w'-->  (Ri_! Ri^! L')[1]
```

The middle component extends to a morphism of triangles
(`CategoryTheory.Pretriangulated.exists_triangleHom_of_comp_eq_zero`) because
`ε_L ≫ φ ≫ η_L' = Ri_! Ri^! φ ≫ ε_L' ≫ η_L' = 0`; its outer components are the ones above
because `Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L') = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`). -/
theorem exists_triangleHom_supportedLocalization (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Disjoint (Set.range i.base) (Set.range j.base))
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : L ⟶ L')
    {w : (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) ⟶
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦(1 : ℤ)⟧}
    {w' : (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L') ⟶
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L'))⟦(1 : ℤ)⟧}
    (hw : supportedLocalizationTriangle Λ i j L w ∈ distTriang _)
    (hw' : supportedLocalizationTriangle Λ i j L' w' ∈ distTriang _) :
    ∃ τ : supportedLocalizationTriangle Λ i j L w ⟶ supportedLocalizationTriangle Λ i j L' w',
      τ.hom₁ = (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map φ) ∧ τ.hom₂ = φ ∧
        τ.hom₃ = (R((j)_*[ModuleCat.{u + 1} Λ])).map ((L((j)^*[ModuleCat.{u + 1} Λ])).map φ) := by
  have : Subsingleton ((supportedLocalizationTriangle Λ i j L w).obj₁⟦(1 : ℤ)⟧ ⟶
      (supportedLocalizationTriangle Λ i j L' w').obj₃) :=
    subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (ModuleCat.{u + 1} Λ) i j
        hij _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw hw' φ (by
    rw [← Category.assoc]
    erw [← (rightDerivedUpperShriekAdjunction Λ i).counit_naturality]
    rw [Category.assoc]
    erw [comp_distTriang_mor_zero₁₂ _ hw']
    rw [comp_zero])
  refine ⟨τ, Triangle.cancel_mor₁_of_subsingleton hw' ?_, hτ,
    Triangle.cancel_mor₂_of_subsingleton hw ?_⟩
  · rw [← τ.comm₁, hτ]
    exact ((rightDerivedUpperShriekAdjunction Λ i).counit_naturality φ).symm
  · rw [τ.comm₂, hτ]
    exact ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit_naturality φ).symm

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Supported localization

**A morphism of supported localization triangles is determined by its middle
component.** Let
`i : Z ⟶ X` be compactifiable and `j : U ⟶ X` an open immersion, with disjoint images. Two
morphisms between distinguished supported localization triangles with the same middle component
are equal (`CategoryTheory.Pretriangulated.triangleHom_ext_of_subsingleton`), because
`Hom((Ri_! Ri^! L)[1], Rj_* Lj^* L') = 0`
(`subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`) [BBD, 1.1.9]. -/
theorem triangleHom_supportedLocalization_ext (i : Z ⟶ X) [HasCompactification i]
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Disjoint (Set.range i.base) (Set.range j.base))
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {w : (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) ⟶
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦(1 : ℤ)⟧}
    {w' : (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L') ⟶
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L'))⟦(1 : ℤ)⟧}
    (hw : supportedLocalizationTriangle Λ i j L w ∈ distTriang _)
    (hw' : supportedLocalizationTriangle Λ i j L' w' ∈ distTriang _)
    {τ τ' : supportedLocalizationTriangle Λ i j L w ⟶ supportedLocalizationTriangle Λ i j L' w'}
    (h : τ.hom₂ = τ'.hom₂) : τ = τ' :=
  have : Subsingleton ((supportedLocalizationTriangle Λ i j L w).obj₁⟦(1 : ℤ)⟧ ⟶
      (supportedLocalizationTriangle Λ i j L' w').obj₃) :=
    subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar (ModuleCat.{u + 1} Λ) i j
        hij _ _ 1
  triangleHom_ext_of_subsingleton hw hw' h

end Localization

end Etale

end AlgebraicGeometry
