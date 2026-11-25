/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Base change of the supported localization triangle

Let `i : Z ⟶ X` be a closed immersion with open complement `j : V ⟶ X`, and let `e : U ⟶ X` be a
morphism, with base changes `i' : Z' ⟶ U` and `j' : V' ⟶ U`. The derived pullback `Le^*` carries
the supported localization triangle `Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ [1]` of `L` to a
distinguished triangle on `U`, which maps to the supported localization triangle of `Le^* L`:
on the first term by the restriction of supports
(`AlgebraicGeometry.Etale.supportedRestriction`), on the last term by the derived base change
map `Ex_* : Le^* Rj_* ⟶ Rj'_* Le₁^*`. The compatibility with the connecting maps is the base
change of the boundary `AlgebraicGeometry.Etale.supportedLocalizationBoundary`.

## Main statements

- `AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X U Z Z' V V' : Scheme.{u}}

/-- **Base change of the supported localization boundary.** Let `i : Z ⟶ X` be a closed
immersion with open complement `j : V ⟶ X`, `e : U ⟶ X` a morphism, `i' : Z' ⟶ U` the base
change of `i` with open complement `j' : V' ⟶ U`, and `e₁ : V' ⟶ V` with `e₁ ≫ j = j' ≫ e`. For
`L ∈ D(X_ét)` and an identification `τ : Le^* L ≅ L'`, the boundaries `δ_L` and `δ_{L'}` of the
supported localization triangles are compatible with the restriction of supports
`ψ = AlgebraicGeometry.Etale.supportedRestriction` and the derived base change map `Ex_*`:

```
  Le^* Rj_* Lj^* L ──Le^* δ_L──▶ Le^* ((Ri_! Ri^! L)[1]) ≅ (Le^* Ri_! Ri^! L)[1]
        │                                                      │
  Ex_*, τ                                                    ψ[1]
        ▼                                                      ▼
  Rj'_* Lj'^* L' ─────────────δ_{L'}──────────────▶ (Ri'_! Ri'^! L')[1]
```

The pulled back triangle is distinguished and its first term is supported on `Z'`, so the middle
map `τ` extends uniquely to a morphism of triangles towards the supported localization triangle
of `L'` [BBD, 1.1.9]; its outer components are `ψ` and the base change map, both characterized
by the commutation of the adjacent squares. -/
theorem supportedLocalizationBoundary_baseChange (e : U ⟶ X) (i : Z ⟶ X) (j : V ⟶ X)
    (i' : Z' ⟶ U) (j' : V' ⟶ U) (g : Z' ⟶ Z) (e₁ : V' ⟶ V)
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (hg : IsPullback g i' i e) (sq : CommSq e₁ j' j e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedLocalizationBoundary Λ i j hij L) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
          (supportedRestriction Λ e i i' g hg L L' τ)⟦(1 : ℤ)⟧' =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app _ ≫
        (R((j')_*[ModuleCat.{u + 1} Λ])).map ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
            sq).inv.app L ≫
          (L((j')^*[ModuleCat.{u + 1} Λ])).map τ.hom) ≫
          supportedLocalizationBoundary Λ i' j' hij' L' := by
  set T₁ := (L((e)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
    (supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L))
  have hT₁ : T₁ ∈ distTriang _ :=
    (L((e)^*[ModuleCat.{u + 1} Λ])).map_distinguished _
        (supportedLocalizationTriangle_mem_distTriang Λ i j hij L)
  have hT₂ := supportedLocalizationTriangle_mem_distTriang Λ i' j' hij' L'
  -- the pulled back supported term vanishes on `V'`
  have hz : IsZero ((L((j')^*[ModuleCat.{u + 1} Λ])).obj T₁.obj₁) :=
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i j
      (by rw [hij]; exact disjoint_compl_left) (j' ≫ e)
      (by rintro _ ⟨x, rfl⟩; exact ⟨e₁ x, by rw [← sq.w]; simp⟩) _).of_iso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j' e).app _).symm
  have hz₁ (n : ℤ) : IsZero ((L((j')^*[ModuleCat.{u + 1} Λ])).obj (T₁.obj₁⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero hz).of_iso (((L((j')^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app
        _)
  have : Subsingleton (T₁.obj₁⟦(1 : ℤ)⟧ ⟶ (supportedLocalizationTriangle Λ i' j' L'
      (supportedLocalizationBoundary Λ i' j' hij' L')).obj₃) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ) j' (hz₁ 1) _
  -- the middle component `τ` extends to a morphism of triangles
  obtain ⟨φ, hφ⟩ := exists_triangleHom_of_comp_eq_zero hT₁ hT₂ τ.hom
    (@Subsingleton.elim _ (subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ) j'
        hz _) _ _)
  -- its first component is the restriction of supports
  have h₁ : φ.hom₁ = supportedRestriction Λ e i i' g hg L L' τ :=
    (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).unique
      (by have h := φ.comm₁; rw [hφ] at h; exact h.symm)
      (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec
  -- its last component is the base change map
  have h₃ : φ.hom₃ = (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app _ ≫
      (R((j')_*[ModuleCat.{u + 1} Λ])).map ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
          sq).inv.app L ≫
        (L((j')^*[ModuleCat.{u + 1} Λ])).map τ.hom) := by
    refine Triangle.cancel_mor₂_of_subsingleton hT₁ ?_
    rw [φ.comm₂, hφ]
    change τ.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.app L' =
      (L((e)^*[ModuleCat.{u + 1} Λ])).map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1}
          Λ) j).unit.app L) ≫ _
    erw [map_unit_derivedBaseChangeMap_app_assoc]
    simp only [Functor.id_obj, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    exact ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.naturality τ.hom)
  have h := φ.comm₃
  rw [h₁, h₃] at h
  change ((L((e)^*[ModuleCat.{u + 1} Λ])).map _ ≫ _) ≫ _ = _ at h
  simp only [Category.assoc] at h
  exact h

variable {V₀ V₀' U₀ U₀' : Scheme.{u}} {e₁ : V₀' ⟶ V₀} {j₀' : V₀' ⟶ U₀'} {j₀ : V₀ ⟶ U₀}
  {e₀ : U₀' ⟶ U₀}

omit [HasSmallSiteSheafify A] in
/-- **Base change of the adjoint of a degree-one class on an open.** For a commutative square
`e₁ ≫ j = j' ≫ e` with `j`, `j'` arbitrary, the pullback along `e` of the adjoint
`K ⟶ Rj_* (M[1]) ≅ (Rj_* M)[1]` of a class `y : Lj^* K ⟶ M[1]`, followed by the derived base
change map `Ex_*`, is the adjoint of the pulled back class: this combines the compatibility of
`Ex_*` with the units, its naturality and its compatibility with the shifts.

```
Le^* K ──Le^*(adjoint of y)──▶ Le^* ((Rj_* M)[1]) ──≅──▶ (Le^* Rj_* M)[1]
   │                                                          │
 η │                                                          │ Ex_*[1]
   ▼                                                          ▼
Rj'_* Lj'^* Le^* K ──Rj'_*(≅ ≫ Le₁^* y ≫ ≅)──▶ Rj'_* ((Le₁^* M)[1]) ──≅──▶ (Rj'_* Le₁^* M)[1]
```
-/
lemma leftDerivedUpperStar_map_adjoint_comp_derivedBaseChangeMap (sq : CommSq e₁ j₀' j₀ e₀)
    (K : DerivedCategory (Sheaf U₀.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf V₀.smallEtaleTopology A))
    (y : (L((j₀)^*[A])).obj K ⟶ M⟦(1 : ℤ)⟧) :
    (L((e₀)^*[A])).map ((derivedUpperStarLowerStarAdjunction A j₀).unit.app K ≫
        (R((j₀)_*[A])).map y ≫ ((R((j₀)_*[A])).commShiftIso (1 : ℤ)).hom.app M) ≫
        ((L((e₀)^*[A])).commShiftIso (1 : ℤ)).hom.app _ ≫
          ((derivedBaseChangeMap A sq).app M)⟦(1 : ℤ)⟧' =
      (derivedUpperStarLowerStarAdjunction A j₀').unit.app ((L((e₀)^*[A])).obj K) ≫
        (R((j₀')_*[A])).map ((derivedSquareUpperStarIso A sq).hom.app K ≫
          (L((e₁)^*[A])).map y ≫ ((L((e₁)^*[A])).commShiftIso (1 : ℤ)).hom.app M) ≫
          ((R((j₀')_*[A])).commShiftIso (1 : ℤ)).hom.app _ := by
  have h₁ := NatTrans.shift_app_comm (derivedBaseChangeMap A sq) (1 : ℤ) M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at h₁
  have h₂ := (derivedBaseChangeMap A sq).naturality y
  have h₃ := map_unit_derivedBaseChangeMap_app A sq K
  simp only [Functor.map_comp, Category.assoc]
  rw [h₁]
  erw [reassoc_of% h₂]
  rw [reassoc_of% h₃]

omit [HasSmallSiteSheafify A] in
/-- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_adjoint_comp_derivedBaseChangeMap`,
precomposed with a map `σ : K' ⟶ Le^* K` and followed by a map `ρ : Le₁^* M ⟶ N`. -/
lemma comp_leftDerivedUpperStar_map_adjoint_comp_derivedBaseChangeMap
    (sq : CommSq e₁ j₀' j₀ e₀)
    (K : DerivedCategory (Sheaf U₀.smallEtaleTopology A))
    (K' : DerivedCategory (Sheaf U₀'.smallEtaleTopology A)) (σ : K' ⟶ (L((e₀)^*[A])).obj K)
    (M : DerivedCategory (Sheaf V₀.smallEtaleTopology A))
    (y : (L((j₀)^*[A])).obj K ⟶ M⟦(1 : ℤ)⟧)
    (N : DerivedCategory (Sheaf V₀'.smallEtaleTopology A)) (ρ : (L((e₁)^*[A])).obj M ⟶ N) :
    σ ≫ (L((e₀)^*[A])).map ((derivedUpperStarLowerStarAdjunction A j₀).unit.app K ≫
        (R((j₀)_*[A])).map y ≫ ((R((j₀)_*[A])).commShiftIso (1 : ℤ)).hom.app M) ≫
        ((L((e₀)^*[A])).commShiftIso (1 : ℤ)).hom.app _ ≫
          ((derivedBaseChangeMap A sq).app M ≫ (R((j₀')_*[A])).map ρ)⟦(1 : ℤ)⟧' =
      (derivedUpperStarLowerStarAdjunction A j₀').unit.app K' ≫
        (R((j₀')_*[A])).map ((L((j₀')^*[A])).map σ ≫
          (derivedSquareUpperStarIso A sq).hom.app K ≫ (L((e₁)^*[A])).map y ≫
            ((L((e₁)^*[A])).commShiftIso (1 : ℤ)).hom.app M ≫ ρ⟦(1 : ℤ)⟧') ≫
          ((R((j₀')_*[A])).commShiftIso (1 : ℤ)).hom.app N := by
  rw [Functor.map_comp (shiftFunctor (DerivedCategory (Sheaf U₀'.smallEtaleTopology A)) (1 : ℤ)),
    reassoc_of% leftDerivedUpperStar_map_adjoint_comp_derivedBaseChangeMap,
    ← Functor.commShiftIso_hom_naturality, ← Adjunction.unit_naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]

section Restriction

variable {Z₀ Z₀' X₀ U₁ : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- The restriction of supports factors the pullback of the counit through the counit:

```
Le^* (Ri_! Ri^! L) ──ψ──▶ Ri'_! Ri'^! L'
        │                       │
 Le^* ε │                       │ ε'
        ▼                       ▼
     Le^* L ────────τ────────▶ L'
```
-/
@[reassoc]
lemma supportedRestriction_comp_counit (e : U₁ ⟶ X₀) (i : Z₀ ⟶ X₀) (i' : Z₀' ⟶ U₁)
    [IsClosedImmersion i] [IsClosedImmersion i']
 (g : Z₀' ⟶ Z₀) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    supportedRestriction Λ e i i' g hg L L' τ ≫
        (rightDerivedUpperShriekAdjunction Λ i').counit.app L' =
      (L((e)^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L) ≫
          τ.hom :=
  (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec

omit [HasSmallSiteSheafify A] in
/-- The pullback along `e` of an object supported on `Z` is supported on the base change `Z'`:
it vanishes on the open complement of `Z'`. -/
lemma isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_rightDerivedLowerShriek
    (e : U₁ ⟶ X₀) (i : Z₀ ⟶ X₀) (i' : Z₀' ⟶ U₁) [IsClosedImmersion i] [IsClosedImmersion i']
    (g : Z₀' ⟶ Z₀) (hg : IsPullback g i' i e)
    (B : DerivedCategory (Sheaf Z₀.smallEtaleTopology A)) :
    IsZero ((L((i'.openComplement.ι)^*[A])).obj ((L((e)^*[A])).obj ((R(i)_![A]).obj B))) := by
  refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i
    i.openComplement.ι (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left)
    (i'.openComplement.ι ≫ e) ?_ _).of_iso
      ((leftDerivedUpperStarComp A i'.openComplement.ι e).app _).symm
  rw [← compl_compl (Set.range i.openComplement.ι), ← i.range_eq_compl_range_openComplement_ι,
    Set.subset_compl_iff_disjoint_left, Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  apply x.2
  rw [Scheme.range_snd_of_isPullback hg]
  exact ⟨z, hx.symm⟩

/-- **Restriction of supports commutes with shifts.** Restricting the class
`γ : K ⟶ Ri_! Ri^! (L[n])` read from a degree-`n` class `γ : K ⟶ (Ri_! Ri^! L)[n]`
(`AlgebraicGeometry.Etale.shiftSupportedClass`) along `e` is the same as restricting `γ` in
degree `n` and reading the result as a class with coefficients `L'[n]`. -/
lemma restrictSupportedClass_shiftSupportedClass (e : U₁ ⟶ X₀) (i : Z₀ ⟶ X₀) (i' : Z₀' ⟶ U₁)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z₀' ⟶ Z₀) (hg : IsPullback g i' i e)
    {K L : DerivedCategory (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf U₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') (n : ℤ)
    (γ : K ⟶ ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦n⟧) :
    restrictSupportedClass Λ e i i' g hg σ
        (((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app L ≪≫ (shiftFunctor _ n).mapIso τ)
        (shiftSupportedClass Λ i n γ) =
      shiftSupportedClass Λ i' n (σ ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map γ ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app _ ≫
          (supportedRestriction Λ e i i' g hg L L' τ)⟦n⟧') := by
  have := (rightDerivedUpperShriekAdjunction Λ i).commShift_of_leftAdjoint ℤ
  have := (rightDerivedUpperShriekAdjunction Λ i').commShift_of_leftAdjoint ℤ
  have hz : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((L((e)^*[ModuleCat.{u +
      1} Λ])).obj
      (((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦n⟧))) := by
    refine ((shiftFunctor _ n).map_isZero
      (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) e i i' g hg ((R(i)^![Λ]).obj L))).of_iso ?_
    exact (L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).mapIso (((L((e)^*[ModuleCat.{u + 1}
        Λ])).commShiftIso n).app _) ≪≫
      ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app _
  have key : (L((e)^*[ModuleCat.{u + 1} Λ])).map (((R(i)_![ModuleCat.{u + 1} Λ]).commShiftIso
      n).inv.app _ ≫
        (R(i)_![ModuleCat.{u + 1} Λ]).map (((R(i)^![Λ]).commShiftIso n).inv.app L)) ≫
        supportedRestriction Λ e i i' g hg (L⟦n⟧) (L'⟦n⟧)
          (((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app L ≪≫ (shiftFunctor _ n).mapIso τ) =
      ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app _ ≫
        (supportedRestriction Λ e i i' g hg L L' τ)⟦n⟧' ≫
          ((R(i')_![ModuleCat.{u + 1} Λ]).commShiftIso n).inv.app _ ≫
            (R(i')_![ModuleCat.{u + 1} Λ]).map (((R(i')^![Λ]).commShiftIso n).inv.app L') := by
    refine (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
      i'.range_eq_compl_range_openComplement_ι hz _).unique ?_ rfl
    have h₁ := (rightDerivedUpperShriekAdjunction Λ i).commShiftIso_inv_app_counit_app ℤ n L
    have h₂ := (rightDerivedUpperShriekAdjunction Λ i').commShiftIso_inv_app_counit_app ℤ n L'
    simp only [Functor.commShiftIso_comp_inv_app, Category.assoc] at h₁ h₂
    rw [Category.assoc, supportedRestriction_comp_counit, ← Functor.map_comp_assoc,
      Category.assoc, h₁, Category.assoc, Category.assoc, Category.assoc, h₂,
      ← Functor.map_comp, supportedRestriction_comp_counit, Functor.map_comp,
      ← Functor.commShiftIso_hom_naturality_assoc]
    rfl
  simp only [Functor.map_comp, Category.assoc] at key
  simp only [restrictSupportedClass, shiftSupportedClass, Functor.map_comp, Category.assoc, key]

end Restriction

end Etale

end AlgebraicGeometry
