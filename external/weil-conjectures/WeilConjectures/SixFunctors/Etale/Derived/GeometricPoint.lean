/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Morphisms are determined at geometric points

A morphism of étale sheaves is determined by its fibres at the geometric points, and the fibre
of `φ` at a geometric point `x : Spec Ω ⟶ X` is the global section of the pullback `x^* φ`. So
two morphisms of étale sheaves whose pullbacks along all geometric points agree are equal.

The same holds in the derived category `D(X_ét, Λ)` for morphisms between sheaves placed in a
single degree: the single-degree functor is fully faithful and commutes with the exact pullback
along a geometric point. This is the *stalk criterion for the equality of sheaf sections*
(`def-weil-derived-cohomology-sheaves`) in the form used by the uniqueness of the orientation
of the zero section (`prop-pur-affine-line-orientation-uniqueness`).

## Main statements

- `AlgebraicGeometry.Etale.sheafHom_ext_of_upperStar_map_eq`
- `AlgebraicGeometry.Etale.singleFunctor_hom_ext_of_leftDerivedUpperStar_map_eq`
- `AlgebraicGeometry.Etale.hom_ext_of_leftDerivedUpperStar_map_eq`
- `AlgebraicGeometry.Etale.isZero_homology_constantComplex`,
  `AlgebraicGeometry.Etale.homologyZeroConstantComplexIso`: the cohomology sheaves of `Λ_X`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Two morphisms of étale sheaves of `Λ`-modules on `X` whose pullbacks along every geometric
point `x : Spec Ω ⟶ X` agree are equal: the fibre of a morphism at the geometric point `x` is
the fibre of its pullback `x^*` at the identity point of `Spec Ω`
(`AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`), and the geometric points jointly
detect equality of morphisms
(`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale`). -/
theorem sheafHom_ext_of_upperStar_map_eq {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {φ ψ : F ⟶ G}
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      ((x)^*[ModuleCat.{u + 1} Λ]).map φ = ((x)^*[ModuleCat.{u + 1} Λ]).map ψ) :
    φ = ψ := by
  refine ((isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyFaithful
    (ModuleCat.{u + 1} Λ)).map_injective ?_
  rintro ⟨-, ⟨s⟩⟩
  have e := upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) (X.algClosurePoint s) (𝟙 _)
  rw [Category.id_comp] at e
  dsimp only [uliftPointSmallEtale]
  rw [← NatIso.naturality_1 e φ, ← NatIso.naturality_1 e ψ, Functor.comp_map, Functor.comp_map,
    h _ (X.algClosurePoint s)]

/-- Two morphisms `F[0] ⟶ G[0]` in `D(X_ét, Λ)` between sheaves placed in degree zero whose
derived pullbacks along every geometric point `x : Spec Ω ⟶ X` agree are equal. The
single-degree functor is fully faithful, and the derived pullback of a sheaf in degree zero is
its pullback in degree zero, so this is `AlgebraicGeometry.Etale.sheafHom_ext_of_upperStar_map_eq`.
-/
theorem singleFunctor_hom_ext_of_leftDerivedUpperStar_map_eq
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {φ ψ : (_root_.DerivedCategory.singleFunctor _ 0).obj F ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj G}
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      (L((x)^*[ModuleCat.{u + 1} Λ])).map φ = (L((x)^*[ModuleCat.{u + 1} Λ])).map ψ) :
    φ = ψ := by
  obtain ⟨a, rfl⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective φ
  obtain ⟨b, rfl⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective ψ
  congr 1
  refine sheafHom_ext_of_upperStar_map_eq fun Ω _ _ x ↦
    (_root_.DerivedCategory.singleFunctor _ 0).map_injective ?_
  let e := Functor.isoWhiskerLeft (_root_.DerivedCategory.singleFunctor _ 0)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) x) ≪≫
    ((x)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0
  have ha := NatIso.naturality_2 e a
  have hb := NatIso.naturality_2 e b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_epi (e.hom.app F), ← cancel_mono (e.inv.app G), Category.assoc, Category.assoc,
    ha, hb, h Ω x]

/-- Two morphisms `K ⟶ L` in `D(X_ét, Λ)` between objects isomorphic to sheaves placed in degree
zero whose derived pullbacks along every geometric point `x : Spec Ω ⟶ X` agree are equal. -/
theorem hom_ext_of_leftDerivedUpperStar_map_eq
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (eK : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eL : L ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G) {φ ψ : K ⟶ L}
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      (L((x)^*[ModuleCat.{u + 1} Λ])).map φ = (L((x)^*[ModuleCat.{u + 1} Λ])).map ψ) :
    φ = ψ := by
  have : eK.inv ≫ φ ≫ eL.hom = eK.inv ≫ ψ ≫ eL.hom :=
    singleFunctor_hom_ext_of_leftDerivedUpperStar_map_eq fun Ω _ _ x ↦ by
      simp only [Functor.map_comp, h Ω x]
  simpa using this

variable (Λ X) in
/-- The constant complex `Λ_X` is the unit sheaf placed in degree zero. -/
noncomputable def constantComplexIsoSingleFunctor :
    constantComplex Λ X ≅
      (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        0).obj (𝟙_ _) :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).symm

/-- Two morphisms `Λ_X ⟶ L` in `D(X_ét, Λ)`, out of the constant complex into an object
isomorphic to the constant complex, whose derived pullbacks along every geometric point
`x : Spec Ω ⟶ X` agree are equal. -/
theorem constantComplex_hom_ext_of_leftDerivedUpperStar_map_eq
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : L ≅ constantComplex Λ X) {φ ψ : constantComplex Λ X ⟶ L}
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      (L((x)^*[ModuleCat.{u + 1} Λ])).map φ = (L((x)^*[ModuleCat.{u + 1} Λ])).map ψ) :
    φ = ψ :=
  hom_ext_of_leftDerivedUpperStar_map_eq (constantComplexIsoSingleFunctor Λ X)
    (e ≪≫ constantComplexIsoSingleFunctor Λ X) h

variable (Λ X) in
/-- The cohomology sheaves of the constant complex `Λ_X` vanish outside degree zero. -/
lemma isZero_homology_constantComplex (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj (constantComplex Λ X)) :=
  (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (constantComplexIsoSingleFunctor Λ X ≪≫
        (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
      (_root_.DerivedCategory.homologyFunctorFactors _ n).app _)

variable (Λ X) in
/-- The zeroth cohomology sheaf of the constant complex `Λ_X` is the constant sheaf `Λ`. -/
noncomputable def homologyZeroConstantComplexIso :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ X) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).mapIso (constantComplexIsoSingleFunctor Λ X) ≪≫
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _

end Etale

end AlgebraicGeometry
