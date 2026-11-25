/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Vanishing

/-!
# The derived functors `Lg^*K ⊗ᴸ Lg^*M` and `Lg^*(K ⊗ᴸ M)`

- `AlgebraicGeometry.ProEtale.derivedTensorLeftDerivedUpperStar g` and
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarDerivedTensor g`: the bifunctors
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, with their counits.
- `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar` and
  `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor`: they are
  total left derived functors.

See `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal` for an
overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
section

open DerivedCategory Functor.LaxMonoidal

/-- The bifunctor `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M`, of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`. -/
noncomputable abbrev derivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) :=
  (((Functor.whiskeringLeft₂ _).obj L((g)^*[A])).obj L((g)^*[A])).obj (-⊗ᴸ-(Z)[A])

/-- The bifunctor `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`. -/
noncomputable abbrev leftDerivedUpperStarDerivedTensor :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) :=
  (Functor.postcompose₂.obj L((g)^*[A])).obj (-⊗ᴸ-(Y)[A])

/-- The counit exhibiting `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` as the total left derived functor of
`(A, B) ↦ g^*A ⊗ g^*B`. On `K, M` in `K(Y_proét)` it is the composite
```
 Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M) --(counit ⊗ᴸ 1)--> Qh(g^*K) ⊗ᴸ Lg^*(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(g^*K) ⊗ᴸ Qh(g^*M) --(μ Qh)--> Qh(g^*K ⊗ g^*M)
```
of the counits of `Lg^*` on both factors and the lax monoidal structure of
`Qh : K(Z_proét) ⥤ D(Z_proét)`. -/
noncomputable def derivedTensorLeftDerivedUpperStarCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf (Scheme.ProEt.topology Y) A))).obj Qh).obj
        (derivedTensorLeftDerivedUpperStar A g) ⟶
      (((Functor.whiskeringLeft₂ _).obj ((g)^*[A].mapHomotopyCategory (.up ℤ))).obj
        ((g)^*[A].mapHomotopyCategory (.up ℤ))).obj
          ((Functor.postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((Functor.whiskeringLeft₂ _).map (g)^*[A].leftDerivedFunctorCounit).app
      (Qh ⋙ L((g)^*[A]))).app (-⊗ᴸ-(Z)[A]) ≫
    (((Functor.whiskeringLeft₂ _).obj ((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      (g)^*[A].leftDerivedFunctorCounit).app (-⊗ᴸ-(Z)[A]) ≫
    (((Functor.whiskeringLeft₂ _).obj ((g)^*[A].mapHomotopyCategory (.up ℤ))).obj
        ((g)^*[A].mapHomotopyCategory (.up ℤ))).map (μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ Lg^*(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ g^*(A ⊗ B)`. On `K, M` in `K(Y_proét)` it is the composite
```
 Lg^*(Qh K ⊗ᴸ Qh M) --(Lg^*(μ Qh))--> Lg^*(Qh (K ⊗ M)) --(counit)--> Qh(g^*(K ⊗ M))
```
of `Lg^*` applied to the lax monoidal structure of `Qh : K(Y_proét) ⥤ D(Y_proét)` and the counit
of `Lg^*`. -/
noncomputable def leftDerivedUpperStarDerivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf (Scheme.ProEt.topology Y) A))).obj Qh).obj
        (leftDerivedUpperStarDerivedTensor A g) ⟶
      (Functor.postcompose₂.obj ((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.obj L((g)^*[A])).map (μNatTrans Qh) ≫
    (Functor.postcompose₂.map (g)^*[A].leftDerivedFunctorCounit).app (curriedTensor _)

/-- `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`
from `K(Y_proét) × K(Y_proét)` to `D(Z_proét)`. It is computed on pairs `(K, M)` with `K` K-flat and
`g^*M` K-flat. -/
theorem isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
    [ProEtale.UpperStarPreservesFlat A] :
    (derivedTensorLeftDerivedUpperStar A g).IsLeftDerivedFunctor₂
      (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    (((g)^*[A].mapHomotopyCategory _).obj X₁.obj) _ X₂.property
  simp only [derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)

/-- `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`
from `K(Y_proét) × K(Y_proét)` to `D(Z_proét)`. It is computed on pairs of K-flat complexes. -/
theorem isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor :
    (leftDerivedUpperStarDerivedTensor A g).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarDerivedTensorCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  simp only [leftDerivedUpperStarDerivedTensorCounit, NatTrans.comp_app]
  -- Instance search times out on `IsIso (L(g^*).map _)`, since the objects in the goal are
  -- only defeq to `X₁.obj` and `X₂.obj`; so the morphism is given explicitly.
  exact IsIso.comp_isIso'
    (Functor.map_isIso L((g)^*[A]) (((μNatTrans Qh).app X₁.obj).app X₂.obj)) inferInstance

end

end ProEtale

end AlgebraicGeometry
