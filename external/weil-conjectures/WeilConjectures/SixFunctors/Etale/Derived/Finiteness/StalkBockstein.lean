/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BocksteinReduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Finiteness of limits of stalks of higher direct images along `Λ ⧸ ϖⁿ⁺¹`

Let `g : T ⟶ Y` be a morphism of schemes, `s` a geometric point of `Y` and `i : ℤ`. The functor
`H = (Hⁱ ∘ Rg_*)_s : D(T_ét, Λ) ⥤ Mod_Λ`, the stalk at `s` of the `i`-th cohomology sheaf of the
derived direct image (`AlgebraicGeometry.Etale.stalkHomologyRightDerivedLowerStar`), is
homological and `Λ`-linear. Hence, for `Λ` noetherian and complete for `I = (ϖ)` with `ϖ` a
nonzerodivisor, the limit `lim_n (Rⁱg_* (Λ ⧸ Iⁿ⁺¹)_T)_s`, along the maps induced by the quotient
maps `Λ ⧸ Iⁿ⁺² ⟶ Λ ⧸ Iⁿ⁺¹`, is a finite `Λ`-module as soon as `(Rⁱg_* (Λ ⧸ I)_T)_s` is
(`AlgebraicGeometry.Etale.finite_limit_stalkHomologyRightDerivedLowerStar`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]

/-- A homological functor followed by an exact functor is homological. -/
lemma isHomological_comp (F : C ⥤ A) (G : A ⥤ B) [F.IsHomological] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] : (F ⋙ G).IsHomological where
  exact T hT := (F.map_distinguished_exact T hT).map G

end CategoryTheory.Functor

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{v} J)
  {R : Type*} [Semiring R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
  [HasColimitsOfSize.{v, v} A]

/-- The fibre functor of a point is linear. -/
lemma linear_sheafFiber [(Φ.sheafFiber (A := A)).Additive] : (Φ.sheafFiber (A := A)).Linear R where
  map_smul f r := Φ.sheafFiber_map_smul r f

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {T Y : Scheme.{u}} (g : T ⟶ Y) {Ω : Type u} [Field Ω]
  [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The stalk at the geometric point `s` of the `i`-th cohomology sheaf of the derived direct
image: `K ↦ (Hⁱ(Rg_* K))_s`. -/
noncomputable abbrev stalkHomologyRightDerivedLowerStar (i : ℤ) :
    _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      ModuleCat.{u + 1} Λ :=
  R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ _root_.DerivedCategory.homologyFunctor _ i ⋙
    (pointSmallEtale s).sheafFiber

instance (i : ℤ) : (stalkHomologyRightDerivedLowerStar (Λ := Λ) g s i).IsHomological := by
  have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := Functor.isHomological_comp (_root_.DerivedCategory.homologyFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i) (pointSmallEtale s).sheafFiber
  infer_instance

instance (i : ℤ) : (stalkHomologyRightDerivedLowerStar (Λ := Λ) g s i).Linear Λ := by
  have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := (pointSmallEtale s).linear_sheafFiber (A := ModuleCat.{u + 1} Λ) (R := Λ)
  infer_instance

variable {I : Ideal Λ} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})

/-- **Finiteness of the limit of the stalks of the higher direct images of `Λ ⧸ Iⁿ⁺¹`.** Let
`Λ` be noetherian and complete for `I = (ϖ)`, `ϖ` a nonzerodivisor. If the stalk at `s` of
`Hⁱ(Rg_* (Λ ⧸ I)_T)` is a finite `Λ`-module, then so is `lim_n (Hⁱ(Rg_* (Λ ⧸ Iⁿ⁺¹)_T))_s`,
along the maps induced by the quotient maps `Λ ⧸ Iⁿ⁺² ⟶ Λ ⧸ Iⁿ⁺¹`
(`DerivedCategory.quotPowTriangleMap_hom₃`). -/
theorem finite_limit_stalkHomologyRightDerivedLowerStar [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ] (i : ℤ)
    [Module.Finite Λ ((stalkHomologyRightDerivedLowerStar g s i).obj
      (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI 1).obj₃)] :
    Module.Finite Λ ↑(limit (Functor.ofOpSequence
      (X := fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).obj
        (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI (n + 1)).obj₃)
      fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).map
        (DerivedCategory.quotPowTriangleMap T.smallEtaleTopology hϖ hI (n + 1)).hom₃)) :=
  finite_limit_quotPowTriangle_of_finite hϖ hI _

end AlgebraicGeometry.Etale
