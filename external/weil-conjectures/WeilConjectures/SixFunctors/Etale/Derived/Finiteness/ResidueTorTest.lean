/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.ResidueField
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Testing finite Tor amplitude at the residue field

Let `Λ` be an Artinian local ring with residue field `κ`, for instance the finite coefficient
ring `A_{E,n} = 𝒪_E/ϖⁿ` with `κ = A_{E,1}`, and let `K ∈ D(X_ét, Λ)`. Then `K` has Tor amplitude
in `[a, b]` if and only if `K ⊗ᴸ κ_X` has cohomology in `[a, b]` (blueprint
`theorem-f-shriek-finite-coefficients--1`).

## Proof

One direction is the definition of Tor amplitude, tested against the constant sheaf `κ_X`. For
the converse, represent `K` by a K-flat complex `P` of flat sheaves, so that `K ⊗ᴸ F` is the
complex `P ⊗ F` for every sheaf `F`. Exactness of a complex of étale sheaves is checked on the
stalks at the geometric points `x̄`, and the stalk of `P ⊗ F` is `P_x̄ ⊗ F_x̄`, a complex of flat
`Λ`-modules tensored with a module. Over the Artinian local ring `Λ`, exactness of `P_x̄ ⊗ κ` in a
degree propagates to exactness of `P_x̄ ⊗ M` for every module `M`
(`DerivedCategory.exactAt_tensorRight_of_exactAt_tensorRight_residueField`).

The blueprint states the lemma for bounded constructible `K`; neither boundedness nor
constructibility is needed, and the main statement does not assume them.

## Main statements

- `AlgebraicGeometry.Etale.torAmplitudeIn_iff_homologyConcentratedIn_tensor_residueField`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- An étale sheaf of `Λ`-modules whose stalks at all geometric points vanish is zero. -/
lemma isZero_of_forall_isZero_sheafFiber (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ s : X, IsZero ((X.uliftPointSmallEtale s).sheafFiber.obj G)) : IsZero G := by
  have : IsIso (0 : G ⟶ 0) := isIso_of_isIso_sheafFiber_map _ fun s ↦
    ⟨⟨0, (h s).eq_of_src _ _,
      (((X.uliftPointSmallEtale s).sheafFiber.map_isZero (isZero_zero _))).eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- Exactness of a complex of étale sheaves of `Λ`-modules is checked on the stalks at the
geometric points. -/
lemma exactAt_of_forall_exactAt_sheafFiber
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (q : ℤ)
    (h : ∀ s : X, (((X.uliftPointSmallEtale s).sheafFiber.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt q) :
    K.ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine isZero_of_forall_isZero_sheafFiber _ fun s ↦ ?_
  have hs := h s
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hs
  exact hs.of_iso ((K.sc q).mapHomologyIso _).symm

/-- The stalk at a geometric point of the complex `P ⊗ F` is the complex `P_x̄ ⊗ F_x̄`. -/
noncomputable def sheafFiberMapHomologicalComplexTensorRightIso (s : X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((X.uliftPointSmallEtale s).sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((tensorRight F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      ((tensorRight ((X.uliftPointSmallEtale s).sheafFiber.obj F)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((X.uliftPointSmallEtale s).sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (Functor.OplaxMonoidal.δ (X.uliftPointSmallEtale s).sheafFiber (P.X n) F))
    (fun i j _ ↦ by
      dsimp
      exact Functor.OplaxMonoidal.δ_natural_left _ (P.d i j) F)

variable [IsLocalRing Λ] [IsArtinianRing Λ]

/-- The constant sheaf `κ_X` on the residue field `κ` of `Λ`. -/
noncomputable abbrev residueFieldSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))

/-- Let `P` be a complex of flat étale sheaves of `Λ`-modules, `Λ` Artinian local with residue
field `κ`. If `P ⊗ κ_X` is exact in degree `q`, so is `P ⊗ F` for every sheaf `F`: on stalks at
a geometric point this is
`DerivedCategory.exactAt_tensorRight_of_exactAt_tensorRight_residueField`. -/
lemma exactAt_tensorRight_of_exactAt_tensorRight_residueFieldSheaf
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : ∀ n, ObjectProperty.flat (P.X n)) (q : ℤ)
    (hκ : (((tensorRight (residueFieldSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).ExactAt q)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (((tensorRight F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q := by
  refine exactAt_of_forall_exactAt_sheafFiber _ q fun s ↦ ?_
  let Φ := X.uliftPointSmallEtale s
  let Ps := (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hPs (n : ℤ) : ObjectProperty.flat (Ps.X n) := Φ.flat_sheafFiber_obj (hP n)
  -- the stalk of `P ⊗ κ_X` is `P_x̄ ⊗ κ`
  have hκs : (((tensorRight (Φ.sheafFiber.obj (residueFieldSheaf X))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Ps).ExactAt q :=
    (show ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((tensorRight (residueFieldSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).ExactAt q from hκ.map Φ.sheafFiber).of_iso
      (sheafFiberMapHomologicalComplexTensorRightIso s P _)
  have hκ' : (((tensorRight (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Ps).ExactAt q := by
    rw [_root_.DerivedCategory.exactAt_tensorRight_iff] at hκs ⊢
    have : Module.Flat Λ (Ps.X (q + 1)) := (ModuleCat.flat_iff_flat _).1 (hPs _)
    refine LinearMap.exact_rTensor_of_linearEquiv _ _ ?_
      (Φ.sheafFiberConstantSheafIso (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))).toLinearEquiv
      hκs
    rw [← ModuleCat.hom_comp, Ps.d_comp_d, ModuleCat.hom_zero]
  exact (_root_.DerivedCategory.exactAt_tensorRight_of_exactAt_tensorRight_residueField Ps hPs q
    hκ' (Φ.sheafFiber.obj F)).of_iso (sheafFiberMapHomologicalComplexTensorRightIso s P F).symm

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Testing finite Tor amplitude at the residue
field.

Let `Λ` be an Artinian local ring with residue field `κ` (for instance `A = 𝒪_E/ϖⁿ` and
`κ = A/(ϖ)`), and let `K ∈ D(X_ét, Λ)`. Then `K` has Tor amplitude in `[a, b]` if and only if
the derived tensor product `K ⊗ᴸ κ_X` has cohomology in `[a, b]`. Representing `K` by a K-flat
complex `P` of flat sheaves, the converse direction is checked on the stalks `P_x̄` at the
geometric points, which are complexes of flat modules over the Artinian local ring `Λ`
(`AlgebraicGeometry.Etale.exactAt_tensorRight_of_exactAt_tensorRight_residueFieldSheaf`). No
boundedness or constructibility of `K` is needed. -/
theorem torAmplitudeIn_iff_homologyConcentratedIn_tensor_residueField {a b : ℤ}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    _root_.DerivedCategory.torAmplitudeIn (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) a b
        K ↔
      _root_.DerivedCategory.homologyConcentratedIn a b
        (K ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj (residueFieldSheaf X)) := by
  obtain ⟨P, hPk, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_flat_iso K
  rw [_root_.DerivedCategory.torAmplitudeIn_iff_forall_exactAt hPk e,
    _root_.DerivedCategory.homologyConcentratedIn_tensor_iff_exactAt hPk e]
  exact ⟨fun h ↦ h _, fun h F q hq ↦
    exactAt_tensorRight_of_exactAt_tensorRight_residueFieldSheaf P hP q (h q hq) F⟩

end Etale

end AlgebraicGeometry
