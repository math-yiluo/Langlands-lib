/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Locally constant sheaves of rank one are invertible

Let `Λ` be a commutative ring and `L` a locally constant sheaf of `Λ`-modules on the small étale
site of a scheme `X` whose stalk at every geometric point is free of rank one. Then `L` is
⊗-invertible, with inverse its dual `L^∨ = [L, Λ_X]`: the evaluation `L ⊗ L^∨ ⟶ Λ_X` is an
isomorphism. On a trivialising étale cover `U_i ⟶ X` the pullback of `L` is the constant sheaf
`Λ_{U_i}`, so this follows from the general criterion for sheaves which are trivial étale-locally
(`AlgebraicGeometry.Etale.isIso_ihom_ev_app_unit_of_upperStar_iso`).

Placed in any degree, such an `L` is then invertible in `D(X_ét, Λ)`.

This is step (4c) of the proof of blueprint `proposition-exceptional-inverse-image-smooth-morphism`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_ihom_ev_app_unit_of_isLocallyConstantSheaf`: the evaluation
  `L ⊗ [L, Λ_X] ⟶ Λ_X` of a locally constant sheaf with free rank-one stalks is an isomorphism.
- `AlgebraicGeometry.Etale.isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf`:
  such a sheaf, placed in any degree, is invertible in `D(X_ét, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- On a nonempty scheme, a constant sheaf of `Λ`-modules whose stalk at some geometric point is
`Λ` is isomorphic to the unit `Λ_X`. -/
lemma nonempty_iso_unit_of_isConstant (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [F.IsConstant X.smallEtaleTopology] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (e : (pointSmallEtale s).sheafFiber.obj F ≅ ModuleCat.of Λ Λ) :
    Nonempty (F ≅ 𝟙_ _) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨M, ⟨eM⟩⟩ := F.mem_essImage_of_isConstant
  let eΛ : M ≅ 𝟙_ (ModuleCat.{u + 1} Λ) :=
    ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm ≪≫
      (pointSmallEtale s).sheafFiber.mapIso eM ≪≫ e
  exact ⟨eM.symm ≪≫ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso eΛ ≪≫
    (Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm⟩

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism`, step (4c): a lisse sheaf of
rank one is invertible.

For a locally constant sheaf `L` of `Λ`-modules on `X_ét` whose stalk at every geometric point
is `Λ`, the evaluation `L ⊗ [L, Λ_X] ⟶ Λ_X` is an isomorphism. On every nonempty member `U_i` of
a trivialising étale cover, `L|_{U_i}` is constant with stalks `Λ`, hence isomorphic to the unit
(`AlgebraicGeometry.Etale.nonempty_iso_unit_of_isConstant`), and the nonempty members still cover
`X`; conclude by `AlgebraicGeometry.Etale.isIso_ihom_ev_app_unit_of_upperStar_iso`. -/
theorem isIso_ihom_ev_app_unit_of_isLocallyConstantSheaf
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    IsIso ((ihom.ev L).app (𝟙_ _)) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := L)
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  -- only the nonempty members of the cover are kept: on them `L` is isomorphic to the unit
  let ι := {i : 𝒰.I₀ // Nonempty (𝒰.X i)}
  refine isIso_ihom_ev_app_unit_of_upperStar_iso (ModuleCat.{u + 1} Λ) (fun i : ι ↦ 𝒰.f i.1)
    (Set.eq_univ_of_forall fun x ↦ ?_) L fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact Set.mem_iUnion.2 ⟨⟨i, ⟨y⟩⟩, y, hy⟩
  obtain ⟨i, hi⟩ := i
  let G := (𝒰.f i)^*[ModuleCat.{u + 1} Λ]
  have hc : (G.obj L).IsConstant (𝒰.X i).smallEtaleTopology :=
    (isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) L).1 (h𝒰 i)
  let t := (𝒰.X i).algClosurePoint hi.some
  let eL := (hL _ (t ≫ 𝒰.f i)).some
  exact (nonempty_iso_unit_of_isConstant (G.obj L) t
    ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (𝒰.f i) t).app L ≪≫ eL)).some

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism`, step (4c): a lisse sheaf of
rank one is invertible.

A locally constant sheaf `L` of `Λ`-modules on `X_ét` whose stalks are `Λ` has the tensor inverse
`[L, Λ_X]`. -/
noncomputable def tensorIhomUnitIsoOfIsLocallyConstantSheaf
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    L ⊗ (ihom L).obj (𝟙_ _) ≅ 𝟙_ _ :=
  have := isIso_ihom_ev_app_unit_of_isLocallyConstantSheaf L hL
  asIso ((ihom.ev L).app (𝟙_ _))

end Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- A sheaf `L` with a tensor inverse `L'`, placed in degree zero, is invertible in `D(X_ét)`:
both are flat, so `L[0] ⊗ᴸ L'[0] ≅ (L ⊗ L')[0] ≅ 𝟙[0]`, and symmetrically using the braiding. -/
theorem Etale.isInvertible_singleFunctor_obj_of_tensorIso {L L' : Sheaf X.smallEtaleTopology A}
    (e : L ⊗ L' ≅ 𝟙_ _) :
    IsInvertible ((_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj L) :=
  ⟨_, ⟨singleFunctorObjTensorIso L L' (ObjectProperty.flat_of_tensorIso e) ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e ≪≫ singleFunctorObjUnitIso A X⟩,
    ⟨singleFunctorObjTensorIso L' L (ObjectProperty.flat_of_tensorIso (β_ L' L ≪≫ e)) ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (β_ L' L ≪≫ e) ≪≫
      singleFunctorObjUnitIso A X⟩⟩

end General

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism`, step (4d): a lisse sheaf of
rank one is invertible in `D(X_ét, Λ)`: `L[0]` has the tensor inverse `[L, Λ_X][0]`
(`AlgebraicGeometry.Etale.isInvertible_singleFunctor_obj_of_tensorIso`). -/
theorem isInvertible_singleFunctor_obj_of_isLocallyConstantSheaf
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    IsInvertible ((_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
  isInvertible_singleFunctor_obj_of_tensorIso (tensorIhomUnitIsoOfIsLocallyConstantSheaf L hL)

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism`, step (4d): a lisse sheaf of
rank one placed in any degree is invertible in `D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.isInvertible_singleFunctor_obj_of_isLocallyConstantSheaf`), shifts of
invertible complexes being invertible. -/
theorem isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) (n : ℤ) :
    DerivedCategory.isInvertible Λ X
      (((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦n⟧) :=
  DerivedCategory.isInvertible.shift ((isInvertible_iff_exists_derivedTensor _).1
    (isInvertible_singleFunctor_obj_of_isLocallyConstantSheaf L hL)) n

end Etale

end AlgebraicGeometry
