/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# The dual of a perfect complex on the pro-étale site

Let `a : X ⟶ Y` carry a compactification, with pro-étale dualizing complex
`ω_X = Ra^! Λ_Y` and Verdier dual `𝔻_X = RHom(-, ω_X)`, and let `η : T ≅ ω_X` be an
identification of `ω_X` with an invertible complex `T`. For `X` smooth of pure dimension `d`
the smooth purity identification `ω_{X,Λ} ≅ Λ_X(d)[2d]` is such an `η`, at each of the
coefficient stages `𝒪_E`, `E` and `Q̄_ℓ` of the Poincaré duality conventions; this file records
what it gives for perfect complexes (blueprint `theorem-poincare-duality--2`), the finite stage
being `WeilConjectures.SixFunctors.Etale.Derived.Orientation`. The statements are made for an
arbitrary object `ω` in place of `ω_X` (at a finite coefficient ring `Λ`,
`ω = AlgebraicGeometry.ProEtale.dualizingComplex Λ a` and `RHom(-, ω)` is
`AlgebraicGeometry.ProEtale.verdierDual Λ a`).

## Main definitions

- `AlgebraicGeometry.ProEtale.verdierDualIsoDerivedDualTensor`: the natural isomorphism
  `𝔻_X K ≅ K^∨ ⊗ᴸ T`.
- `AlgebraicGeometry.ProEtale.verdierDualVerdierDualIso`: the induced `𝔻_X 𝔻_X K ≅ K^∨∨`.
- `AlgebraicGeometry.ProEtale.verdierDualEquivalenceOfIso`: the anti-equivalence of the perfect
  objects given by `𝔻_X`.

## Main statements

- `AlgebraicGeometry.ProEtale.whiskerLeft_verdierDualIsoDerivedDualTensor_hom_app_comp`:
  compatibility with the evaluations.
- `AlgebraicGeometry.ProEtale.toIhomIhom_comp_verdierDualVerdierDualIso_hom`: the Verdier
  biduality is the coefficient-dual biduality.
- `AlgebraicGeometry.ProEtale.isIso_toIhomIhom_dualizingComplex`,
  `AlgebraicGeometry.ProEtale.isIso_toIhomIhomUnit`: Verdier and coefficient-dual biduality
  for perfect complexes.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X : Scheme.{u}} {ω T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  (η : T ≅ ω) (hT : IsInvertible T)

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

For an identification `η : T ≅ ω_X` of the pro-étale dualizing complex with an invertible
complex `T` (for smooth `X` of pure dimension `d`, `T = Λ_X(d)[2d]`), the natural isomorphism
```
  𝔻_X K = RHom(K, ω_X) ≅ RHom(K, T) ≅ K^∨ ⊗ᴸ T,
```
the composite of `RHom(K, η⁻¹)` and of the twist interchange
(`CategoryTheory.MonoidalClosed.ihomIsoIhomUnitTensor`). -/
noncomputable def verdierDualIsoDerivedDualTensor :
    (RHom(X)[A]).flip.obj ω ≅ derivedDual A X ⋙ tensorRight T :=
  MonoidalClosed.ihomFlipIsoIhomUnitTensor η hT

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (compatibility with the
canonical evaluation).

Under `𝔻_X K ≅ K^∨ ⊗ᴸ T` the evaluation `K ⊗ᴸ 𝔻_X K ⟶ ω_X` is the coefficient evaluation
`K ⊗ᴸ K^∨ ⟶ Λ_X` tensored with `T`, up to `η`. -/
@[reassoc]
lemma whiskerLeft_verdierDualIsoDerivedDualTensor_hom_app_comp
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ◁ ((verdierDualIsoDerivedDualTensor η hT).hom.app (op K)) ≫ (α_ _ _ _).inv ≫
        derivedDualEval K ▷ T ≫ (λ_ T).hom =
      (ihom.ev K).app (ω) ≫ η.inv :=
  MonoidalClosed.whiskerLeft_ihomIsoIhomUnitTensor_hom_comp η hT K

include η hT in
/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

Under an identification `ω_X ≅ T` with an invertible `T`, the Verdier dual of a perfect complex
is perfect. -/
theorem isDualizable_verdierDual
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsDualizable K) :
    IsDualizable (((RHom(X)[A]).flip.obj ω).obj (op K)) := by
  obtain ⟨_⟩ :=
    _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology X) A)
  exact MonoidalClosed.isDualizable_ihom_obj η hT hK

variable [BraidedCategory (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))]

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

For any braiding of `D(X_proét)`, the coefficient-dual biduality `K ⟶ K^∨∨` of a perfect
complex is an isomorphism. -/
theorem isIso_toIhomIhomUnit
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsDualizable K) :
    IsIso (MonoidalClosed.toIhomIhomUnit K) :=
  MonoidalClosed.isIso_toIhomIhomUnit_of_isDualizable hK

/-- The isomorphism `𝔻_X 𝔻_X K ≅ K^∨∨` induced by `𝔻_X K ≅ K^∨ ⊗ᴸ T`. -/
noncomputable def verdierDualVerdierDualIso
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((RHom(X)[A]).flip.obj ω).obj (op (((RHom(X)[A]).flip.obj ω).obj (op K))) ≅
      (derivedDual A X).obj (op ((derivedDual A X).obj (op K))) :=
  MonoidalClosed.ihomIhomIsoIhomIhomUnit η hT K

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (biduality).

Under the isomorphism `𝔻_X 𝔻_X K ≅ K^∨∨` induced by `η`, the double-dual map
`K ⟶ 𝔻_X 𝔻_X K` is the coefficient-dual biduality `K ⟶ K^∨∨`. -/
@[reassoc]
lemma toIhomIhom_comp_verdierDualVerdierDualIso_hom
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    MonoidalClosed.toIhomIhom (ω) K ≫
        (verdierDualVerdierDualIso η hT K).hom =
      MonoidalClosed.toIhomIhomUnit K :=
  MonoidalClosed.toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom η hT K

include η hT in
/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (biduality).

For a perfect `K` the double-dual map `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. -/
theorem isIso_toIhomIhom_dualizingComplex
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsDualizable K) :
    IsIso (MonoidalClosed.toIhomIhom (ω) K) :=
  MonoidalClosed.isIso_toIhomIhom_of_isDualizable η hT hK

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (anti-equivalence).

The Verdier dual `𝔻_X` restricts to an anti-equivalence of the perfect objects of
`D(X_proét)`, its own quasi-inverse, the unit and counit being the double-dual isomorphisms. -/
noncomputable def verdierDualEquivalenceOfIso :
    (ObjectProperty.FullSubcategory
      (IsDualizable (C := _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))))ᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (IsDualizable (C := _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) :=
  MonoidalClosed.dualizableIhomEquivalence η hT

/-- The functor of the anti-equivalence `verdierDualEquivalenceOfIso` is `𝔻_X`. -/
lemma verdierDualEquivalenceOfIso_functor_obj_obj
    (K : (ObjectProperty.FullSubcategory
      (IsDualizable (C := _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))))ᵒᵖ) :
    ((verdierDualEquivalenceOfIso η hT).functor.obj K).obj =
      ((RHom(X)[A]).flip.obj ω).obj (op K.unop.obj) :=
  rfl

end ProEtale

end AlgebraicGeometry
