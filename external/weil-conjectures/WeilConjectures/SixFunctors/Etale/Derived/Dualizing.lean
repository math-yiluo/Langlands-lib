/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality

/-!

# The dualizing complex and Verdier duality on the étale site

Let `A` be a monoidal Grothendieck abelian coefficient category, let `S` be a base scheme and
let `a : X ⟶ S` be a structure morphism admitting a compactification. The *dualizing complex*
of `X` over `S` is `ω_X = Ra^! Λ_S`, the exceptional inverse image of the monoidal unit, and
the *Verdier dual* is `𝔻_X = RHom_X(-, ω_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplex`: `ω_X = Ra^! Λ_S`.
- `AlgebraicGeometry.Etale.verdierDual`: `𝔻_X = RHom_X(-, ω_X)`.
- `AlgebraicGeometry.Etale.verdierDualEvaluation`, `AlgebraicGeometry.Etale.verdierDualDoubleDual`
  (`definition-verdier-dual-evaluation--4`): the evaluation pairing `K ⊗ᴸ 𝔻_X K ⟶ ω_X` and the
  double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`, its transpose.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual_of_isInvertible`: biduality for
  an invertible dualizing complex.

General Verdier biduality on `Dctf(X, Λ)` (`sk-prop-sf-biduality-general`) and the preservation
of `Dctf(X, Λ)` by `𝔻_X` (`lemma-verdier-duality-preserves-constructibility--1`) are proved in
`WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality`.

## Implementation notes

`dualizingComplex` and `verdierDual` are defined relatively, for an arbitrary morphism
`a : X ⟶ S` carrying a compactification and an arbitrary coefficient category `A` for which
`Ra_!` is a left adjoint (`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` for
torsion coefficients).

The biduality theorems are stated in the setting of the blueprint's
`sk-prop-sf-biduality-general` and of `definition-constructible-sheaves--6`: `X` is a separated
scheme of finite type over a field `k`, and the coefficients are a finite ring `Λ` whose exponent is
invertible on `k`. Both hypotheses are needed. Over a singular base biduality fails already for
`a = 𝟙`: on a nodal curve, with `K = i_* Λ` the skyscraper at the node, `i^! Λ` has rank three, so
`𝔻_X 𝔻_X K` has rank nine. For `p`-torsion coefficients in characteristic `p` the Verdier dual of
`j_! Λ` is `Rj_* Λ`, which is not constructible (Artin–Schreier). At a finite stage every object of
`Dctf` is locally perfect, so no quasi-Frobenius hypothesis on `Λ` is needed.

The statements are for torsion coefficients, finitely generated objects of `A` being finite
(`CategoryTheory.ConcreteCategory.FiniteOfIsFinitelyGenerated`, which holds for `ModuleCat Λ`
with `Λ` finite). With coefficients `ℤ` they fail: for the origin `i` of `𝔸¹` in characteristic
zero, `Ri^!ℤ` has `ℚ/ℤ` in degree `3`, so `𝔻(i_*ℤ)` is not constructible, and
`𝔻𝔻(i_*ℤ) = i_*Ẑ` is not `i_*ℤ`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

namespace Etale

/-- The dualizing complex `ω_X = Ra^! Λ_S` of a scheme `X` over a base `S`, the exceptional
inverse image along the structure morphism `a : X ⟶ S` of the monoidal unit `Λ_S` (blueprint
`definition-verdier-dual-evaluation`, with `S = Spec k` and finite coefficients
`A = ModuleCat Λ`). -/
noncomputable def dualizingComplex : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) :=
  (R(a)^![Λ]).obj (𝟙_ _)

/-- Blueprint `definition-verdier-dual-evaluation--2`: Coefficient dual, Verdier dual, and the
projection formula, and `definition-verdier-dual-evaluation` (the dualizing complex).

The Verdier dual `𝔻_X = RHom_X(-, ω_X) : D(X_ét)ᵒᵖ ⥤ D(X_ét)`, the internal hom into the
dualizing complex `AlgebraicGeometry.Etale.dualizingComplex`. The other two items of the
blueprint definition are the coefficient dual `K^∨ = RHom(K, Λ_X)`
(`AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`) and the projection transformation
`PF_{f,K,L}` (`AlgebraicGeometry.Etale.projectionMap`). -/
noncomputable def verdierDual :
    (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj (dualizingComplex Λ a)

/-- The braiding of the derived tensor product on `D(X_ét)`: the braiding of the sheaf category,
with the Koszul sign rule on complexes, descended along K-flat resolutions
(`CategoryTheory.DerivedMonoidal.braidedCategory'`). It is the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`, and is used as a local instance. -/
noncomputable abbrev derivedBraidedCategory (X : Scheme.{u}) :
    BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  _root_.DerivedCategory.braidedCategory' _

attribute [local instance] derivedBraidedCategory

attribute [local instance] _root_.DerivedCategory.braidedCategory' in
/-- The double-dual transformation `K ⟶ RHom(RHom(K, ω), ω)` of the derived hom of étale sheaves,
for an object `ω`: `CategoryTheory.MonoidalClosed.toIhomIhomNatTrans`. It is stated for a general
coefficient category `A`, where the kernel checks it without unfolding the monoidal structure. -/
noncomputable def derivedHomToIhomIhomNatTrans (X : Scheme.{u})
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    𝟭 _ ⟶ ((derivedHom A X).flip.obj ω).rightOp ⋙ (derivedHom A X).flip.obj ω :=
  MonoidalClosed.toIhomIhomNatTrans ω

/-- Blueprint `definition-verdier-dual-evaluation--4`: The duality pairing and the double-dual
morphism.

The evaluation `ev_K : K ⊗ᴸ 𝔻_X K ⟶ ω_X` of the internal hom, a pairing natural in `K`. No
finiteness of `K` or of `𝔻_X K` is needed. -/
noncomputable def verdierDualEvaluation
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    K ⊗ (verdierDual Λ a).obj (op K) ⟶ dualizingComplex Λ a :=
  (ihom.ev K).app (dualizingComplex Λ a)

/-- Blueprint `definition-verdier-dual-evaluation--4`: The duality pairing and the double-dual
morphism.

The double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`, natural in `K`: the transpose of the
evaluation pairing `AlgebraicGeometry.Etale.verdierDualEvaluation` precomposed with the
symmetry `𝔻_X K ⊗ᴸ K ≅ K ⊗ᴸ 𝔻_X K` (`AlgebraicGeometry.Etale.verdierDualDoubleDual_app`).
It is `CategoryTheory.MonoidalClosed.toIhomIhom` for the dualizing complex. -/
noncomputable def verdierDualDoubleDual :
    𝟭 _ ⟶ (verdierDual Λ a).rightOp ⋙ verdierDual Λ a :=
  derivedHomToIhomIhomNatTrans (ModuleCat.{u + 1} Λ) X (dualizingComplex Λ a)

/-- Blueprint `definition-verdier-dual-evaluation--4`: the double-dual morphism `δ_K` is the
transpose of the evaluation `ev_K` composed with the symmetry,
`CategoryTheory.MonoidalClosed.toIhomIhom` (see
`CategoryTheory.MonoidalClosed.uncurry_toIhomIhom`). -/
lemma verdierDualDoubleDual_app (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))) :
    (verdierDualDoubleDual Λ a).app K = MonoidalClosed.toIhomIhom (dualizingComplex Λ a) K :=
  rfl

/-- **Verdier biduality for dualizable complexes when `ω_X` is invertible.** If the dualizing
complex `ω_X` is invertible — for instance for `X` smooth over a field, where an orientation
gives `ω_X ≅ Λ_X(d)[2d]` — then the double Verdier dual of a dualizable `K` is `K`:
`𝔻_X 𝔻_X K ≅ K`. This is the duality `[[K, ω], ω] ≅ K` of
`CategoryTheory.nonempty_iso_ihom_obj_ihom_obj_of_isInvertible`, the derived category of étale
sheaves being braided (`AlgebraicGeometry.Etale.derivedBraidedCategory`). -/
theorem nonempty_iso_verdierDual_verdierDual_of_isInvertible
    (hω : IsInvertible (dualizingComplex Λ a))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hK :
        IsDualizable K) :
    Nonempty (K ≅ (verdierDual Λ a).obj (op ((verdierDual Λ a).obj (op K)))) := by
  obtain ⟨e⟩ := nonempty_iso_ihom_obj_ihom_obj_of_isInvertible hK hω
  exact ⟨e.symm⟩

end Etale

end AlgebraicGeometry
