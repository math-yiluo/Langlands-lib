/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!

# Duality against pullback

Let `f : X ⟶ Y` be a morphism admitting a compactification. The Verdier dual exchanges the
derived pullback and the exceptional inverse image:

`𝔻_X Lf^* ≅ Rf^! 𝔻_Y`.

It is the evaluation at `N = ω_Y` of the internal-Hom form

`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`,

natural in `K` and `N`, combined with `Rf^! ω_Y ≅ ω_X`. For `f` smooth of pure relative
dimension `d` with an orientation, substituting smooth purity `Rf^! ≅ Lf^*(-)(d)[2d]` gives
`𝔻_X Lf^* K ≅ (Lf^* 𝔻_Y K)(d)[2d]`.

As the blueprint remark `rem-sf-kv-formal` explains, given biduality the first statement turns
the Künneth–Verdier theorem into the statement that Verdier duality commutes with external
products, `𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N`, which is not formal.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_rightDerivedUpperShriek_derivedHom_iso`
  (`lemma-internal-adjunction-two-exchange-formulas--3`):
  `Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`, for a general coefficient category in which the
  projection formula holds.
- `AlgebraicGeometry.Etale.nonempty_rightDerivedUpperShriek_derivedHom_iso_of_finite`
  (`lemma-internal-adjunction-two-exchange-formulas--3`): the same at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`
  (`lemma-internal-adjunction-two-exchange-formulas--3`): `𝔻_X Lf^* ≅ Rf^! 𝔻_Y` as functors on
  `D(Y_ét, Λ)ᵒᵖ`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_leftDerivedUpperStar`
  (`lemma-internal-adjunction-two-exchange-formulas--3`): `𝔻_X Lf^* K ≅ (Lf^* 𝔻_Y K)(d)[2d]` for an
  oriented smooth `f`.

## Implementation notes

The blueprint obtains `𝔻_X Lf^* ≅ Rf^! 𝔻_Y` by passing to right adjoints in the Verdier
exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`, using biduality to see that `𝔻_Y` is its own adjoint. Here the
same mate calculus is applied one step earlier, to the projection formula itself: the
internal-Hom form is the conjugate of `PF : Rf_! M ⊗ᴸ K ≅ Rf_!(M ⊗ᴸ Lf^* K)` under the
adjunctions `K ⊗ᴸ Rf_!(-) ⊣ Rf^! RHom(K, -)` and `Rf_!(Lf^* K ⊗ᴸ -) ⊣ RHom(Lf^* K, Rf^! -)`,
exactly as the tensor–Hom exchange (`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`)
is. This avoids biduality, so the isomorphism holds on all of `D(Y_ét, Λ)` and not only on
`Dᵇctf`. Its naturality in `f` is not recorded.

The symmetry of `⊗ᴸ` is only available as `Nonempty`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`), so the isomorphisms are asserted
as `Nonempty (_ ≅ _)`, as for the other comparison isomorphisms of this directory.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--3`: Duality against pullback,
internal-Hom form.

Let `f : X ⟶ Y` admit a compactification, and assume the projection formula for `f`
(axiom (A3) of `def-sf-datum`). Then

`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`,

naturally in `K` and `N`, i.e. as bifunctors `D(Y_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(X_ét)`.

The bifunctor `(K, M) ↦ K ⊗ᴸ Rf_! M` is left adjoint, with the parameter `K`, to
`(K, N) ↦ Rf^! RHom_Y(K, N)`, and `(K, M) ↦ Rf_!(Lf^* K ⊗ᴸ M)` is left adjoint to
`(K, N) ↦ RHom_X(Lf^* K, Rf^! N)`. The projection formula, together with the symmetry of
`⊗ᴸ`, identifies the two left adjoints, and the isomorphism is the conjugate
(`CategoryTheory.ParametrizedAdjunction.conjugateIso`). -/
theorem nonempty_rightDerivedUpperShriek_derivedHom_iso [IsIso (projectionMap (ModuleCat.{u + 1} Λ)
    f)] :
    Nonempty (RHom(Y)[ModuleCat.{u + 1} Λ] ⋙ (Functor.whiskeringRight _ _ _).obj R(f)^![Λ] ≅
      L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ RHom(X)[ModuleCat.{u + 1} Λ] ⋙ (Functor.whiskeringLeft _ _
          _).obj R(f)^![Λ]) := by
  obtain ⟨βX⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  obtain ⟨βY⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Y
  -- `Rf_!(Lf^* K ⊗ᴸ M) ≅ Rf_!(M ⊗ᴸ Lf^* K) ≅ Rf_! M ⊗ᴸ K ≅ K ⊗ᴸ Rf_! M`
  let e : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ -⊗ᴸ-(X)[ModuleCat.{u + 1} Λ] ⋙ (Functor.whiskeringLeft _ _
      _).obj (𝟭 _) ⋙
        (Functor.whiskeringRight _ _ _).obj R(f)_![ModuleCat.{u + 1} Λ] ≅
      -⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ] ⋙ (Functor.whiskeringLeft _ _ _).obj R(f)_![ModuleCat.{u + 1} Λ]
          ⋙
        (Functor.whiskeringRight _ _ _).obj (𝟭 _) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft L((f)^*[ModuleCat.{u + 1} Λ]) βX)
        ((Functor.whiskeringRight _ _ _).obj R(f)_![ModuleCat.{u + 1} Λ]) ≪≫
      (asIso ((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f))).symm ≪≫
      Functor.isoWhiskerRight βY.symm ((Functor.whiskeringLeft _ _ _).obj R(f)_![ModuleCat.{u + 1}
          Λ])
  exact ⟨((derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} Λ) Y).comp
      (rightDerivedUpperShriekAdjunction Λ f)
      Adjunction.id).conjugateIso
    (((derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} Λ) X).precomp L((f)^*[ModuleCat.{u + 1}
        Λ])).comp Adjunction.id
      (rightDerivedUpperShriekAdjunction Λ f)) e⟩

end General

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--3`: Duality against pullback,
internal-Hom form.

For a morphism `f : X ⟶ Y` admitting a compactification and a finite coefficient ring `Λ`,

`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`,

naturally in `K` and `N`. This is
`AlgebraicGeometry.Etale.nonempty_rightDerivedUpperShriek_derivedHom_iso` at
`A = ModuleCat Λ`, the projection formula holding at finite coefficients
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). -/
theorem nonempty_rightDerivedUpperShriek_derivedHom_iso_of_finite :
    Nonempty (RHom(Y)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringRight _ _ _).obj R(f)^![Λ] ≅
      L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ RHom(X)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(f)^![Λ]) :=
  have := isIso_projectionMap_of_finite Λ f
  nonempty_rightDerivedUpperShriek_derivedHom_iso _ f

variable {S : Scheme.{u}} (aY : Y ⟶ S) [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--3`: Duality against pullback.

Let `f : X ⟶ Y` be a morphism over a base `S`, with structure morphisms `a_Y : Y ⟶ S` and
`a_X = f ≫ a_Y`, all admitting a compactification, and let `Λ` be a finite coefficient ring.
Then the Verdier duals `𝔻_Y = RHom_Y(-, ω_Y)` and `𝔻_X = RHom_X(-, ω_X)` satisfy

`𝔻_X Lf^* ≅ Rf^! 𝔻_Y`

as functors `D(Y_ét, Λ)ᵒᵖ ⥤ D(X_ét, Λ)`.

The blueprint deduces this from the Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`
(`lemma-internal-adjunction-two-exchange-formulas--2`) by passing to right adjoints, using biduality
to identify the adjoint of `𝔻_Y` with `𝔻_Y`, and so states it on `Dᵇctf`. The same mate calculus
applied to the projection formula gives the internal-Hom form
`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`
(`AlgebraicGeometry.Etale.nonempty_rightDerivedUpperShriek_derivedHom_iso_of_finite`) without
biduality; at `N = ω_Y`, with `Rf^! ω_Y ≅ ω_X`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`), it is the
statement, on all of `D(Y_ét, Λ)`. -/
theorem nonempty_iso_verdierDual_leftDerivedUpperStar :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ verdierDual _ (f ≫ aY) ≅
      verdierDual _ aY ⋙ R(f)^![Λ]) := by
  obtain ⟨e₁⟩ := nonempty_rightDerivedUpperShriek_derivedHom_iso_of_finite Λ f
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY
  exact ⟨Functor.isoWhiskerLeft _ ((RHom(X)[ModuleCat.{u + 1} Λ]).flip.mapIso e₂.symm) ≪≫
    (Functor.isoWhiskerRight e₁
      ((CategoryTheory.evaluation _ _).obj (dualizingComplex _ aY))).symm⟩

end Finite

section Orientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y S : Scheme.{u}}
  [HasInvertibleExponent Λ X] {d : ℕ} {f : X ⟶ Y} [HasCompactification f] (aY : Y ⟶ S)
  [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--3`: Duality against pullback,
oriented smooth case.

Let `Y` be a scheme over a base `S`, let `Λ` be a finite coefficient ring whose exponent is
invertible on `X`, and let `f : X ⟶ Y` be smooth of pure relative dimension `d`, with an
orientation `o`. Then for every `K ∈ D(Y_ét, Λ)` (the blueprint takes `K ∈ Dᵇctf(Y, Λ)` over a
perfect field)

`𝔻_X Lf^* K ≅ (Lf^* 𝔻_Y K)(d)[2d]`.

As in the blueprint, this substitutes the orientation into
`𝔻_X Lf^* K ≅ Rf^! 𝔻_Y K` (`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`):
the tensor formula `Rf^! L ≅ Lf^* L ⊗ᴸ ω_f` of
`proposition-exceptional-inverse-image-smooth-morphism`, applied to `L = 𝔻_Y K`, and the orientation
`ω_f ≅ Λ_X(d)[2d]`. -/
theorem Orientation.nonempty_iso_verdierDual_leftDerivedUpperStar (o : Orientation Λ f d)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((verdierDual _ (f ≫ aY)).obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (twistShift Λ X d).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual _ aY).obj (op K)))) := by
  have := o.smoothOfRelativeDimension
  obtain ⟨e⟩ := _root_.AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar Λ f aY
  obtain ⟨φ⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d
    ((verdierDual _ aY).obj (op K))
  exact ⟨e.app (op K) ≪≫ φ.symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso o.twistShiftIso.symm ≪≫
    (twistShiftObjIso Λ X d _).symm⟩

end Orientation

end Etale

end AlgebraicGeometry
