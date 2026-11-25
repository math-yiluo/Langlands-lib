/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineLine

/-!
# Smooth cohomological duality without a chosen orientation

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` admitting a
compactification, and a finite coefficient ring `Λ` whose exponent is invertible on `X`, the
relative dualizing complex `ω_f = Rf^! Λ_Y` is a locally constant sheaf of free rank-one
`Λ`-modules placed in degree `-2d`, and the canonical map `ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an
isomorphism for every `K`. No orientation,
that is no identification of `ω_f` with the Tate twist `Λ(d)[2d]`, is involved. The formation
of `Rf^!` commutes with arbitrary base change
(`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange`).

## Main statements

- `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`
  (`proposition-exceptional-inverse-image-smooth-morphism`).

## Implementation notes

The blueprint states `proposition-exceptional-inverse-image-smooth-morphism` for a Noetherian base;
its proof, through the étale local normal form `fu = p_d e` of a smooth morphism and the adjunctions
for étale morphisms and for the affine-space projections, does not use it, and the statement here is
made for an arbitrary base, as everywhere in `WeilConjectures.SixFunctors.Etale.Derived`. The
canonical tensor morphism is `AlgebraicGeometry.Etale.dualizingComplexTensorMap`, with the
tensor factors in the order `ω_f ⊗ᴸ Lf^* K` of the projection formula.

The canonical base change morphism `Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is the mate of the
compact-support base change `Ex_!`, which is only constructed for a quasi-compact base change
`f'`.

The exponent of `Λ` is asked to be invertible on the source `X`, not on the base `Y`: this is
the setting of the purity chapter (`proposition-exceptional-inverse-image-smooth-morphism`), and the
proof is local on `X`. Over the image of `f`, which is open, the two conditions agree.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism`: Smooth cohomological duality
without a chosen orientation.

Let `f : X ⟶ Y` be smooth, separated, compactifiable and of pure relative dimension `d`, let `Λ`
be a finite ring whose exponent is invertible on `X`, and put `ω_f = Rf^! Λ_Y`. Then `ω_f[-2d]` is
a locally constant sheaf `L` of free rank-one `Λ`-modules: `L` is locally constant, every stalk
of `L` at a geometric point is free of rank one, and `ω_f ≅ L[2d]`. For every complex `K` on `Y`,
the canonical map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`) is an isomorphism.

The proof reduces, through the étale-local normal form, to étale morphisms
(`AlgebraicGeometry.Etale.etaleSmoothDuality`) and to the affine line
(`AlgebraicGeometry.Etale.affineLineSmoothDuality`, from the projective-line adjunction), for the
Tate twist `μₙ ⊗ Λ` (`AlgebraicGeometry.Etale.hasKummerClass`). -/
theorem exists_dualizingComplex_iso_and_tensor :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (dualizingComplex Λ f ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * d : ℤ)⟧) ∧
      ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (dualizingComplexTensorMap Λ f K) :=
  have : NeZero (ringChar Λ) := ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩
  exists_dualizingComplex_iso_and_tensor_of_etale_of_affineLine etaleSmoothDuality
    (affineLineSmoothDuality etaleSmoothDuality) f d

include d in
/-- The tensor formula of `proposition-exceptional-inverse-image-smooth-morphism` with the factors
in the other order: `Lf^* K ⊗ᴸ ω_f ≅ ω_f ⊗ᴸ Lf^* K ≅ Rf^! K`, by the symmetry of the derived tensor
product and `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`. -/
theorem nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
        (dualizingComplex _ f) ≅ (R(f)^![Λ]).obj K) := by
  obtain ⟨-, -, -, -, h⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  have := h K
  exact ⟨(β.app _).app _ ≪≫ asIso (dualizingComplexTensorMap Λ f K)⟩

end Etale

end AlgebraicGeometry
