/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurjGenerators

/-!
# (Obj): descent of bounded constructible `ℚ̄_ℓ`-complexes

Let `ℓ` be a prime and `X` a scheme with noetherian underlying space. Assuming
**(Hom)**-surjectivity for the extensions of scalars from the finite subextensions
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, every bounded constructible `ℚ̄_ℓ,X`-complex `K` is isomorphic to
`T^X_{E,Ω} K_E = ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E` for some finite subextension `E` and some bounded
constructible `E_X`-complex `K_E`
(`ProEtale.exists_iso_derivedExtendScalarsToPadicAlgCl_obj`, blueprint
`proposition-dctf-x-qbar-2-colimit--2`, `lemma-descent-finite-coefficient-field--2`).

The complexes which descend in this sense (`ProEtale.descendsToPadicSubfield`) form a class closed
under isomorphisms and extensions in distinguished triangles (the cone step,
`ProEtale.descendsToPadicSubfield_obj₂`) and under shifts, which contains the generators
`a_! L` of `Dᵇc(X, ℚ̄_ℓ)` (`ProEtale.descendsToPadicSubfield_lowerShriek`). By the generation of
`Dᵇc(X, ℚ̄_ℓ)` by the `(a_! L)[n]`
(`ProEtale.CondensedRing.boundedConstructible_le_of_lowerShriek_isLocallyFree`), it contains
every bounded constructible complex.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- **(Obj)**, blueprint `proposition-dctf-x-qbar-2-colimit--2`,
`lemma-descent-finite-coefficient-field--2`: on a scheme with noetherian underlying space,
assuming (Hom)-surjectivity `hHom`, every bounded constructible `ℚ̄_ℓ,X`-complex `K` is
isomorphic to `ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E` for some finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and some
bounded constructible `E_X`-complex `K_E`. -/
theorem exists_iso_derivedExtendScalarsToPadicAlgCl_obj
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [TopologicalSpace.NoetherianSpace X]
    (hHom : ∀ {E F : PadicAlgCl.FiniteIntermediateField ℓ}
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ E))),
      boundedConstructible _ K →
      ∀ (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ F))),
      boundedConstructible _ L →
      ∀ (f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K ⟶
        (derivedExtendScalarsToPadicAlgCl X ℓ F).obj L),
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H)
        (g : (derivedExtendScalarsSubfield X ℓ hE).obj K ⟶
          (derivedExtendScalarsSubfield X ℓ hF).obj L),
        f = (derivedExtendScalarsCompIso X ℓ hE).inv.app K ≫
          (derivedExtendScalarsToPadicAlgCl X ℓ H).map g ≫
            (derivedExtendScalarsCompIso X ℓ hF).hom.app L)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ)))
    (hK : boundedConstructible (padicAlgClRingObj X ℓ) K) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ E))),
      boundedConstructible _ K' ∧ Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K' ≅ K) :=
  CondensedRing.boundedConstructible_le_of_lowerShriek_isLocallyFree ℓ X
    (descendsToPadicSubfield X ℓ)
    (fun T hT h₁ h₃ ↦ descendsToPadicSubfield_obj₂ X ℓ hHom T hT h₁ h₃)
    (fun j _ i _ L hL n ↦ (descendsToPadicSubfield X ℓ).le_shift n _
      (descendsToPadicSubfield_lowerShriek X ℓ j i L hL)) K hK

end AlgebraicGeometry.ProEtale
