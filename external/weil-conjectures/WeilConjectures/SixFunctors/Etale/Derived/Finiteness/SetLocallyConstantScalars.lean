/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant

/-!
# Set-level finite local constancy and change of coefficients

`AlgebraicGeometry.Scheme.IsSetFLC` only sees the underlying sheaf of sets, so it can be checked
over any coefficient ring:

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isSetFLC`: finite locally constant
  sheaves over a finite ring (e.g. `ULift (𝒪_E ⧸ ℓⁿ)`, as given by the torsion finiteness theorem
  and the uniform stratification) are `IsSetFLC`;
- `AlgebraicGeometry.Scheme.IsSetFLC.restrictScalars`: it is preserved by restriction of scalars
  (e.g. along `ULift 𝒪_E → ULift (𝒪_E ⧸ ℓⁿ)`), so the levels of a torsion tower, each finite
  locally constant over its own finite ring, form an `IsSetFLC` tower over `ULift 𝒪_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A finite locally constant sheaf of modules over a finite ring has finite locally constant
underlying sheaf of sets. -/
lemma IsFiniteLocallyConstantSheaf.isSetFLC {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F) :
    IsSetFLC F :=
  IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes F hF

/-- `IsSetFLC` only depends on the underlying sheaf of sets: it is invariant under restriction of
scalars along a ring homomorphism (e.g. from `ULift 𝒪_E` to `ULift 𝒪_E ⧸ ℓⁿ`). -/
lemma IsSetFLC.restrictScalars {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (f : Λ →+* Λ')
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')} (hF : IsSetFLC F) :
    IsSetFLC ((sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} f)).obj F) :=
  hF

end AlgebraicGeometry.Scheme
