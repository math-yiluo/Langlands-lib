/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.WeilDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilComplex

/-!
# Scalar extension of strict Weil complexes

Let `R → S` be a homomorphism of finite commutative rings whose exponent is invertible on a
scheme `X` of finite type over a field, and `g` an automorphism of `X`. Derived scalar extension
`Ψ = - ⊗ᴸ_R S` preserves `Dctf` (`AlgebraicGeometry.ProEtale.
constructibleFiniteTor_leftDerivedSheafExtendScalars`), so it sends a strict Weil complex
`(K, φ : Lg^* K ≅ K)` over `R` to the strict Weil complex `(Ψ K, φ_S)` over `S`, with
`φ_S : Lg^* Ψ K ≅ Ψ Lg^* K --Ψ φ--> Ψ K` (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`).

## Main definitions

- `AlgebraicGeometry.ProEtale.StrictWeilComplex.extendScalars`: the scalar extension
  `(K_S, φ_S)` of a strict Weil complex `(K, φ)`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace StrictWeilComplex

variable {R : Type (u + 1)} (S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [Finite R]
  [Finite S] {k : Type u} [Field k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent R X] {g : X ≅ X}

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7`: the scalar extension `(K_S, φ_S)`
of a strict Weil complex `(K, φ)` over a finite ring `R` along `R → S`: `K_S = K ⊗ᴸ_R S` lies in
`Dctf` (`AlgebraicGeometry.ProEtale.constructibleFiniteTor_leftDerivedSheafExtendScalars`), and its
Weil structure is `φ_S : Lg^* K_S ≅ (Lg^* K) ⊗ᴸ_R S --φ ⊗ S--> K_S`, whose underlying morphism
is `AlgebraicGeometry.ProEtale.extendScalarsWeilDatum` of that of `φ`. -/
noncomputable def extendScalars (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) :
    StrictWeilComplex (ModuleCat.{u + 1} S) g where
  obj := ⟨L(sheafExtendScalars (algebraMap R S) X).obj W.obj.obj,
    constructibleFiniteTor_leftDerivedSheafExtendScalars aX W.obj.property⟩
  frobenius := (leftDerivedUpperStarExtendScalarsIso R S g.hom).app W.obj.obj ≪≫
    L(sheafExtendScalars (algebraMap R S) X).mapIso W.frobenius

lemma extendScalars_obj_obj (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) :
    (W.extendScalars S aX).obj.obj = L(sheafExtendScalars (algebraMap R S) X).obj W.obj.obj :=
  rfl

lemma extendScalars_frobenius_hom (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) :
    (W.extendScalars S aX).frobenius.hom = extendScalarsWeilDatum W.frobenius.hom :=
  rfl

end StrictWeilComplex

end AlgebraicGeometry.ProEtale
