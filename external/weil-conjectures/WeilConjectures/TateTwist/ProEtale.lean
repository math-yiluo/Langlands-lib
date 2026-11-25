/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.TateTwist.RootsOfUnity

/-!

# Tate twists of the `ℚ̄_ℓ`-sheaf on the pro-étale site

Let `ℓ` be a prime and `X` a scheme. This file constructs the Tate twists `ℚ̄_ℓ,X(d)`,
`d ∈ ℤ`, as module objects over the coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`
(`AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X`) of abelian
sheaves on `X_proét`, the pullback of the condensed ring `ℚ̲̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` along `p_X : X_proét ⟶ *_proét`,
following Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8:
```
ℤ_ℓ(1) := lim_n μ_{ℓ^n},     ℚ̄_ℓ(1) := ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ(1),
```
where `ℤ_ℓ = ℤ_ℓ,X = p_X^* ℤ̲_ℓ` is the pullback of the condensed ring `ℤ̲_ℓ = C(-, ℤ_ℓ)`.

## The construction

* The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1)` is the free module `ℤ_ℓ,X ⊗ μ_{ℓ^n}` on the sheaf `μ_{ℓ^n}` of
  `ℓ^n`-th roots of unity (`AlgebraicGeometry.ProEtale.rootsOfUnitySheaf`), the tensor product
  being the sheafified tensor product of abelian sheaves. Since `μ_{ℓ^n}` is killed by `ℓ^n`, this
  is `ℤ/ℓ^n ⊗_{ℤ/ℓ^n} μ_{ℓ^n} = μ_{ℓ^n}` as an abelian sheaf, with its natural structure of a
  module over `ℤ_ℓ,X ⟶ ℤ/ℓ^n` (`AlgebraicGeometry.ProEtale.tateModuleLevel`). Taking the free
  module avoids defining the action of `ℤ_ℓ,X` on `μ_{ℓ^n}` by hand.
* `ℤ_ℓ(1)` is the limit, in the category of `ℤ_ℓ,X`-module objects, of the inverse system
  `ℤ_ℓ ⊗ μ_{ℓ^{n+1}} ⟶ ℤ_ℓ ⊗ μ_{ℓ^n}` induced by the `ℓ`-th power maps
  (`AlgebraicGeometry.ProEtale.tateModule`).
* `ℚ̄_ℓ(1)` is the extension of scalars of `ℤ_ℓ(1)` along the coefficient change
  `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.coefficientMap`), the pullback along `p_X` of the
  inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings (`Profinite.padicIntRingObjToPadicAlgCl`), i.e. the
  relative tensor product `ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)` (`AlgebraicGeometry.ProEtale.tateTwistOne`).
  The tensor product has to be taken over `ℤ_ℓ,X` and not over `ℤ`: `ℚ̄_ℓ ⊗_ℤ μ_{ℓ^n} = 0`, and
  `ℚ̄_ℓ ⊗_ℤ ℤ_ℓ(1)` is much larger than `ℚ̄_ℓ(1)`.
* For `d ≥ 0`, `ℚ̄_ℓ(d)` is the `d`-th tensor power of `ℚ̄_ℓ(1)` over `ℚ̄_ℓ,X`, and for `d < 0`
  it is the dual `Hom_{ℚ̄_ℓ}(ℚ̄_ℓ(-d), ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.tateTwist`).

Finally `ℚ̄_ℓ,X(d)` is placed in degree `0` of the derived category `D(Mod_{ℚ̄_ℓ,X})`
(`AlgebraicGeometry.ProEtale.tateTwistDerived`), and the twist functor `K ↦ K(d)` on
`D(Mod_{ℚ̄_ℓ,X})` is the derived tensor product with it
(`AlgebraicGeometry.ProEtale.tateTwistFunctor`).

## Implementation notes

* The construction is functorial in nothing: the comparisons `f^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)`, the
  invertibility `ℚ̄_ℓ(d) ⊗ ℚ̄_ℓ(e) ≅ ℚ̄_ℓ(d + e)` and the local triviality of `ℚ̄_ℓ(1)` when `ℓ`
  is invertible on `X` are not stated here.
* The Galois (Frobenius) action on `ℚ̄_ℓ(1)` for `X` over a finite field, which is what
  distinguishes `ℚ̄_ℓ(d)` from `ℚ̄_ℓ` over a separably closed field, is part of the Weil sheaf
  formalism and is not considered.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `ℤ_ℓ ⊆ ℚ_ℓ`, as a ring homomorphism into the bottom finite subextension
`ℚ_ℓ ⊆ ℚ̄_ℓ`. -/
noncomputable def padicIntToBotFiniteIntermediateField :
    ℤ_[ℓ] →+* (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (algebraMap ℚ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))).comp PadicInt.Coe.ringHom

lemma continuous_padicIntToBotFiniteIntermediateField :
    Continuous (padicIntToBotFiniteIntermediateField ℓ) :=
  continuous_induced_rng.2
    ((continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val)

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings: a continuous map `S → ℤ_ℓ` is a section of
`ℚ̲̄_ℓ` over `S`, with values in the finite subextension `ℚ_ℓ`. -/
noncomputable def padicIntCondensedRingToPadicAlgCl :
    padicIntCondensedRing.{u} ℓ ⟶ padicAlgClCondensedRing ℓ :=
  continuousMapRingSheafMap (padicIntToBotFiniteIntermediateField ℓ)
      (continuous_padicIntToBotFiniteIntermediateField ℓ) ≫
    padicSubfieldCondensedRingToPadicAlgCl ℓ ⟨⊥, inferInstance⟩

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups: the abelian sheaf
morphism underlying `Profinite.padicIntCondensedRingToPadicAlgCl`. -/
noncomputable def padicIntRingObjToPadicAlgCl :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntCondensedRingToPadicAlgCl ℓ)

instance : IsMonHom (padicIntRingObjToPadicAlgCl.{u} ℓ) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntCondensedRingToPadicAlgCl ℓ)))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Tate module `ℤ_ℓ(1)` -/

/-- The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1) = ℤ_ℓ,X ⊗ μ_{ℓ^n}`: the free `ℤ_ℓ,X`-module on the sheaf of
`ℓ^n`-th roots of unity, where `ℤ_ℓ,X = p_X^* ℤ̲_ℓ`. As an abelian sheaf it is `μ_{ℓ^n}`, since
`μ_{ℓ^n}` is killed by `ℓ^n`. -/
noncomputable def tateModuleLevel (n : ℕ) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  (Mod.freeFunctor _).obj (rootsOfUnitySheaf X (ℓ ^ n))

/-- The transition map `ℤ/ℓ^{n+1}(1) ⟶ ℤ/ℓ^n(1)` of the Tate module, induced by the `ℓ`-th
power map `μ_{ℓ^{n+1}} ⟶ μ_{ℓ^n}`. -/
noncomputable def tateModuleTransition (n : ℕ) :
    tateModuleLevel X ℓ (n + 1) ⟶ tateModuleLevel X ℓ n :=
  (Mod.freeFunctor _).map (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ℓ ^ n) ℓ)

/-- The inverse system `n ↦ ℤ/ℓ^n(1)` of `ℤ_ℓ,X`-modules. -/
noncomputable def tateModuleSystem :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  Functor.ofOpSequence (tateModuleTransition X ℓ)

/-- The Tate module `ℤ_ℓ(1) = lim_n μ_{ℓ^n}` on `X_proét`, as a module object over `ℤ_ℓ,X`: the
limit of the inverse system `n ↦ ℤ/ℓ^n(1)`. -/
noncomputable def tateModule :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  limit (tateModuleSystem X ℓ)

/-! ### The Tate twists `ℚ̄_ℓ(d)` -/

/-- The Tate twist `ℚ̄_ℓ,X(1) = ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)`: the extension of scalars of the Tate
module along the coefficient change `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def tateTwistOne :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
  (Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
    (tateModule X ℓ)

/-- The non-negative Tate twists `ℚ̄_ℓ,X(d) = ℚ̄_ℓ,X(1)^{⊗ d}`, the tensor powers over `ℚ̄_ℓ,X`,
with `ℚ̄_ℓ,X(0) = ℚ̄_ℓ,X`. -/
noncomputable def tateTwistNat :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  | 0 => 𝟙_ _
  | d + 1 => tateTwistNat d ⊗ tateTwistOne X ℓ

/-- The Tate twist `ℚ̄_ℓ,X(d)` for `d ∈ ℤ`: the tensor power `ℚ̄_ℓ,X(1)^{⊗ d}` for `d ≥ 0`, and
the dual `Hom_{ℚ̄_ℓ,X}(ℚ̄_ℓ,X(-d), ℚ̄_ℓ,X)` for `d < 0`. -/
noncomputable def tateTwist :
    ℤ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  | (d : ℕ) => tateTwistNat X ℓ d
  | .negSucc d => (ihom (tateTwistNat X ℓ (d + 1))).obj (𝟙_ _)

lemma tateTwist_natCast (d : ℕ) : tateTwist X ℓ d = tateTwistNat X ℓ d := rfl

/-- The Tate twist `ℚ̄_ℓ,X(d)`, placed in degree `0` of the derived category
`D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistDerived (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  (DerivedCategory.singleFunctor _ 0).obj (tateTwist X ℓ d)

/-- The Tate twist functor `K ↦ K(d) = K ⊗ᴸ_{ℚ̄_ℓ,X} ℚ̄_ℓ,X(d)` on `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistFunctor (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  tensorRight (tateTwistDerived X ℓ d)

end AlgebraicGeometry.ProEtale
