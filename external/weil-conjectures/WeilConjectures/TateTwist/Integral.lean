/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsComp
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!
# Integral Tate twists `𝒪_E(d)` on the pro-étale site

Let `ℓ` be a prime, `X` a scheme and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`, with ring of
integers `𝒪_E`. This file constructs the integral Tate twists `𝒪_{E,X}(d)`, `d ∈ ℤ`, as module
objects over the coefficient ring object `𝒪_{E,X} = p_X^* 𝒪̲_E`
(`AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X`), and
compares them with the Tate twists `ℚ̄_ℓ,X(d)` of `WeilConjectures.TateTwist.ProEtale`.

## The construction

* `𝒪_E(1) = 𝒪_{E,X} ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)` is the extension of scalars of the Tate module `ℤ_ℓ(1)`
  along the coefficient change `ℤ_ℓ,X ⟶ 𝒪_{E,X}`, the pullback along `p_X` of the inclusion
  `ℤ̲_ℓ ⟶ 𝒪̲_E` (`Profinite.padicIntRingObjToPadicIntegers`)
  (`AlgebraicGeometry.ProEtale.integralTateTwistOne`).
* For `d ≥ 0`, `𝒪_E(d)` is the `d`-th tensor power of `𝒪_E(1)` over `𝒪_{E,X}`, and for `d < 0`
  it is the dual `Hom_{𝒪_E}(𝒪_E(-d), 𝒪_E)` (`AlgebraicGeometry.ProEtale.integralTateTwist`).

## Comparison with `ℚ̄_ℓ`

The inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ` (`Profinite.padicIntegersRingObjToPadicAlgCl`) sends a continuous map
`S → 𝒪_E` to the map `S → 𝒪_E ⊆ E ⊆ ℚ̄_ℓ`, with values in the finite subextension `E ⊆ ℚ̄_ℓ`; it
restricts to the inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` on `ℤ̲_ℓ`
(`Profinite.padicIntRingObjToPadicIntegers_comp_padicIntegersRingObjToPadicAlgCl`). Hence the
extension of scalars of `𝒪_E(1)` along `𝒪_{E,X} ⟶ ℚ̄_ℓ,X` is `ℚ̄_ℓ(1)`, by transitivity of
extension of scalars (`AlgebraicGeometry.ProEtale.extendScalarsIntegralTateTwistOneIso`), and,
extension of scalars being strong monoidal, the same holds for all non-negative twists
(`AlgebraicGeometry.ProEtale.extendScalarsIntegralTateTwistNatIso`). The comparison for negative
twists needs the dualizability of `𝒪_E(1)`, and is in
`WeilConjectures.TateTwist.IntegralLocallyFree`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-! ### The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E` -/

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E` of ring objects of condensed abelian groups: the abelian sheaf
morphism underlying `Profinite.padicIntCondensedRingToPadicIntegersCondensedRing`. -/
noncomputable def padicIntRingObjToPadicIntegers :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ padicIntegersRingObj ℓ E :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntCondensedRingToPadicIntegersCondensedRing ℓ E)

instance : IsMonHom (padicIntRingObjToPadicIntegers.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntCondensedRingToPadicIntegersCondensedRing ℓ E)))

/-! ### The inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ` -/

variable [FiniteDimensional ℚ_[ℓ] E]

/-- The inclusion `C(-, 𝒪_E) ⟶ ℚ̲̄_ℓ` of presheaves of rings on profinite sets: a continuous map
`S → 𝒪_E`, composed with the inclusions `𝒪_E ⊆ E ⊆ ℚ̄_ℓ`, takes values in the finite
subextension `E ⊆ ℚ̄_ℓ`. -/
noncomputable def padicIntegersToPadicAlgClRingPresheaf :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    continuousMapRingPresheaf.{u} (PadicAlgCl.integers ℓ E) ⟶ padicAlgClRingPresheaf ℓ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  { app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((((algebraMap E (PadicAlgCl ℓ)).comp (PadicAlgCl.integers ℓ E).subtype).compLeftContinuous
        S.unop ((continuous_algebraMap_padicAlgCl_of_algebra ℓ E).comp
          continuous_subtype_val)).codRestrict
        (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)
        (fun a ↦ (PadicAlgCl.mem_finiteIntermediateFieldValued_iff ℓ _ _).mpr
          ⟨(IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)).fieldRange,
            AlgebraicGeometry.ProEtale.finiteDimensional_fieldRange_toAlgHom ℓ E,
            fun x ↦ ⟨(a x).1, rfl⟩⟩)).comp
        ULift.ringEquiv.toRingHom))
    naturality _ _ _ := rfl }

/-- The inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ` of condensed rings, for a finite extension `E` of `ℚ_ℓ` embedded
in `ℚ̄_ℓ`. -/
noncomputable def padicIntegersCondensedRingToPadicAlgCl :
    padicIntegersCondensedRing.{u} ℓ E ⟶ padicAlgClCondensedRing ℓ :=
  ⟨padicIntegersToPadicAlgClRingPresheaf ℓ E⟩

/-- The inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups: the abelian sheaf
morphism underlying `Profinite.padicIntegersCondensedRingToPadicAlgCl`. -/
noncomputable def padicIntegersRingObjToPadicAlgCl :
    padicIntegersRingObj.{u} ℓ E ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntegersCondensedRingToPadicAlgCl ℓ E)

instance : IsMonHom (padicIntegersRingObjToPadicAlgCl.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntegersCondensedRingToPadicAlgCl ℓ E)))

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E` followed by the inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ` is the inclusion
`ℤ̲_ℓ ⟶ ℚ̲̄_ℓ`: both send a continuous map `S → ℤ_ℓ` to the same map into `ℚ̄_ℓ`, the embedding
`E → ℚ̄_ℓ` being a `ℚ_ℓ`-algebra map. -/
@[reassoc]
lemma padicIntRingObjToPadicIntegers_comp_padicIntegersRingObjToPadicAlgCl :
    padicIntRingObjToPadicIntegers.{u} ℓ E ≫ padicIntegersRingObjToPadicAlgCl ℓ E =
      padicIntRingObjToPadicAlgCl ℓ := by
  rw [padicIntRingObjToPadicIntegers, padicIntegersRingObjToPadicAlgCl,
    padicIntRingObjToPadicAlgCl, ← Functor.map_comp]
  congr 1
  refine Sheaf.hom_ext (NatTrans.ext (funext fun S ↦ RingCat.hom_ext (RingHom.ext
    fun a ↦ ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_)))))
  exact (IsScalarTower.algebraMap_apply ℚ_[ℓ] E (PadicAlgCl ℓ) (a.down x)).symm

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-! ### The integral Tate twists `𝒪_E(d)` -/

/-- The integral Tate twist `𝒪_{E,X}(1) = 𝒪_{E,X} ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)`: the extension of scalars of
the Tate module along the coefficient change `ℤ_ℓ,X ⟶ 𝒪_{E,X}`. -/
noncomputable def integralTateTwistOne :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) :=
  (Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicIntegers ℓ E) X)).obj
    (tateModule X ℓ)

/-- The non-negative integral Tate twists `𝒪_{E,X}(d) = 𝒪_{E,X}(1)^{⊗ d}`, the tensor powers
over `𝒪_{E,X}`, with `𝒪_{E,X}(0) = 𝒪_{E,X}`. -/
noncomputable def integralTateTwistNat :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
  | 0 => 𝟙_ _
  | d + 1 => integralTateTwistNat d ⊗ integralTateTwistOne X ℓ E

/-- The integral Tate twist `𝒪_{E,X}(d)` for `d ∈ ℤ`: the tensor power `𝒪_{E,X}(1)^{⊗ d}` for
`d ≥ 0`, and the dual `Hom_{𝒪_{E,X}}(𝒪_{E,X}(-d), 𝒪_{E,X})` for `d < 0`. -/
noncomputable def integralTateTwist :
    ℤ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
  | (d : ℕ) => integralTateTwistNat X ℓ E d
  | .negSucc d => (ihom (integralTateTwistNat X ℓ E (d + 1))).obj (𝟙_ _)

lemma integralTateTwist_natCast (d : ℕ) :
    integralTateTwist X ℓ E d = integralTateTwistNat X ℓ E d := rfl

lemma integralTateTwist_negSucc (d : ℕ) :
    integralTateTwist X ℓ E (.negSucc d) =
      (ihom (integralTateTwistNat X ℓ E (d + 1))).obj (𝟙_ _) := rfl

/-! ### Comparison with `ℚ̄_ℓ(d)` -/

variable [FiniteDimensional ℚ_[ℓ] E]

/-- The extension of scalars of `𝒪_{E,X}(1)` along `𝒪_{E,X} ⟶ ℚ̄_ℓ,X` is `ℚ̄_ℓ,X(1)`:
`ℚ̄_ℓ ⊗_{𝒪_E} (𝒪_E ⊗_{ℤ_ℓ} ℤ_ℓ(1)) ≅ ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ(1)`, by transitivity of extension of
scalars along `ℤ_ℓ,X ⟶ 𝒪_{E,X} ⟶ ℚ̄_ℓ,X`. -/
noncomputable def extendScalarsIntegralTateTwistOneIso :
    (Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)).obj
        (integralTateTwistOne X ℓ E) ≅ tateTwistOne X ℓ :=
  (Mod.extendScalarsCompIsoOfEq (CondensedRing.coefficientMap_comp_eq _ _ _
    (Profinite.padicIntRingObjToPadicIntegers_comp_padicIntegersRingObjToPadicAlgCl ℓ E)
      X)).app (tateModule X ℓ)

/-- The extension of scalars of `𝒪_{E,X}(d)` along `𝒪_{E,X} ⟶ ℚ̄_ℓ,X` is `ℚ̄_ℓ,X(d)`, for
`d ≥ 0`: extension of scalars is strong monoidal, and `ℚ̄_ℓ ⊗_{𝒪_E} 𝒪_E(1) ≅ ℚ̄_ℓ(1)`. -/
noncomputable def extendScalarsIntegralTateTwistNatIso :
    (d : ℕ) → (Mod.extendScalars
        (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)).obj
        (integralTateTwistNat X ℓ E d) ≅ tateTwistNat X ℓ d
  | 0 =>
    letI := Mod.extendScalarsMonoidal
      (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)
    (Functor.Monoidal.εIso _).symm
  | d + 1 =>
    letI := Mod.extendScalarsMonoidal
      (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)
    (Functor.Monoidal.μIso _ _ _).symm ≪≫
      tensorIso (extendScalarsIntegralTateTwistNatIso d)
        (extendScalarsIntegralTateTwistOneIso X ℓ E)

end AlgebraicGeometry.ProEtale
