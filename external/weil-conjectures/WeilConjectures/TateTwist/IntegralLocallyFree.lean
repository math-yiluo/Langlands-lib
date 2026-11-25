/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.MapIhomUnit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.TateTwist.Integral
public import WeilConjectures.TateTwist.LocallyFree

/-!
# The integral Tate twists are locally free of rank one

Let `X` be a scheme over a field `k` in which the prime `ℓ` is invertible, and `E ⊆ ℚ̄_ℓ` a
finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. Every integral Tate twist `𝒪_{E,X}(d)`,
`d ∈ ℤ`, is a locally free `𝒪_{E,X}`-module of rank one
(`AlgebraicGeometry.ProEtale.isLocallyFree_integralTateTwist`): over the pro-étale cover
`X ×_k Spec kˢᵉᵖ ⟶ X`, a compatible system of primitive `ℓⁿ`-th roots of unity of `kˢᵉᵖ`
trivializes the Tate module `ℤ_ℓ(1)` (`ProEtale.upperStarMapModTateModuleIsoUnit`), hence
`𝒪_E(1) = 𝒪_E ⊗_{ℤ_ℓ} ℤ_ℓ(1)` (`ProEtale.upperStarMapModExtendScalarsIsoUnit`), hence all its
tensor powers and their duals. This is the argument of `WeilConjectures.TateTwist.LocallyFree`,
with `𝒪_E` in place of `ℚ̄_ℓ`.

Consequently:

* `𝒪_{E,X}(d)` placed in degree `0` is a bounded constructible complex
  (`AlgebraicGeometry.ProEtale.boundedConstructible_singleFunctor_integralTateTwist`), an object
  of `Dᵇc(X)⟦𝒪_E⟧` (`AlgebraicGeometry.ProEtale.integralTateTwistBoundedConstructible`);
* `𝒪_{E,X}(d)` is dualizable, so extension of scalars along `𝒪_{E,X} ⟶ ℚ̄_ℓ,X` commutes with its
  dual, and `ℚ̄_ℓ ⊗_{𝒪_E} 𝒪_E(d) ≅ ℚ̄_ℓ(d)` for all `d ∈ ℤ`
  (`AlgebraicGeometry.ProEtale.extendScalarsIntegralTateTwistIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-! ### Local triviality over a cover trivializing `𝒪_E(1)` -/

section OfIso

variable {X U : Scheme.{u}} (g : U ⟶ X)

/-- If the pullback of `𝒪_{E,X}(1)` along `g` is trivial, so is the pullback of every
non-negative integral Tate twist `𝒪_{E,X}(d) = 𝒪_{E,X}(1)^{⊗ d}`. -/
noncomputable def upperStarMapModIntegralTateTwistNatIsoUnit
    (e : ((g)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).obj
        (integralTateTwistOne X ℓ E) ≅ 𝟙_ _) :
    (d : ℕ) → ((g)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).obj
        (integralTateTwistNat X ℓ E d) ≅ 𝟙_ _
  | 0 => Functor.mapUnitIsoUnit _
  | d + 1 => Functor.mapTensorObjIsoUnit _ (upperStarMapModIntegralTateTwistNatIsoUnit e d) e

variable [WeaklyEtale g]

/-- If the pullback of `𝒪_{E,X}(1)` along a weakly étale `g` is trivial, so is the pullback of
every integral Tate twist `𝒪_{E,X}(d)`, `d ∈ ℤ`: for `d < 0` it is the dual of `𝒪_{E,X}(-d)`,
and `g^*` commutes with internal homs. -/
noncomputable def upperStarMapModIntegralTateTwistIsoUnit
    (e : ((g)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).obj
        (integralTateTwistOne X ℓ E) ≅ 𝟙_ _) :
    (d : ℤ) → ((g)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).obj
        (integralTateTwist X ℓ E d) ≅ 𝟙_ _
  | (d : ℕ) => upperStarMapModIntegralTateTwistNatIsoUnit ℓ E g e d
  | .negSucc d =>
    have := isIso_ihomComparison_upperStar Ab.{u + 1} g
    Functor.mapIhomObjIsoUnit _ (upperStarMapModIntegralTateTwistNatIsoUnit ℓ E g e (d + 1))
      (Functor.mapUnitIsoUnit _)

/-- **The integral Tate twists are locally free of rank one** over any pro-étale cover over which
`𝒪_{E,X}(1)` is trivial. -/
theorem isLocallyFree_integralTateTwist_of_iso
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, Nonempty (((𝒰.f i)^*[Ab.{u + 1}].mapMod
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).obj
        (integralTateTwistOne X ℓ E) ≅ 𝟙_ _))
    (d : ℤ) :
    IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      (integralTateTwist X ℓ E d) := by
  refine ⟨𝒰, fun i ↦ ⟨1, ⟨?_⟩⟩⟩
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  exact upperStarMapModIntegralTateTwistIsoUnit ℓ E (𝒰.f i) (h i).some d ≪≫
    (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm

end OfIso

/-! ### Local freeness over a field in which `ℓ` is invertible -/

variable {k : Type u} [Field k] [NeZero (ℓ : k)] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

include f

/-- **The integral Tate twists are locally free of rank one**: for a scheme `X` over a field `k`
in which `ℓ` is invertible, every `𝒪_{E,X}(d)` is a locally free `𝒪_{E,X}`-module, trivial over
`X ×_k Spec kˢᵉᵖ`. -/
theorem isLocallyFree_integralTateTwist (d : ℤ) :
    IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      (integralTateTwist X ℓ E d) := by
  have : NeZero (ℓ : SeparableClosure k) :=
    ‹NeZero (ℓ : k)›.of_injective (algebraMap k (SeparableClosure k)).injective
  obtain ⟨ζ, hζ, hζ'⟩ := IsSepClosed.exists_isPrimitiveRoot_pow_eq (SeparableClosure k) ℓ
  refine isLocallyFree_integralTateTwist_of_iso ℓ E (sepClosureCover f) (fun _ ↦ ⟨?_⟩) d
  exact upperStarMapModExtendScalarsIsoUnit (pullback.fst f (specSepClosureHom k))
    (Profinite.padicIntRingObjToPadicIntegers ℓ E) _
    (upperStarMapModTateModuleIsoUnit (pullback.fst f (specSepClosureHom k))
      (pullback.snd f (specSepClosureHom k)) ℓ hζ hζ')

/-- **The non-negative integral Tate twists are locally free of rank one**, for a scheme over a
field in which `ℓ` is invertible. -/
theorem isLocallyFree_integralTateTwistNat (d : ℕ) :
    IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      (integralTateTwistNat X ℓ E d) :=
  isLocallyFree_integralTateTwist ℓ E f d

/-! ### Bounded constructibility -/

/-- The integral Tate twist `𝒪_{E,X}(d)`, `d ∈ ℤ`, placed in degree `0`, is a bounded
constructible complex of `𝒪_{E,X}`-modules: it is locally free, hence constructible. -/
theorem boundedConstructible_singleFunctor_integralTateTwist (d : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwist X ℓ E d)) :=
  CondensedRing.boundedConstructible_singleFunctor_zero_obj _ _
    (isLocallyFree_integralTateTwist ℓ E f d).isConstructibleModuleObject

/-- The non-negative integral Tate twist `𝒪_{E,X}(d)`, placed in degree `0`, is a bounded
constructible complex of `𝒪_{E,X}`-modules. -/
theorem boundedConstructible_singleFunctor_integralTateTwistNat (d : ℕ) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) :=
  boundedConstructible_singleFunctor_integralTateTwist ℓ E f d

open CondensedRing in
/-- The non-negative integral Tate twist `𝒪_{E,X}(d)` placed in degree `0`, as an object of the
bounded constructible derived category `Dᵇc(X)⟦𝒪_E⟧`. -/
noncomputable def integralTateTwistBoundedConstructible (d : ℕ) :
    Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d),
    boundedConstructible_singleFunctor_integralTateTwistNat ℓ E f d⟩

/-! ### Comparison with `ℚ̄_ℓ(d)` for all `d ∈ ℤ` -/

variable [FiniteDimensional ℚ_[ℓ] E]

/-- The extension of scalars of `𝒪_{E,X}(d)` along `𝒪_{E,X} ⟶ ℚ̄_ℓ,X` is `ℚ̄_ℓ,X(d)`, for every
`d ∈ ℤ`. For `d ≥ 0` this is `ProEtale.extendScalarsIntegralTateTwistNatIso`; for `d < 0`,
`𝒪_{E,X}(-d)` is locally free, hence dualizable, and the strong monoidal extension of scalars
commutes with the duals of dualizable objects. -/
noncomputable def extendScalarsIntegralTateTwistIso :
    (d : ℤ) → (Mod.extendScalars
        (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)).obj
        (integralTateTwist X ℓ E d) ≅ tateTwist X ℓ d
  | (d : ℕ) => extendScalarsIntegralTateTwistNatIso X ℓ E d
  | .negSucc d =>
    letI := Mod.extendScalarsMonoidal
      (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)
    Functor.mapIhomUnitIsoOfIsDualizable _
        (isLocallyFree_integralTateTwistNat ℓ E f (d + 1)).isDualizable ≪≫
      ((internalHom.mapIso (extendScalarsIntegralTateTwistNatIso X ℓ E (d + 1)).op).app
        (𝟙_ _)).symm

end AlgebraicGeometry.ProEtale
