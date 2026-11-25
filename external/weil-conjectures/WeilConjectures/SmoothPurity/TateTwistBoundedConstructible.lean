/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!

# The shifted Tate twists as bounded constructible complexes

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. For a separated
`k`-scheme of finite type `X` (an object of `Over (Spec (.of k))`), the shifted Tate twist
`ℚ̄_ℓ,X(d)[n]` of `WeilConjectures.TateTwist.ProEtale` is a bounded constructible complex
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived`), hence an
object `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleTateTwist` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. These are the targets of the smooth orientation of
`WeilConjectures.SmoothPurity.Defs`; they are stated here, before the construction of the
orientation, so that the construction can use them.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Constructibility of the Tate twists -/

section TateTwist

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` of a separated `k`-scheme of finite type, on which `ℓ`
is invertible, is bounded constructible. -/
lemma boundedConstructible_tateTwistDerived (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      ((shiftFunctor _ n).obj (tateTwistDerived X.left ℓ d)) := by
  have : NeZero (ℓ : k) :=
    ⟨fun h ↦ (Fact.out : ringChar k ≠ ℓ)
      (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h)).resolve_left
        CharP.ringChar_ne_one)⟩
  have := isNoetherian_of_locallyOfFiniteType X.hom
  exact ObjectProperty.le_shift
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) n _
    (CondensedRing.boundedConstructible_singleFunctor_zero_obj _ _
      (isLocallyFree_tateTwist ℓ X.hom d).isConstructibleModuleObject)

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]`, as a bounded constructible complex. -/
noncomputable def boundedConstructibleTateTwist (d n : ℤ) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X.left ℓ d),
    boundedConstructible_tateTwistDerived ℓ X d n⟩

end TateTwist

/-- The Tate twist `ℚ̄_ℓ,X(0)`, placed in degree `0`, is the unit of `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistDerivedZeroIso (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    tateTwistDerived T ℓ 0 ≅ 𝟙_ _ :=
  DerivedCategory.singleFunctorObjUnitIso _

end AlgebraicGeometry.ProEtale.CondensedRing
