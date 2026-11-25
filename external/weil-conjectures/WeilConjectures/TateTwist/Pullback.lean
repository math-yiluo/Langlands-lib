/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.MapIhomUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.TateTwist.TateModuleUpperStar

/-!
# Pullback of the Tate twists

Let `g : X' ⟶ X` be a morphism of schemes, with `X` over a field `k` in which the prime `ℓ` is
invertible. The pullback of module objects over `ℚ̄_ℓ` sends the Tate twists of `X` to the Tate
twists of `X'`:

* `AlgebraicGeometry.ProEtale.upperStarTateTwistNatIso`: `g^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X'(d)` for `d ≥ 0`,
  by induction from `g^* ℚ̄_ℓ,X(1) ≅ ℚ̄_ℓ,X'(1)`
  (`AlgebraicGeometry.ProEtale.upperStarTateTwistOneIso`), the pullback being strong monoidal;
* `AlgebraicGeometry.ProEtale.upperStarTateTwistIso`: `g^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X'(d)` for `d ∈ ℤ`; for
  `d < 0`, `ℚ̄_ℓ,X(d)` is the dual of the dualizable (locally free) `ℚ̄_ℓ,X(-d)`
  (`AlgebraicGeometry.ProEtale.isLocallyFree_tateTwist`), and strong monoidal functors preserve
  duals of dualizable objects (`CategoryTheory.Functor.mapIhomUnitIsoOfIsDualizable`);
* `AlgebraicGeometry.ProEtale.upperStarTateTwistDerivedIso`: `Lg^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X'(d)` in the
  derived categories: the pullback of module objects is exact, so its total left derived functor
  is computed levelwise (`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`) and
  commutes with complexes concentrated in degree `0`;
* `AlgebraicGeometry.ProEtale.upperStarShiftTateTwistDerivedIso`: the shifted version
  `Lg^* ℚ̄_ℓ,X(d)[n] ≅ ℚ̄_ℓ,X'(d)[n]`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : k)] {X X' : Scheme.{u}}
  (g : X' ⟶ X)

/-- **The pullback of `ℚ̄_ℓ(d)` is `ℚ̄_ℓ(d)`** for `d ≥ 0`: `g^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X'(d)`, the
pullback being strong monoidal. -/
noncomputable def upperStarTateTwistNatIso (f : X ⟶ Spec (.of k)) :
    (d : ℕ) → (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).obj
      (tateTwistNat X ℓ d) ≅ tateTwistNat X' ℓ d
  | 0 => (Functor.Monoidal.εIso _).symm
  | d + 1 => (Functor.Monoidal.μIso _ _ _).symm ≪≫
      (upperStarTateTwistNatIso f d ⊗ᵢ upperStarTateTwistOneIso ℓ g f)

/-- `ℚ̄_ℓ,X(d)` is dualizable for `d ≥ 0`, being locally free. -/
lemma isDualizable_tateTwistNat (f : X ⟶ Spec (.of k)) (d : ℕ) :
    IsDualizable (tateTwistNat X ℓ d) :=
  (isLocallyFree_tateTwist ℓ f d).isDualizable

/-- The pullback of the dual `ℚ̄_ℓ,X(-d) = [ℚ̄_ℓ,X(d), ℚ̄_ℓ,X]` of `ℚ̄_ℓ,X(d)`, `d ≥ 0`, is the
dual of `ℚ̄_ℓ,X'(d)`: the strong monoidal pullback preserves duals of dualizable objects. -/
noncomputable def upperStarIhomTateTwistNatIso (f : X ⟶ Spec (.of k)) (d : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).obj
        ((ihom (tateTwistNat X ℓ d)).obj (𝟙_ _)) ≅ (ihom (tateTwistNat X' ℓ d)).obj (𝟙_ _) :=
  Functor.mapIhomUnitIsoOfIsDualizable _ (isDualizable_tateTwistNat ℓ f d) ≪≫
    MonoidalClosed.ihomIsoOfIsoLeft (upperStarTateTwistNatIso ℓ g f d) _

/-- **The pullback of `ℚ̄_ℓ(d)` is `ℚ̄_ℓ(d)`**: `g^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X'(d)` for `d ∈ ℤ`. For
`d < 0`, `ℚ̄_ℓ,X(d)` is the dual of the locally free, hence dualizable, `ℚ̄_ℓ,X(-d)`, and the
strong monoidal pullback preserves duals of dualizable objects. -/
noncomputable def upperStarTateTwistIso (f : X ⟶ Spec (.of k)) :
    (d : ℤ) → (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).obj
      (tateTwist X ℓ d) ≅ tateTwist X' ℓ d
  | (d : ℕ) => upperStarTateTwistNatIso ℓ g f d
  | .negSucc d => upperStarIhomTateTwistNatIso ℓ g f (d + 1)

/-- **The derived pullback of `ℚ̄_ℓ(d)` is `ℚ̄_ℓ(d)`**: `Lg^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X'(d)` in the derived
categories of module objects, for `g : X' ⟶ X` with `X` over a field `k` in which `ℓ` is
invertible. The pullback of module objects is exact, so its total left derived functor is the
levelwise pullback, which commutes with complexes concentrated in degree `0`. -/
noncomputable def upperStarTateTwistDerivedIso (f : X ⟶ Spec (.of k)) (d : ℤ) :
    L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived X ℓ d) ≅
      tateTwistDerived X' ℓ d :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (upperStarTateTwistIso ℓ g f d)

/-- **The derived pullback of the shifted Tate twist** `ℚ̄_ℓ,X(d)[n]` is `ℚ̄_ℓ,X'(d)[n]`, the
derived pullback commuting with the shifts. -/
noncomputable def upperStarShiftTateTwistDerivedIso (f : X ⟶ Spec (.of k)) (d n : ℤ) :
    L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) ≅
      (shiftFunctor _ n).obj (tateTwistDerived X' ℓ d) :=
  (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (upperStarTateTwistDerivedIso ℓ g f d)

end AlgebraicGeometry.ProEtale
