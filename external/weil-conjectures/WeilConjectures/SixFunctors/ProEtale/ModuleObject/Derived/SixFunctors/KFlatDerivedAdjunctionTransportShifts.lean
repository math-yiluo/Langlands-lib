/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LeftDerivedExactComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Transport and fixed shifts of the K-flat module derived adjunction

Source: Stacks Project, derived.tex, Tags 0DVC and 0FND; blueprint main-20261015,
proper base change rational proof, paragraph (3)
(blueprint: lem-sfb-kflat-derived-adjunction-transport-shifts).

The two adjunctions below are the specified constructions from the same ordinary module
adjunction. Both use `rightDerivedFunctorUnit` as their right derived comparison. The
comparison and the pullback and pushforward shift structures are the existing canonical
ones recorded by `def-sfb-module-derived-comparison-shifts` in
`ModuleDerivedFunctorCompositorShifts`; no adjoint shift is installed here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The specified K-flat/K-injective adjunction is the transport of the canonical
exact-left/K-injective-right adjunction, and its unit and counit commute with all fixed
integer shifts. Source: Stacks Project, derived.tex, Tags 0DVC and 0FND, canonical derived
adjunction; blueprint proper base change rational proof, paragraph (3)
(blueprint: lem-sfb-kflat-derived-adjunction-transport-shifts).

Proof: (1) Apply `lem-sfb-abstract-derived-unit-factorization` to the two derived-unit
lifts, using the termwise adjunction of `lem-weil-pbc-termwise-adjunction-homotopy` and
the same right comparison beta. The exact factorization is invertible by
`situation-conventions`; the K-flat factorization is its
composite with the canonical exact comparison. Postcomposing either invertible
factorization with the right derived functor gives a universal left-derived pair by
the fully faithful descent of `lem-weil-pbc-localization-universal-property`.
(2) Substitute alphaP = c followed by alphaA in the two unit equations and cancel
G(alphaA). Localization faithfulness extends the resulting equality from localized
complexes to every derived object. Compose with G(c inverse) to obtain the unit formula.
(3) The proposed counit c followed by epsilonA has transpose the identity, by the unit
formula and the right triangle identity for the exact-left adjunction. The specified
counit has the same transpose; injectivity of the adjunction bijection identifies them.
The unit and counit formulas determine transport of the whole adjunction.
(4) `lem-sp-canonical-right-derived-adjunction-shift` gives shift compatibility for the
exact-left adjunction with the fixed K-injective shifts. The pullback shift is transported
along c. In the unit square substitute step (2), use naturality of the pushforward shift
along c and the transport equation, then cancel shifted G(c). In the counit square
substitute step (3), use naturality of c along the pushforward shift and the same transport
equation, and finish with the exact-left counit square. This works for every integer,
including zero and negative integers, with the original shift on G throughout. -/
theorem kflat_derived_adjunction_transport_shifts :
    (∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R.X Y)),
      (derivedUpperStarLowerStarAdjunction R.X f).unit.app M =
        (upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction.unit.app M ≫
          (moduleObjectDerivedPushforward R.X f).map
            ((modulePullbackExactComparison R.X f).inv.app M)) ∧
    (∀ N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X)),
      (derivedUpperStarLowerStarAdjunction R.X f).counit.app N =
        (modulePullbackExactComparison R.X f).hom.app
            ((moduleObjectDerivedPushforward R.X f).obj N) ≫
          (upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction.counit.app
            N) ∧
    Adjunction.CommShift
      (F := moduleObjectDerivedPullback R.X f) (G := moduleObjectDerivedPushforward R.X f)
      (derivedUpperStarLowerStarAdjunction R.X f) ℤ := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let L := upperStar R.X f
      let P := moduleObjectDerivedPullback R.X f
      let G := moduleObjectDerivedPushforward R.X f
      let A := L.mapDerivedCategory
      let aP : P ⊣ G := derivedUpperStarLowerStarAdjunction R.X f
      let aA : A ⊣ G :=
        (upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction
      let c : P ≅ A := modulePullbackExactComparison R.X f
      have htransport : aP = aA.ofNatIsoLeft c.symm := by
        exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
          L.leftDerivedFunctorIsoMapDerivedCategory
          L.leftDerivedFunctorIsoMapDerivedCategory_hom_fac.symm
      refine ⟨?_, ?_, ?_⟩
      · intro M
        change aP.unit.app M = _
        rw [htransport]
        rfl
      · intro N
        change aP.counit.app N = _
        rw [htransport]
        rfl
      · change Adjunction.CommShift (F := P) (G := G) aP ℤ
        have : aA.CommShift ℤ :=
          canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction R.X f)
        have : NatTrans.CommShift (F₁ := A) (F₂ := P) c.symm.hom ℤ :=
          Functor.CommShift.ofIso_compatibility c.symm ℤ
        rw [htransport]
        exact Adjunction.commShift_ofNatIsoLeft (F := A) (G := P) (H := G) aA c.symm

end AlgebraicGeometry.ProEtale.CondensedRing
