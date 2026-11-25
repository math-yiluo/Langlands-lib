/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateBoundedBelowRestricted

/-! # The bounded-below completed-to-native proper scalar mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- The completed-to-native proper scalar mate is invertible on bounded-below inputs.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 5.3(1);
the proper factor in steps 3--4 of the native compact-support scalar-mate plan.
(blueprint: lem-sf-native-proper-scalar-mate-bounded-below).

Proof: identify the completed integral coefficient ring with the continuous integral
ring using its normalized finite quotient projections. Its map to native coefficients
factors as the localization to the finite rational coefficient field followed by that
field's inclusion into the locally finite algebraic-closure coefficient ring. Transport
module sheaves through the internal/section equivalences. The first proper comparison
is the localizedDirectImageComparison of HRS Lemma 5.3(1); it is invertible because the
input is bounded below and a proper morphism is quasi-compact and quasi-separated.
The localization is flat, so its scalar extension preserves the input's lower bound.
Apply the bounded proper push comparison for the finite field's inclusion into the
algebraic closure to that scalar-extended object. Identify the native ring with the
finite-field sheaf colimit, normalized on each finite-field function. Under these
identifications the two comparisons are the scalar-adjunction mates of the canonical
restriction/direct-image squares. The balanced scalar associator identifies successive
extensions with extension along the composite. Pasting those squares, and the mate
unit/counit equations, identifies the composite comparison with properComparison a g.
The assumption on a.map identifies its map with this normalized composite for every
coefficient presentation. All transport and associativity maps are isomorphisms; the
two proper comparisons are invertible, hence so is the specified mate. This argument
uses no constructibility, completeness, finite Tor condition, field of definition of
the schemes, or open immersion. Identity morphisms, empty schemes and zero inputs use
the same normalized unit equations. -/
theorem native_proper_scalar_mate_bounded_below
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    {U V : Scheme.{u}} (g : U ⟶ V) [IsProper g]
    (M : DerivedCategory (pbcModules U
      ((PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).ring U)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((PurCompactSupport.properComparison a g).app M) := by
  have hrestricted := native_proper_scalar_mate_bounded_below_restricted
    l E a ha g M hM
  let F := pbcRestrict (a.map V)
  have hF : F.ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (a.map V)).2.2
  haveI : F.ReflectsIsomorphisms := hF
  haveI : F.mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun {X Y} f hf => ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro q
    have hq : IsIso (F.map ((DerivedCategory.homologyFunctor _ q).map f)) := by
      have := (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso q) f).2
        (by rw [Functor.comp_map]; infer_instance)
      exact this
    exact isIso_of_reflects_iso _ F
  haveI : IsIso (F.mapDerivedCategory.map
      ((PurCompactSupport.properComparison a g).app M)) := hrestricted
  exact isIso_of_reflects_iso _ F.mapDerivedCategory

end WeilConjectures.LocallyFiniteAdicCompactSupport
