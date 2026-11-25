/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
public import WeilConjectures.Compactification.RefinementOfIsPullback

/-! # Total-derived exchange and a normalized boundary refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- Pasting the specified compact-support mate with one normalized boundary refinement.

Source: blueprint proposition-composition-base-change-rf-shriek--4, proof clause (3);
lem-sfb-total-derived-cartesian-compact-support, the refinement-pasting equation.
(blueprint: lem-sfb-total-derived-boundary-exchange).

Proof: the boundary equality says the square formed by the two distinguished opens,
with identity on their common source, is Cartesian. It remains Cartesian after the
supplied base change. Transpose the normalized isomorphisms e and e' under the two
open adjunctions. Their normalization equations identify these adjuncts with the open
units followed by the inverse of the proper restriction comparison. That comparison
is invertible on extension by zero: the direct-image restriction to that open is
sectionwise the identity, and exact restriction of a K-injective resolution computes
the derived restriction there. The open units are invertible since extension by zero
is fully faithful. Thus the equations uniquely determine e and e'.
The canonical pullback composition comparisons satisfy the cocycle law. Taking
mates under the proper adjunctions gives horizontal pasting, with pushComp as its
compositor. Taking mates under the open adjunctions gives the same pasting for the
inverse open exchange. Substitute the two normalization equations, apply naturality
of the proper counits, and cancel the open unit and restriction isomorphisms. The
result equates the proper exchange followed by the two open mates on both paths.
After applying the final proper pushforward, its compositors cancel those in
refinementIso, giving the displayed component identity. Only the inverse open
exchanges require invertibility; no proper-exchange invertibility, arithmetic,
localizing hypothesis, density, or comparison family is used. In particular the
argument includes zero objects, empty opens, and nondense compactifications. -/
theorem normalizedBoundaryExchange
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c d : Compactification f)
    (r : c.Refinement d) (hr : r.hom ⁻¹ᵁ d.i.opensRange = c.i.opensRange)
    (ho : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.isPullback_i_ofIsPullback sq).toCommSq))
    (K : Ambient Λ X)
    (e : (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K))
    (he : (openAdjunction Λ d.i).homEquiv _ _ e.hom ≫
      refinementRestriction Λ r K = (openAdjunction Λ c.i).unit.app K)
    (e' : (extend Λ (d.ofIsPullback sq).i).obj ((pull Λ u').obj K) ≅
      (push Λ (r.ofIsPullback sq).hom).obj
        ((extend Λ (c.ofIsPullback sq).i).obj ((pull Λ u').obj K)))
    (he' : (openAdjunction Λ (d.ofIsPullback sq).i).homEquiv _ _ e'.hom ≫
      refinementRestriction Λ (r.ofIsPullback sq) ((pull Λ u').obj K) =
        (openAdjunction Λ (c.ofIsPullback sq).i).unit.app ((pull Λ u').obj K)) :
    (pull Λ v).map (refinementIso Λ r K e).hom ≫ (baseChange Λ d sq hd).app K =
      (baseChange Λ c sq ho).app K ≫
        (refinementIso Λ (r.ofIsPullback sq) ((pull Λ u').obj K) e').hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
