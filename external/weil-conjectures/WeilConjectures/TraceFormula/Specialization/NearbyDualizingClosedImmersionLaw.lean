/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingClosedImmersion
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap

/-!

# The closed-immersion law of the dualizing maps: concrete trace identities

This file provides concrete inputs of the closed-immersion law
`θ_{Z'} ∘ Ψ_{Z'}(ρ) = ρ' ∘ Ri₂^!(θ_Z) ∘ β_i(ω_{X₁})` of the dualizing maps of trait models over a
generic base (blueprint `sec-Base-change-for-nearby-cycles` (4), see
`CategoryTheory.closedImmersionLaw_aux`):

* the composition of traces `tr_Y ∘ Ra_{Y*}(ρ) = tr_X ∘ Ra_{X*}(Ri_* Ri^! ω_X ⟶ ω_X)` for a proper
  `i : Y ⟶ X` of proper `k`-schemes, stated with `NearbyCyclesModel.trace`, `dualizingComplex` and
  `upperShriekDualizingComplexIso`
  (`ProEtale.CondensedRing.lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace`);
* the components of the composition isomorphisms `Rf_* ⋙ Rg_* ≅ Rh_*` on the ambient derived
  categories (`ProEtale.CondensedRing.boundedConstructibleLowerStarCompOfEq_inv_app_hom`).

## Implementation notes

The terms `NearbyCyclesModel.trace`, `dualizingComplex` and `upperShriekDualizingComplexIso` are
definitionally the counit of `Ra_! ⊣ Ra^!`, `Ra^! ℚ̄_ℓ` and the composition isomorphism of
`Ra^!`, but their bodies carry auxiliary proofs (`trace._proof_2`, …) inside the instances of the
unit `ℚ̄_ℓ`, different from those of terms elaborated elsewhere. Checking such an identification
inside a large statement makes the kernel unfold the bounded constructible functors and time out
(even through `exact_mod_proofs`/`cast_proofs`). The composition of traces is therefore proved
for *arbitrary* objects `ωX`, `ωY`, traces `tX`, `tY` and isomorphism `ρ`, given by equalities
(`ProEtale.CondensedRing.lowerStar_map_comp_trace_of_heq`), which are then instantiated by small
`rfl` lemmas checked in isolation.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y P : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The composition isomorphism `Rp_* ⋙ Ra₁_* ≅ Ra₃_*` on bounded constructible complexes, for
`p ≫ a₁ = a₃`, is the conjugate of the composition isomorphism of the derived pullbacks: the
inverse version of `boundedConstructibleLowerStarCompOfEq_hom_app_hom`. -/
lemma boundedConstructibleLowerStarCompOfEq_inv_app_hom (p : X ⟶ Y) (a₁ : Y ⟶ P) (a₃ : X ⟶ P)
    (wa : p ≫ a₁ = a₃) (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerStarCompOfEq ℓ p a₁ wa).inv.app M).hom =
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction _ a₃.left)
        ((derivedUpperStarLowerStarAdjunction _ a₁.left).comp
          (derivedUpperStarLowerStarAdjunction _ p.left))
        (leftDerivedUpperStarCompOfEq _ (congrArg CommaMorphism.left wa)).symm).hom.app
          M.obj := by
  subst wa
  have e : (boundedConstructibleLowerStarCompOfEq ℓ p a₁ rfl).inv.app M =
      (boundedConstructibleLowerStarComp ℓ p a₁).inv.app M := by
    simp [boundedConstructibleLowerStarCompOfEq]
  rw [e]
  exact boundedConstructibleLowerStarComp_inv_app_hom ℓ p a₁ M

/-- **Composition of traces, for arbitrary representatives**: for proper `i : Y ⟶ X`,
`a_X : X ⟶ P` and `a_Y = i ≫ a_X`, objects `ωX = Ra_X^! U`, `ωY = Ra_Y^! U`, traces `tX`, `tY`
equal to the counits of `Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`, and `ρ : Ri^! ωX ⟶ ωY` equal to
the composition isomorphism, `tY ∘ Ra_{Y*}(ρ) = tX ∘ Ra_{X*}(Ri_* Ri^! ωX ⟶ ωX)` through
`Ra_{Y*} ≅ Ra_{X*} Ri_*`. The equalities are hypotheses so that the instantiation never has to
unfold `ωX`, `tX`, `ρ` inside the statement (see the implementation notes). -/
lemma lowerStar_map_comp_trace_of_heq (i : Y ⟶ X) (aX : X ⟶ P) {aY : Y ⟶ P}
    (w : i ≫ aX = aY) [IsProper i.left] [IsProper aX.left] [IsProper aY.left]
    {U : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ωX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ωY : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (hωX : ωX = (boundedConstructibleUpperShriek ℓ aX).obj U)
    (hωY : ωY = (boundedConstructibleUpperShriek ℓ aY).obj U)
    (tX : (boundedConstructibleLowerStar ℓ aX).obj ωX ⟶ U)
    (htX : HEq tX ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aX).inv.app
      ((boundedConstructibleUpperShriek ℓ aX).obj U) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ aX).counit.app U))
    (tY : (boundedConstructibleLowerStar ℓ aY).obj ωY ⟶ U)
    (htY : HEq tY ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aY).inv.app
      ((boundedConstructibleUpperShriek ℓ aY).obj U) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ aY).counit.app U))
    (ρ : (boundedConstructibleUpperShriek ℓ i).obj ωX ⟶ ωY)
    (hρ : HEq ρ (((boundedConstructibleUpperShriekComp_padicAlgCl ℓ i aX).app U).inv ≫
      eqToHom (congrArg (fun a ↦ (boundedConstructibleUpperShriek ℓ a).obj U) w))) :
    (boundedConstructibleLowerStar ℓ aY).map ρ ≫ tY =
      (boundedConstructibleLowerStarCompOfEq ℓ i aX w).inv.app
          ((boundedConstructibleUpperShriek ℓ i).obj ωX) ≫
        (boundedConstructibleLowerStar ℓ aX).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).inv.app
              ((boundedConstructibleUpperShriek ℓ i).obj ωX) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ i).counit.app ωX) ≫ tX := by
  subst hωX hωY w
  obtain rfl := eq_of_heq htX
  obtain rfl := eq_of_heq htY
  obtain rfl := eq_of_heq hρ
  have e : (boundedConstructibleLowerStarCompOfEq ℓ i aX rfl).inv.app
      ((boundedConstructibleUpperShriek ℓ i).obj ((boundedConstructibleUpperShriek ℓ aX).obj U)) =
      (boundedConstructibleLowerStarComp ℓ i aX).inv.app
        ((boundedConstructibleUpperShriek ℓ i).obj
          ((boundedConstructibleUpperShriek ℓ aX).obj U)) := by
    simp [boundedConstructibleLowerStarCompOfEq]
  rw [e, eqToHom_refl, Category.comp_id]
  exact map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app
    (boundedConstructibleUpperShriekAdjunction ℓ i)
    (boundedConstructibleUpperShriekAdjunction ℓ aX)
    (boundedConstructibleUpperShriekAdjunction ℓ (i ≫ aX))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ i aX)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aX)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (i ≫ aX))
    (boundedConstructibleLowerStarComp ℓ i aX)
    (fun K ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ i aX K) U

omit [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] in
/-- The dualizing complex is `Ra^! ℚ̄_ℓ` for the structure morphism `a = toPoint Z`. -/
lemma dualizingComplex_eq_upperShriek_obj (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] :
    dualizingComplex ℓ Z = (boundedConstructibleUpperShriek ℓ (toPoint Z)).obj (𝟙_ _) :=
  rfl

omit [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] in
/-- The trace of a proper `k`-scheme is the counit of `Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`. -/
lemma NearbyCyclesModel.trace_heq (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left] :
    HEq (NearbyCyclesModel.trace ℓ Z)
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).inv.app
        ((boundedConstructibleUpperShriek ℓ (toPoint Z)).obj (𝟙_ _)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)) :=
  HEq.rfl

omit [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] in
/-- The composition isomorphism `Ri^! ω_X ≅ ω_Y` is the composition isomorphism of the
exceptional inverse images at `ℚ̄_ℓ`. -/
lemma upperShriekDualizingComplexIso_hom_heq (i : Y ⟶ X) :
    HEq (upperShriekDualizingComplexIso ℓ i).hom
      (((boundedConstructibleUpperShriekComp_padicAlgCl ℓ i (toPoint X)).app (𝟙_ _)).inv ≫
        eqToHom (congrArg (fun a ↦ (boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _))
          (comp_toPoint i))) :=
  HEq.rfl

omit [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] in
/-- **Composition of traces** for a proper morphism `i : Y ⟶ X` of proper `k`-schemes:
`tr_Y ∘ Ra_{Y*}(ρ) = tr_X ∘ Ra_{X*}(Ri_* Ri^! ω_X ⟶ ω_X)` through `Ra_{Y*} ≅ Ra_{X*} Ri_*`, for
the composition isomorphism `ρ : Ri^! ω_X ≅ ω_Y` (`upperShriekDualizingComplexIso`). -/
lemma lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace (i : Y ⟶ X) [IsProper i.left]
    [IsProper (toPoint X).left] [IsProper (toPoint Y).left] :
    (boundedConstructibleLowerStar ℓ (toPoint Y)).map (upperShriekDualizingComplexIso ℓ i).hom ≫
        NearbyCyclesModel.trace ℓ Y =
      (boundedConstructibleLowerStarCompOfEq ℓ i (toPoint X) (comp_toPoint i)).inv.app
          ((boundedConstructibleUpperShriek ℓ i).obj (dualizingComplex ℓ X)) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).inv.app
              ((boundedConstructibleUpperShriek ℓ i).obj (dualizingComplex ℓ X)) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ i).counit.app (dualizingComplex ℓ X)) ≫
        NearbyCyclesModel.trace ℓ X :=
  lowerStar_map_comp_trace_of_heq ℓ i (toPoint X) (comp_toPoint i)
    (dualizingComplex_eq_upperShriek_obj ℓ X) (dualizingComplex_eq_upperShriek_obj ℓ Y) _
    (NearbyCyclesModel.trace_heq ℓ X) _ (NearbyCyclesModel.trace_heq ℓ Y) _
    (upperShriekDualizingComplexIso_hom_heq ℓ i)

end AlgebraicGeometry.ProEtale.CondensedRing
