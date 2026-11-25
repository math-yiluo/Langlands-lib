/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.FinitePresentation
public import WeilConjectures.TraceFormula.Specialization.BoundedConstructibleFiniteComplement
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessQuasiFinite

/-!

# Deligne's finiteness criterion for nearby cycles of proper models

Let `S = Spec k'⟦t⟧` be the strictly henselian trait (`k'` separably closed, `ℓ ≠ char k'`) and
`q : T ⟶ S` a proper morphism. For every bounded constructible `ℚ̄_ℓ`-complex `B` on `T`, the
cohomology `RΓ(T_s, Ψ_T B)` of the geometric nearby cycles of the standard model of `T`
(`NearbyCyclesModel.traitStdModel`) is bounded constructible on `Spec k'`
(`NearbyCyclesModel.boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper`):
by the proper exchange along `q`, `RΓ(T_s, Ψ_T B) ≅ Ψ_S (Rq_* B)`, where `Rq_* B` is bounded
constructible (finiteness of proper direct images) and so are the nearby cycles of the trait
(`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`).

This is the global input of Deligne's criterion (SGA 4½, [Th. finitude], proof of 3.2), which
then reduces the bounded constructibility of `Ψ_T B` to its local form on the coordinate
fibres of the special fibre
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isProper_of_coordinates`,
from `ProEtale.CondensedRing.boundedConstructible_of_forall_exists_coordinates_of_lowerStar`).

For a separated morphism `q : T ⟶ S` of finite type, a Nagata compactification `T ⊆ P` over `S`
reduces the bounded constructibility of `Ψ_T B` to that of `Ψ_P (j_! B)`, since nearby cycles
commute with the open immersion `j`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_compactification`), hence to
the coordinate criterion on the proper special fibre `P_s`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_coordinates`), or to its
pointwise form at the points over the generic points of the coordinate lines
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint`).

The proper exchange and the finiteness of proper direct images are `sorry`ed upstream.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k').Prime] in
/-- **Cohomology of the nearby cycles of a proper scheme over the trait** (SGA 4½,
[Th. finitude], proof of 3.2): for a proper morphism `q : T ⟶ S` to the trait and a bounded
constructible complex `B` on `T`, the cohomology `RΓ(T_s, Ψ_T B)` of the geometric nearby cycles
of the standard model of `T` is bounded constructible on `Spec k'`. By the proper exchange along
`q`, it is `Ψ_S (Rq_* B)`, the nearby cycles of the trait of the bounded constructible complex
`Rq_* B`. -/
theorem boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper {T : Scheme.{u}}
    (q : T ⟶ trait k') [IsProper q]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k')))
      ((R(((traitStdSpecialFibre q).hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B)) := by
  let M := traitStdModel q
  have hj : IsPullback M.j (pullback.snd q (traitGenericPoint k')) q (traitGenericPoint k') :=
    IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre q).hom q (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let ψ : M.geometric.Hom (traitSelfModel k').geometric q
      (pullback.snd q (traitClosedPoint k')) :=
    { total := q
      generic := pullback.snd q (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  have hiso :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric (X' := traitStdSpecialFibre q)
      (Y' := Over.mk (𝟙 (Spec (.of k')))) (M := M) (N := traitSelfModel k') ψ
      (isTraitModel_traitStdModel _) (isTraitModel_traitSelfModel k') rfl hj.flip hi B hB
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have h₁ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of k')))
      (((traitSelfModel k').geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((q)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B)) :=
    preservesBoundedConstructible_traitSelfModel k' _
      (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj ℓ
        (traitToBase k' k') q B hB)
  exact (boundedConstructible _).prop_of_iso (@asIso _ _ _ _ _ hiso) h₁

/-- **Deligne's criterion for a proper model over the trait** (SGA 4½, [Th. finitude], proof of
3.2): let `q : T ⟶ S` be proper and `B` a bounded constructible complex on `T`. Suppose that
every point of the special fibre `T_s` has an open neighbourhood `U` with finitely many
coordinates `bᵢ : U ⟶ 𝔸¹_{k'}`, jointly detecting closed points, such that `Ψ_T B` is bounded
constructible on `U` away from the preimage `bᵢ⁻¹(Fᵢ)` of a finite set `Fᵢ` of closed points.
Then `Ψ_T B` is bounded constructible: its cohomology `RΓ(T_s, Ψ_T B)` is
(`NearbyCyclesModel.boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper`) and
`T_s` is proper over `k'`
(`ProEtale.CondensedRing.boundedConstructible_of_forall_exists_coordinates_of_lowerStar`). -/
theorem boundedConstructible_nearbyCycles_traitStdModel_of_isProper_of_coordinates
    {T : Scheme.{u}} (q : T ⟶ trait k') [IsProper q]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hB : boundedConstructible _ B)
    (H : ∀ y : (traitStdSpecialFibre q).left, ∃ (U : (traitStdSpecialFibre q).left.Opens)
      (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))),
      (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (F : Finset 𝔸(ULift.{u} (Fin 1); Spec (.of k'))) (hF : ∀ x ∈ F, IsClosed {x}),
        boundedConstructible _
          (L(((b i ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
              (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
                B)))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre q).left)
      (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have : IsProper (traitStdSpecialFibre q).hom :=
    inferInstanceAs (IsProper (pullback.snd q (traitClosedPoint k')))
  exact boundedConstructible_of_forall_exists_coordinates_of_lowerStar
    (traitStdSpecialFibre q)
    (boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper q hB) H

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Reduction to a compactification**: let `q : T ⟶ S` factor as an open immersion
`j : T ⟶ P` followed by a morphism `p : P ⟶ S`. If the geometric nearby cycles `Ψ_P (j_! B)` of
the extension by zero of a complex `B` on `T` are bounded constructible, so are those of `B`:
nearby cycles commute with the open immersion `j`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`), so
`Ψ_T B ≅ Ψ_T (Lj^* j_! B) ≅ Lj_s^* Ψ_P (j_! B)`. -/
theorem boundedConstructible_nearbyCycles_traitStdModel_of_compactification
    {T P : Scheme.{u}} (q : T ⟶ trait k') (j : T ⟶ P) [IsOpenImmersion j] (p : P ⟶ trait k')
    (hjp : j ≫ p = q)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hP : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre p).left)
      (((traitStdModel p).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre q).left)
      (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  let M := traitStdModel q
  have hj : IsPullback M.j (pullback.snd q (traitGenericPoint k')) q (traitGenericPoint k') :=
    IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre q).hom q (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let φ := traitStdHom p hj hi j hjp
  have : IsOpenImmersion φ.total := ‹IsOpenImmersion j›
  have := φ.isIso_pullbackExchange_of_isOpenImmersion (Profinite.padicAlgClRingObj ℓ)
    (isPullback_traitStdHom_generic p hj hi j hjp)
  have h₂ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
    (traitStdSpecialHom p hi j hjp) _ hP
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  exact (boundedConstructible _).prop_of_iso (asIso ((φ.pullbackExchange
    (Profinite.padicAlgClRingObj ℓ)).app _) ≪≫
      (M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _ j).app _ ≪≫
          (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) j).unit.app B)).symm)) h₂

/-- **Deligne's criterion through a compactification** (SGA 4½, [Th. finitude], proof of 3.2):
let `q : T ⟶ S` factor as an open immersion `j : T ⟶ P` followed by a proper `p : P ⟶ S` (a
Nagata compactification, `NearbyCyclesModel.exists_isOpenImmersion_isProper_trait`), and `B` be
bounded constructible on `T`. If the nearby cycles `Ψ_P (j_! B)` satisfy the local coordinate
condition on the proper special fibre `P_s`, then `Ψ_T B` is bounded constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isProper_of_coordinates`
and `NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_compactification`). -/
theorem boundedConstructible_nearbyCycles_traitStdModel_of_coordinates
    {T P : Scheme.{u}} (q : T ⟶ trait k') (j : T ⟶ P) [IsOpenImmersion j] (p : P ⟶ trait k')
    [IsProper p] (hjp : j ≫ p = q)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hB : boundedConstructible _ B)
    (H : ∀ y : (traitStdSpecialFibre p).left, ∃ (U : (traitStdSpecialFibre p).left.Opens)
      (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))),
      (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (F : Finset 𝔸(ULift.{u} (Fin 1); Spec (.of k'))) (hF : ∀ x ∈ F, IsClosed {x}),
        boundedConstructible _
          (L(((b i ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
              (((traitStdModel p).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
                ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre q).left)
      (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian P := ⟨⟩
  exact boundedConstructible_nearbyCycles_traitStdModel_of_compactification q j p hjp
    (boundedConstructible_nearbyCycles_traitStdModel_of_isProper_of_coordinates p
      (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _ j B hB) H)

/-- **Deligne's criterion through a compactification, pointwise form** (SGA 4½, [Th. finitude],
proof of 3.2): let `q : T ⟶ S` factor as an open immersion `j : T ⟶ P` followed by a proper
`p : P ⟶ S`, and `B` be bounded constructible on `T`. Suppose that every point of the special
fibre `P_s` has an open neighbourhood `U` with finitely many coordinates `bᵢ : U ⟶ 𝔸¹_{k'}`
locally of finite type, jointly detecting closed points, such that `Ψ_P (j_! B)` is bounded
constructible on a neighbourhood of every point of `U` over the generic point of a coordinate
line. Then `Ψ_T B` is bounded constructible
(`ProEtale.CondensedRing.boundedConstructible_of_forall_exists_coordinates_of_isGenericPoint`).
The remaining input of Deligne's proof is the spreading of the bounded constructibility of the
restrictions of `Ψ_P (j_! B)` to the geometric generic fibres of the coordinates to
neighbourhoods of the points over the generic points of the coordinate lines. -/
theorem boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint
    {T P : Scheme.{u}} (q : T ⟶ trait k') (j : T ⟶ P) [IsOpenImmersion j] (p : P ⟶ trait k')
    [IsProper p] (hjp : j ≫ p = q)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hB : boundedConstructible _ B)
    (H : ∀ y : (traitStdSpecialFibre p).left, ∃ (U : (traitStdSpecialFibre p).left.Opens)
      (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))),
      (∀ i, LocallyOfFiniteType (b i)) ∧ (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i (v : U), IsGenericPoint (b i v) Set.univ →
        ∃ W : U.toScheme.Opens, v ∈ W ∧ boundedConstructible _
          (L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
              (((traitStdModel p).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
                ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre q).left)
      (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian P := ⟨⟩
  have : IsProper (traitStdSpecialFibre p).hom :=
    inferInstanceAs (IsProper (pullback.snd p (traitClosedPoint k')))
  exact boundedConstructible_nearbyCycles_traitStdModel_of_compactification q j p hjp
    (boundedConstructible_of_forall_exists_coordinates_of_isGenericPoint
      (traitStdSpecialFibre p)
      (boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper p
        (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _ j B hB)) H)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Nagata compactification over the trait**: a separated morphism `q : T ⟶ S` of finite type
to the trait factors as an open immersion followed by a proper morphism
(`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`). -/
lemma exists_isOpenImmersion_isProper_trait {T : Scheme.{u}} (q : T ⟶ trait k')
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q] :
    ∃ (P : Scheme.{u}) (j : T ⟶ P) (p : P ⟶ trait k'), IsOpenImmersion j ∧ IsProper p ∧
      j ≫ p = q := by
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have : HasCompactification q := nagataCompactification_of_locallyOfFinitePresentation q
  obtain ⟨c⟩ := HasCompactification.nonempty_compactification (f := q)
  exact ⟨c.Z, c.i, c.g, c.isOpenImmersion, c.isProper, c.comm.symm⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
