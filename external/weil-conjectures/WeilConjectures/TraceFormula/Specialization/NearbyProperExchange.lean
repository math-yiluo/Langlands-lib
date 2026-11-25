/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.NearbySpecialFibreBaseChange
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The proper exchange of nearby cycles

For a morphism `φ : M ⟶ N` of nearby cycles models of finite type over the trait
`S = Spec k'⟦t⟧` over a proper `f` whose morphism of total spaces is proper and whose squares of
special fibres and of identifications `ε` are cartesian, the pushforward exchange
`χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` (`NearbyCyclesModel.Hom.pushforwardExchange`) is an isomorphism on
bounded constructible `ℚ̄_ℓ`-complexes (blueprint `prose-E-03` (2), "proper
exchange", `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`), provided the
target `Y` of `f` is noetherian over a field in which `ℓ` is invertible. For the geometric models,
whose identifications are the inclusions of the geometric generic fibres, this is
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`.

Following the proof of the blueprint, `χ_f` is the composite of `Li_N^* Rj_{N*}` of the base
change morphism of the square of identifications, of the comparison of the two generic direct
images, and of the base change morphism of the square of special fibres at `Rj_{M*} Lε_M^* K`
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isIso_baseChangeMap`). The first is
invertible by proper base change over noetherian bases mapping to fields
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`), the
last by proper base change at generic direct images
(`NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_lowerStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k' ≠ ℓ)]

omit [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- A model of finite type over the trait whose special fibre is a `k'`-scheme `Y'`, read with
the special fibre as a bare scheme. -/
lemma _root_.AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModel.exists_over
    {Y : Scheme.{u}} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y Y'.left}
    (hN : N.IsTraitModel) : ∃ a : Y'.left ⟶ Spec (.of k'), N.IsTraitModel (X' := Over.mk a) :=
  ⟨Y'.hom, ⟨hN.exists_isPullback⟩⟩

/-- **Proper base change for nearby cycles** (blueprint `prose-E-03` (2),
proper half; SGA 7 XIII 2.1.7): let `φ : M ⟶ N` be a morphism of models of finite type over the
trait over `f : X ⟶ Y`, with `Y` noetherian over a field `k` in which `ℓ` is invertible. If the
morphism of total spaces and `f` are proper and the squares of special fibres and of
identifications `ε` are cartesian, the pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` is
invertible on bounded constructible complexes: by proper base change along `ε_N` and `i_N`, both
sides are `i_N^* Rt_* Rj_{M*} Lε_M^*`. (The `ε`-square cannot be dropped: `Rf_*` must commute
with the base change to the geometric generic fibre.) -/
theorem isIso_pushforwardExchange_app_of_isProper {k : Type u} [Field k]
    [Fact (ringChar k ≠ ℓ)] {X Y : Scheme.{u}} [IsNoetherian Y] (aY : Y ⟶ Spec (.of k))
    {X' Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} (φ : M.Hom N f f')
    (hM : ∃ a : X' ⟶ Spec (.of k'), M.IsTraitModel (X' := Over.mk a))
    (hN : ∃ a : Y' ⟶ Spec (.of k'), N.IsTraitModel (X' := Over.mk a))
    [IsProper φ.total] [IsProper f]
    (hi : IsPullback M.i f' φ.total N.i) (hε : IsPullback M.ε φ.generic f N.ε)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  obtain ⟨aN, hN'⟩ := hN
  have : IsNoetherian N.generic := hN'.isNoetherian_generic
  obtain ⟨q, -, -, -, -, -, -⟩ := hN'.exists_isPullback
  have h₁ := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ aY
    (N.j ≫ q ≫ traitToBase k' k') φ.commSq_ε hε K hK
  have h₂ := φ.isIso_baseChangeMap_commSq_i_app_lowerStar hM ⟨aN, hN'⟩ hi _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε K hK)
  have h₃ := φ.isIso_pushforwardExchange_app_of_isIso_baseChangeMap
    (Profinite.padicAlgClRingObj ℓ) K (by cast_proofs h₁) (by cast_proofs h₂)
  cast_proofs h₃

/-- **The proper exchange for geometric models** (blueprint `prose-E-03` (2)):
let `M` and `N` be models over `Spec k'⟦t⟧`, and `φ : M.geometric ⟶ N.geometric` a morphism of
their geometric models whose morphism of total spaces `t` is proper and whose squares of geometric
generic fibres and of special fibres are cartesian. Then the pushforward exchange
`χ_t : Ψ_N Rt_* ⟶ Rt_{s*} Ψ_M` is an isomorphism on bounded constructible `ℚ̄_ℓ`-complexes. This
is `isIso_pushforwardExchange_app_of_isProper` for the geometric models, whose identifications `ε`
are the inclusions `j` of the geometric generic fibres; their target, the total space of `N`, is
noetherian over `k'`. -/
theorem isIso_pushforwardExchange_app_of_isProper_geometric {X Y : Scheme.{u}}
    {X' Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} {t : M.total ⟶ N.total} {f' : X'.left ⟶ Y'.left}
    (φ : M.geometric.Hom N.geometric t f') (hM : M.IsTraitModel) (hN : N.IsTraitModel)
    (ht : φ.total = t) [IsProper t]
    (hj : IsPullback φ.generic M.j N.j t) (hi : IsPullback M.i f' t N.i)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)))
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  have : IsProper φ.total := by rw [ht]; infer_instance
  have := hN.isNoetherian_total
  obtain ⟨q, -, -, -, -, -, -⟩ := hN.exists_isPullback
  exact φ.isIso_pushforwardExchange_app_of_isProper (q ≫ traitToBase k' k')
    hM.geometric.exists_over ⟨Y'.hom, ⟨hN.exists_isPullback⟩⟩ (by rw [ht]; exact hi) hj.flip hK

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
