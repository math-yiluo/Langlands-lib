/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Ideal
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Restricting a model over the trait to an open of its total space

Let `M` be a model of finite type over the trait `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.IsTraitModel`), with total space `𝒳`, geometric generic fibre
`j : 𝒳_η̄ ⟶ 𝒳` and special fibre `i : X' ⟶ 𝒳`.

* The *geometric model* `M.geometric` of `𝒳` itself has the same total space, fibres and
  inclusions, and identification `ε = j`; its nearby cycles are the geometric nearby cycles
  `Li^* Rj_* Lj^*` (`NearbyCyclesModel.geometric`).
* For an open `V ⊆ 𝒳`, the restriction `M.restrictOpen V` keeps the identification `ε`
  (restricted to `j⁻¹ V`), and the inclusions form a morphism of models
  `M.restrictOpenHom V : M.restrictOpen V ⟶ M` over `𝟙 X` and `i⁻¹ V ⟶ X'`
  (`NearbyCyclesModel.restrictOpen`, `NearbyCyclesModel.restrictOpenHom`).
* The *restriction* `M.restrict V` is the geometric model of `M.restrictOpen V`, with
  geometric generic fibre `j⁻¹ V` and special fibre `i⁻¹ V` (`NearbyCyclesModel.restrict`). It is
  again a model of finite type over the trait if `V ⟶ 𝒳` is quasi-compact
  (`NearbyCyclesModel.IsTraitModel.restrict`), and the inclusions form a morphism of models
  `M.restrict V ⟶ M.geometric` (`NearbyCyclesModel.restrictHom`) whose square of geometric
  generic fibres is cartesian, so that its pullback exchange is invertible
  (`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`): nearby cycles commute with
  restriction to opens.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {X X'' : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- The *geometric model* of the total space of a model: the same total space, fibres and
inclusions, with the identification `ε = j`. Its nearby cycles are the geometric nearby cycles
`Li^* Rj_* Lj^*`. -/
@[simps]
def geometric (M : NearbyCyclesModel X X'') : NearbyCyclesModel M.total X'' where
  total := M.total
  generic := M.generic
  j := M.j
  i := M.i
  ε := M.j

/-- The geometric model of a model of finite type over the trait is one. -/
lemma IsTraitModel.geometric {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    M.geometric.IsTraitModel :=
  ⟨hM.exists_isPullback⟩

/-- The special fibre `i⁻¹ V` of the restriction of a model to an open `V` of its total space, as
a scheme over `k'`. -/
noncomputable def restrictSpecialFibre (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    Over (Spec (.of k')) :=
  Over.mk ((M.i ⁻¹ᵁ V).ι ≫ X'.hom)

/-- The *restriction* of a model to an open `V` of its total space, keeping the identification
`ε` (restricted to the geometric generic fibre `j⁻¹ V`), with special fibre `i⁻¹ V`. -/
@[simps]
noncomputable def restrictOpen (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    NearbyCyclesModel X (M.restrictSpecialFibre V).left where
  total := V
  generic := M.j ⁻¹ᵁ V
  j := M.j ∣_ V
  i := M.i ∣_ V
  ε := (M.j ⁻¹ᵁ V).ι ≫ M.ε

/-- The inclusion of the restriction of a model to an open `V` of its total space, over `𝟙 X`
and `i⁻¹ V ⟶ X'`. -/
@[simps]
noncomputable def restrictOpenHom (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    (M.restrictOpen V).Hom M (𝟙 X) (M.i ⁻¹ᵁ V).ι where
  total := V.ι
  generic := (M.j ⁻¹ᵁ V).ι
  comm_j := (morphismRestrict_ι M.j V).symm
  comm_i := (morphismRestrict_ι M.i V).symm
  comm_ε := (Category.comp_id _).symm

/-- The *restriction* of a model to an open `V` of its total space: the geometric model of `V`,
with geometric generic fibre `j⁻¹ V` and special fibre `i⁻¹ V`. -/
@[simps!]
noncomputable def restrict (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    NearbyCyclesModel V (M.restrictSpecialFibre V).left :=
  (M.restrictOpen V).geometric

/-- The inclusions of the restriction of a model to an open `V` of its total space into its
geometric model, over the open immersions `V ⟶ 𝒳` and `i⁻¹ V ⟶ X'`. -/
@[simps]
noncomputable def restrictHom (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    (M.restrict V).geometric.Hom M.geometric V.ι (M.i ⁻¹ᵁ V).ι where
  total := V.ι
  generic := (M.j ⁻¹ᵁ V).ι
  comm_j := (morphismRestrict_ι M.j V).symm
  comm_i := (morphismRestrict_ι M.i V).symm
  comm_ε := (morphismRestrict_ι M.j V).symm

/-- The square of geometric generic fibres of the inclusion of a restricted model is
cartesian. -/
lemma isPullback_restrictHom (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    IsPullback (M.restrictHom V).generic (M.restrict V).geometric.j M.geometric.j
      (M.restrictHom V).total :=
  (isPullback_morphismRestrict M.j V).flip

/-- **Nearby cycles commute with restriction to opens**: the pullback exchange
`L(i⁻¹V ⟶ X')^* Ψ_M ⟶ Ψ_{M|_V} L(V ⟶ 𝒳)^*` of the inclusion of the restriction of a model to an
open `V` of its total space is an isomorphism. -/
theorem isIso_pullbackExchange_restrictHom (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : NearbyCyclesModel X X'.left) (V : M.total.Opens) :
    IsIso ((M.restrictHom V).pullbackExchange Λ) :=
  have : IsOpenImmersion (M.restrictHom V).total := inferInstanceAs (IsOpenImmersion V.ι)
  (M.restrictHom V).isIso_pullbackExchange_of_isOpenImmersion Λ (M.isPullback_restrictHom V)

/-- The restriction of a model of finite type over the trait to an open `V` of its total space
with quasi-compact inclusion is a model of finite type over the trait. -/
lemma IsTraitModel.restrict {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel)
    (V : M.total.Opens) [QuasiCompact V.ι] : (M.restrict V).IsTraitModel := by
  obtain ⟨q, g, _, _, _, hj, hi⟩ := hM.exists_isPullback
  exact ⟨⟨V.ι ≫ q, (M.j ⁻¹ᵁ V).ι ≫ g, inferInstance, inferInstance, inferInstance,
    (isPullback_morphismRestrict M.j V).paste_vert hj,
    (isPullback_morphismRestrict M.i V).paste_vert hi⟩⟩

/-- The total space of a model of finite type over the trait is a noetherian scheme. -/
lemma IsTraitModel.isNoetherian_total {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    IsNoetherian M.total := by
  obtain ⟨q, g, _, _, _, -, -⟩ := hM.exists_isPullback
  have : IsLocallyNoetherian M.total := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace M.total := QuasiCompact.compactSpace_of_compactSpace q
  exact ⟨⟩

/-- The total space of a model of finite type over the trait is covered by finitely many affine
opens. -/
lemma IsTraitModel.exists_affineOpens_cover {M : NearbyCyclesModel X X'.left}
    (hM : M.IsTraitModel) :
    ∃ (n : ℕ) (V : Fin n → M.total.affineOpens), ∀ x, ∃ a, x ∈ (V a : M.total.Opens) := by
  have := hM.isNoetherian_total
  obtain ⟨s, hs, hs'⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := M.total)
    (U := ⊤)).1 isCompact_univ
  have := hs.fintype
  refine ⟨Fintype.card s, fun a ↦ ((Fintype.equivFin s).symm a).1, fun x ↦ ?_⟩
  have hx : x ∈ (⊤ : M.total.Opens) := trivial
  rw [hs'] at hx
  simp only [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨W, hW, hxW⟩ := hx
  exact ⟨Fintype.equivFin s ⟨W, hW⟩, by simpa using hxW⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
