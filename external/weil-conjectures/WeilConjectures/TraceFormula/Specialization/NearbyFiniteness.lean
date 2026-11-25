/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.RetractPadicAlgCl
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessQuasiFiniteClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice

/-!

# Deligne's finiteness theorem for nearby cycles

Let `M` be a model of finite type over the strictly henselian trait `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.IsTraitModel`), `k'` separably closed of characteristic `p ≠ ℓ`, with total
space `𝒳`, geometric generic fibre `j : 𝒳_η̄ ⟶ 𝒳` and special fibre `i : X' ⟶ 𝒳`. Deligne's
finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2) says that the geometric nearby cycles
`Ψ = Li^* Rj_* Lj^*` (the nearby cycles of the geometric model `M.geometric`) carry bounded
constructible `ℚ̄_ℓ`-complexes on `𝒳` to bounded constructible complexes on `X'`
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). Hence the nearby cycles
`Ψ = Li^* Rj_* Lε^*` of a model whose identification factors as `ε = j ≫ e` through the total
space preserve bounded constructible complexes
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`): `Lε^* ≅ Lj^* Le^*`, and the
pullback `Le^*` preserves bounded constructible complexes.

Following Deligne's proof, the theorem is reduced to the affine spaces `𝔸ⁿ_S`, where it is
proved by induction on `n`:
* **locality**: bounded constructibility on the special fibre is local on a finite open cover
  (`ProEtale.CondensedRing.boundedConstructible_of_openCover`), and nearby cycles commute with
  restriction to the members `V` of a finite affine open cover of `𝒳`
  (`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`), which reduces to affine `𝒳`
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_isAffine`);
* **closed embedding**: an affine `𝒳` embeds as a closed subscheme `c : 𝒳 ⟶ 𝔸ⁿ_S`; by the proper
  exchange `Ψ_{𝔸ⁿ} Rc_* ≅ Rc_{s*} Ψ_𝒳` (blueprint `prose-E-03` (2),
  `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`), the full faithfulness of
  `Rc_{s*}` and the preservation of bounded constructibility by `Rc_*`
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion`),
  this reduces to `𝒳 = 𝔸ⁿ_S` with its standard model `NearbyCyclesModel.traitStdModel`
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj`);
* **induction on `n`**, for all separably closed fields `k'` at once
  (`WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice`): for `n = 0` the nearby
  cycles of the trait itself are computed directly on the pro-étale site
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`); for `n + 1`,
  the restrictions of `Ψ B` to the coordinate generic slices `𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`,
  `K = k'(x)^alg`, are retracts of the nearby cycles over the trait `Spec K⟦t⟧` of the pullbacks
  of `B` to `𝔸ⁿ_{K⟦t⟧}`
  (`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`),
  bounded constructible by induction and closure under retracts
  (`ProEtale.boundedConstructible_of_retract_padicAlgClRingObj`);
* **dévissage**, inside the induction step: along the truncation triangles and by noetherian
  induction along the open–closed triangles, to the extensions by zero `v_! L` of lisse sheaves
  along locally closed immersions into the generic or the special fibre
  (`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`). The nearby cycles
  vanish if the support misses the generic fibre or its closure misses the special fibre
  (`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`), the quasi-finite case reduces
  to the trait by the proper exchange
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite`),
  and Deligne's criterion on the slices
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices`) treats the
  remaining case.

## Implementation notes

The comparison with the slices (SGA 4½, [Th. finitude], Lemme 3.3 and 3.7) is proved in
`WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice`. Deligne's criterion on the
slices (loc. cit., proof of Thm. 3.2) needs the ind-constructibility of torsion étale sheaves,
which has no analogue for pro-étale `ℚ̄_ℓ`-sheaves; it is deduced there from the finiteness
theorem on `𝔸ⁿ_S`, proved first with the finite coefficients `𝔽_E` by Deligne's induction
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`) and then for
`ℚ̄_ℓ` through integral models
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`).
No blueprint node states the finiteness theorem: the blueprint uses it without a node
in the proofs of `proposition-nearby-cycles-commute-verdier-duality` ("bounded constructible by the
finiteness theorem for nearby cycles") and `lemma-nearby-cycles-constant-family--1` ("an exact
functor with bounded constructible values"). The reductions also use the proper exchange (blueprint
`prose-E-03` (2),
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k').Prime] in
/-- **Deligne's finiteness theorem for the extension by zero of a lisse sheaf on a locally closed
subscheme of the generic fibre of `𝔸ⁿ⁺¹_S`, given the slices** (SGA 4½, [Th. finitude], proof of
Thm. 3.2): over the strictly henselian trait `S = Spec k'⟦t⟧`, let `v : E ⟶ 𝔸ⁿ⁺¹_S` be a locally
closed immersion, factored as a surjective closed immersion `c' : E ⟶ W` onto an open `W` of a
closed subscheme `c : D ⟶ 𝔸ⁿ⁺¹_S`, with `W` inside the generic fibre `𝔸ⁿ⁺¹_η`, and let `L` be a
lisse sheaf of `ℚ̄_ℓ`-modules on `E`. If the restrictions `Lhᵢ,ₛ^* Ψ B` of the nearby cycles to
the coordinate generic slices are bounded constructible for all bounded constructible `B`, then
the nearby cycles of `v_! L = Rc_* j_{W!} Rc'_* L` are bounded constructible. If `D` misses the
special fibre, they vanish (`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`); if a
closed subscheme of `D` containing `W` is quasi-finite over `S`, this is
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite`;
the remaining case is Deligne's criterion
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse_generic (n : ℕ)
    (h : ∀ (i : Fin (n + 1))
      (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
        Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (affineSpaceModel k' (n + 1)).total))),
      boundedConstructible _ B →
      boundedConstructible _
        ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
            (Profinite.padicAlgClRingObj ℓ)).obj B)))
    (D : Scheme.{u}) (c : D ⟶ (affineSpaceModel k' (n + 1)).total) [IsClosedImmersion c]
    (W : D.Opens) (hW : (W : Set D) ⊆ c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c'] (hc' : Surjective c')
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
              ((DerivedCategory.singleFunctor _ 0).obj L))))) := by
  by_cases hc : Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' (n + 1)).i.base)
  · exact boundedConstructible_of_isZero _ (isZero_nearbyCycles_affineSpace_of_disjoint _ c hc
      (boundedConstructible_lisseExtension_closed _ D c W E c' L hL))
  by_cases hqf : ∃ (D' : Scheme.{u}) (ι : D' ⟶ D), IsClosedImmersion ι ∧
      (W : Set D) ⊆ Set.range ι.base ∧
      LocallyQuasiFinite (ι ≫ c ≫ (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k'))
  · obtain ⟨D', ι, _, hι, hι'⟩ := hqf
    exact boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite _ D c W E c' L
      hL ι hι hι'
  exact boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices n h D c hc W hqf hW E c' hc'
    L hL

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Dévissage of the finiteness theorem on `𝔸ⁿ_S` to lisse sheaves on the generic fibre**: if
the geometric nearby cycles of the extensions by zero `Rc_* j_{W!} Rc'_* L` of lisse sheaves `L`
along locally closed immersions into the generic fibre `𝔸ⁿ_η` are bounded constructible, then
the geometric nearby cycles of the standard model of `𝔸ⁿ_S` preserve bounded constructible
complexes. This is the dévissage
`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`, adapted to the generic
fibre: when `W` lies in the special fibre, the nearby cycles vanish
(`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_isZero`). -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_lisse_generic (n : ℕ)
    (hgen : ∀ (D : Scheme.{u}) (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
      (W : D.Opens) (_ : (W : Set D) ⊆ c ⁻¹ᵁ affineSpaceGenericOpen k' n) (E : Scheme.{u})
      (c' : E ⟶ W) [IsClosedImmersion c'] (_ : Surjective c')
      (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E)),
      IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L →
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
        (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
          ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
            (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
              ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
                ((DerivedCategory.singleFunctor _ 0).obj L))))))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' n).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) := by
  have := isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel (k' := k') n)
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)).IsTriangulated :=
    isTriangulated_boundedConstructible_padicAlgClRingObj _ ℓ
  refine boundedConstructible_obj_of_forall_lisse_along
    (Φ := L(((affineSpaceModel k' n).geometric.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
      R(((affineSpaceModel k' n).geometric.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L(((affineSpaceModel k' n).geometric.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (U := affineSpaceGenericOpen k' n) (fun D c _ W hW E c' _ hc' L hL ↦ ?_) hB
  rcases hW with hW | hW
  · exact hgen D c W hW E c' hc' L hL
  · have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace (c ⁻¹ᵁ affineSpaceGenericOpen k' n) :=
      (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι :=
      ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    exact boundedConstructible_of_isZero _ (isZero_nearbyCycles_affineSpace_of_isZero n c
      (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint _ W.ι
        (c ⁻¹ᵁ affineSpaceGenericOpen k' n).ι (by rwa [Scheme.Opens.range_ι,
          Scheme.Opens.range_ι]) _))

omit [Fact (ringChar k').Prime] in
/-- **Deligne's finiteness theorem on `𝔸ⁿ⁺¹_S`, given the slices** (SGA 4½, [Th. finitude], proof
of Thm. 3.2): if the restrictions `Lhᵢ,ₛ^* Ψ B` of the nearby cycles to the coordinate generic
slices of the special fibre are bounded constructible for all bounded constructible `B`, then the
geometric nearby cycles of the standard model of `𝔸ⁿ⁺¹_S` preserve bounded constructible
complexes: by the dévissage
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_lisse_generic`, this is
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_slices (n : ℕ)
    (h : ∀ (i : Fin (n + 1))
      (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
        Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (affineSpaceModel k' (n + 1)).total))),
      boundedConstructible _ B →
      boundedConstructible _
        ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
            (Profinite.padicAlgClRingObj ℓ)).obj B)))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) :=
  boundedConstructible_nearbyCycles_affineSpace_of_lisse_generic (n + 1)
    (fun D c _ W hW E c' _ hc' L hL ↦
      boundedConstructible_nearbyCycles_affineSpace_lisse_generic n h D c W hW E c' hc' L hL) hB

/-- **Deligne's finiteness theorem for nearby cycles on an affine space** (SGA 4½,
[Th. finitude], Thm. 3.2; for `ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): over the strictly
henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the geometric nearby
cycles of the standard model of `𝔸ⁿ_S` preserve bounded constructible complexes.

Deligne's induction on `n`, for all separably closed fields `k'` at once (the slices live over
the different field `K = k'(x)^alg`): for `n = 0`,
`𝔸⁰_S ⟶ S` is an isomorphism and the nearby cycles of the trait are computed directly
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`). For `n + 1`, by
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_slices` it suffices that the
restrictions `Lhᵢ,ₛ^* Ψ B` to the coordinate generic slices of the special fibre are bounded
constructible; they are retracts
(`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`) of the nearby
cycles over the trait `Spec K⟦t⟧` of the pullbacks `Lhᵢ^* B` to `𝔸ⁿ_{K⟦t⟧}`, which are bounded
constructible by induction. -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj (n : ℕ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' n).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        B) := by
  induction n generalizing k' with
  | zero => exact boundedConstructible_nearbyCycles_affineSpaceModel_zero hB
  | succ n ih =>
    have : Fact (ringChar (traitSliceField k')).Prime :=
      ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
    have : Fact (ringChar (traitSliceField k') ≠ ℓ) :=
      ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
    have : IsNoetherian (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n);
        trait (traitSliceField k')) ↘ trait (traitSliceField k'))).left :=
      isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel n)
    refine boundedConstructible_nearbyCycles_affineSpace_of_slices n (fun i B' hB' ↦ ?_) hB
    obtain ⟨e⟩ := nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice n i hB'
    exact ProEtale.boundedConstructible_of_retract_padicAlgClRingObj ℓ e
      (ih (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB'))

/-- **Reduction to affine spaces**: for a model `M` of finite type over the trait with affine
total space `𝒳`, the geometric nearby cycles preserve bounded constructible complexes. Choose a
closed immersion `c : 𝒳 ⟶ 𝔸ⁿ_S` over the trait; then
`Ψ_𝒳 B ≅ Lc_s^* Rc_{s*} Ψ_𝒳 B ≅ Lc_s^* Ψ_{𝔸ⁿ} (Rc_* B)` by the full faithfulness of `Rc_{s*}` and
the proper exchange, and `Rc_* B` is bounded constructible. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_isAffine
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel) [IsAffine M.total]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  obtain ⟨q, g, _, _, _, hj, hi⟩ := hM.exists_isPullback
  obtain ⟨n, c, hc, _⟩ := exists_isClosedImmersion_affineSpace_of_isAffine q
  exact boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding
    (N := affineSpaceModel k' n) hM (isTraitModel_affineSpaceModel n) (traitStdHom _ hj hi c hc)
    rfl (isPullback_traitStdHom_generic _ hj hi c hc) (isPullback_traitStdHom_special _ hi c hc)
    (fun hB' ↦ boundedConstructible_nearbyCycles_affineSpace_obj n hB') hB

/-- **Deligne's finiteness theorem for nearby cycles** (SGA 4½, [Th. finitude], Thm. 3.2; for
`ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): for a model `M` of finite type over the strictly
henselian trait `Spec k'⟦t⟧`, the geometric nearby cycles `Li^* Rj_* Lj^*` carry bounded
constructible complexes on the total space `𝒳` to bounded constructible complexes on the special
fibre. Bounded constructibility on the special fibre is checked on the traces `i⁻¹ V` of a
finite affine open cover of `𝒳`, where the nearby cycles are those of the restricted models
(`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`), and the affine case is
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_isAffine`. -/
theorem boundedConstructible_geometricNearbyCycles_obj
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have := hM.isNoetherian_total
  have := isNoetherian_of_isTraitModel hM
  obtain ⟨n, V, hV⟩ := hM.exists_affineOpens_cover
  refine boundedConstructible_of_openCover _ (fun a ↦ M.i ⁻¹ᵁ (V a : M.total.Opens))
    (fun x ↦ hV (M.i.base x)) _ fun a ↦ ?_
  have : TopologicalSpace.NoetherianSpace (V a : M.total.Opens) :=
    (V a : M.total.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (V a : M.total.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsAffine (M.restrict (V a : M.total.Opens)).total := (V a).2
  have := isIso_pullbackExchange_restrictHom (Profinite.padicAlgClRingObj ℓ) M (V a)
  exact (boundedConstructible _).prop_of_iso
    (asIso (((M.restrictHom (V a)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B)).symm
    (boundedConstructible_geometricNearbyCycles_obj_of_isAffine _ (hM.restrict _)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB))

/-- **Deligne's finiteness theorem for the nearby cycles of a model** (SGA 4½, [Th. finitude],
Thm. 3.2; for `ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): over the strictly henselian trait
`Spec k'⟦t⟧`, the nearby cycles `Ψ = Li^* Rj_* Lε^*` of a model of finite type whose
identification factors as `ε = j ≫ e` through the total space preserve bounded constructible
complexes: `Lε^* A ≅ Lj^* Le^* A`, the pullback `Le^* A` is bounded constructible, and the
geometric nearby cycles `Li^* Rj_* Lj^*` preserve bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). No blueprint node states
this theorem; it is the analogue over the trait of `proposition-six-operations-dctf--5`
(`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`). -/
theorem preservesBoundedConstructible_of_isTraitModel (M : NearbyCyclesModel X X'.left)
    (hM : M.IsTraitModel) (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) := by
  obtain ⟨e, he⟩ := hε
  intro K hK
  have hB := boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.padicAlgClRingObj ℓ) e K hK
  have i₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    he.symm K).some
  have i₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) M.j e).app K
  exact (boundedConstructible _).prop_of_iso
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso
      ((R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso (i₁ ≪≫ i₂)).symm)
    (boundedConstructible_geometricNearbyCycles_obj M hM hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
