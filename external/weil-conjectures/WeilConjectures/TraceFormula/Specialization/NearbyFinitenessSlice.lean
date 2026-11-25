/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayerIntegral
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessPadicAlgCl
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Deligne's induction for the finiteness of nearby cycles

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic `p ≠ ℓ`, and let `Ψ` be the
geometric nearby cycles of the standard model of `𝔸ⁿ⁺¹_S` (`NearbyCyclesModel.affineSpaceModel`).
Deligne proves that `Ψ` preserves bounded constructible complexes by induction on the relative
dimension (SGA 4½, [Th. finitude], proof of Thm. 3.2), using the coordinate generic slices
`hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`, `K = k'(x)^alg` (`AlgebraicGeometry.affineSpaceSlice`), with
special fibres `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` (`AlgebraicGeometry.affineSpaceSliceSpecial`), the
geometric generic fibres of the coordinate projections of the special fibre. The two steps are:

* **slices** (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`):
  the pullback exchange `α : Lhᵢ,ₛ^* Ψ B ⟶ Ψ_K (Lhᵢ^* B)` of the morphism of geometric models
  over the slice (`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism, so `Lhᵢ,ₛ^* Ψ B`
  is a retract of the nearby cycles over the trait `Spec K⟦t⟧`
  (`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`).
  The slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` is (up to a purely inseparable extension of the residue field) the
  completion of the strict localization `S'` of `𝔸¹_S` at the generic point of
  its special fibre. The nearby cycles over `S` of the base change to `S'` are the invariants
  `(Ψ_{S'})^P` of the nearby cycles over `S'` under the kernel `P` of the surjection of inertia
  groups `I_{S'} ⟶ I_S`, a pro-`p` group (SGA 4½, [Th. finitude], Lemme 3.3), and the nearby
  cycles do not change under the extension of traits `S' ⟶ Spec K⟦t⟧` (loc. cit., 3.7). Since
  `P` is pro-`p` and `p ≠ ℓ`, the averaging over `P` splits the inclusion of the invariants.
* **criterion**
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices`): if the
  restrictions `Lhᵢ,ₛ^* Ψ B` to all the coordinate slices are bounded constructible, then so is
  `Ψ B`. It is stated, and needed, only for the extensions by zero `v_! L` of lisse sheaves on
  the generic fibre to which the dévissage reduces, in the case not covered by the proper
  exchange (the support meets the special fibre and is not quasi-finite over `S`). The points of
  `𝔸ⁿ⁺¹_{k'}` outside the images of all the slices `hᵢ,ₛ` are the closed points; by Deligne's
  argument (loc. cit., proof of 3.2; see also the ind-holonomic analogue in D. Abe, *Around the
  nearby cycle functor for arithmetic 𝒟-modules*, §2) the cohomology sheaves of `Ψ B` are
  extensions of sums of skyscrapers at closed points by constructible sheaves, and the skyscraper
  parts are finite by the finiteness of
  `RΓ(ℙⁿ⁺¹_s, Ψ_{ℙⁿ⁺¹} j_! B) = RΓ(ℙⁿ⁺¹_η̄, j_! B)` (proper exchange and Deligne's finiteness
  over the field `η̄`).

Together with the trait case `n = 0`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`), the dévissage to
lisse sheaves and the proper-exchange cases, they prove the finiteness theorem by induction on `n`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj`).

## Implementation notes

The slice step is proved from Th. finitude 3.7 and the averaging splitting (M2)
(`WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayerIntegral`). Deligne's
argument for the criterion needs that the cohomology sheaves of `Ψ B` are ind-constructible,
which holds for every étale sheaf with torsion coefficients (Stacks 03SA) but has no analogue for
pro-étale `ℚ̄_ℓ`-sheaves. The criterion is therefore deduced from the finiteness theorem itself,
which is proved first with the finite coefficients `𝔽_E`, by Deligne's induction with the
closed-point criterion (`WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsion`),
and then for `ℚ̄_ℓ` through integral models and the integral criterion for derived complete
`𝒪_E`-complexes (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`,
Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8).

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

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Change of trait to the generic slice trait** (SGA 4½, [Th. finitude], 3.7): the pullback
exchange of the change of strictly henselian trait `τ : (𝔸ⁿ_{K⟦t⟧} over Spec K⟦t⟧) ⟶
(𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' over S')` is an isomorphism at the pullback of a bounded constructible
complex `B` on `𝔸ⁿ⁺¹_S`; a case of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`. -/
theorem isIso_pullbackExchange_app_genericSliceTraitChangeHom (D : GenericSliceTrait k') (n : ℕ)
    (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsIso (((genericSliceTraitChangeHom D n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app
        ((L((genericSliceTraitProj D n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B)) := by
  have : Fact (ringChar D.κ ≠ ℓ) := ⟨D.ringChar_κ ▸ Fact.out⟩
  have hB' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
    (genericSliceTraitModel D n i).ε _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
      (genericSliceTraitProj D n i) B hB)
  have hNj : IsPullback (genericSliceTraitModel D n i).j (pullback.snd _ _)
      (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.a)) :=
    IsPullback.of_hasPullback _ _
  have hNi : IsPullback (genericSliceTraitModel D n i).i (pullback.snd _ _)
      (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.b)) :=
    IsPullback.of_hasPullback _ _
  have hMj : IsPullback (affineSpaceModel (traitSliceField k') n).geometric.j (pullback.snd _ _)
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (PowerSeries (traitSliceField k'))
          (traitGenericField (traitSliceField k'))))) :=
    IsPullback.of_hasPullback _ _
  have hMi : IsPullback (affineSpaceModel (traitSliceField k') n).geometric.i (pullback.snd _ _)
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := traitSliceField k')))) :=
    IsPullback.of_hasPullback _ _
  have hφ := isPullback_genericSliceTraitChangeTotal D n i
  have hgen : (genericSliceTraitChangeHom D n i).generic ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωK) := pullback.lift_snd _ _ _
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait (ι := D.ι) (a₁ := D.a)
    (a₂ := algebraMap _ _) (c := D.ωK) (b₁ := D.b) (b₂ := PowerSeries.constantCoeff)
    D.injective_ι D.maximalIdeal_eq_map_ι D.injective_a
    (algebraMap_traitGenericField_injective _) D.isAlgebraic_a
    (isAlgebraic_traitGenericField _) D.ωK_comp_a D.ker_b
    PowerSeries.ker_coeff_eq_max_ideal (genericSliceTraitChangeHom D n i)
    (genericSliceTraitStructure D n i) _ hNj _ hNi _ _ hMj _ hMi hφ hgen hB'

/-- **Slicing over the generic slice trait** (SGA 4½, [Th. finitude], Lemme 3.4): the pullback
exchange of `σ : (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' over S') ⟶ (𝔸ⁿ⁺¹_S over S)` is a split monomorphism at a
bounded constructible complex: its cartesian factor is weakly étale base change, and its change of
generic fibres is split by averaging over the pro-`p` kernel (M2). -/
theorem isSplitMono_pullbackExchange_app_genericSliceTraitHom (D : GenericSliceTrait k') (n : ℕ)
    (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsSplitMono (((genericSliceTraitHom D n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have := (genericSliceTraitHom D n i).isIso_pullbackExchange_fromCartesian_of_weaklyEtale
    (Profinite.padicAlgClRingObj ℓ)
  have h₂ := isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom D n i hB
  have h := Hom.isSplitMono_pullbackExchange_app_of_cartesian (genericSliceTraitHom D n i)
    (Profinite.padicAlgClRingObj ℓ) B inferInstance (by exact_mod_proofs h₂)
  exact_mod_proofs h


/-- **Nearby cycles on the coordinate generic slices** (SGA 4½, [Th. finitude], Lemme 3.3 and
3.7): for a bounded constructible complex `B` on `𝔸ⁿ⁺¹_S` and a coordinate `i`, the pullback
exchange `α : Lhᵢ,ₛ^* Ψ B ⟶ Ψ_K (Lhᵢ^* B)` of the morphism of models over the slice
(`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism: it is the inclusion of the
invariants of `Ψ_K (Lhᵢ^* B)` under a pro-`p` group `P` (`p ≠ ℓ`), split by averaging over `P`.
It is deduced, following Deligne's proof of Lemme 3.3, from the factorization of the slice through
the strict localization `S'` of `𝔸¹_S` at the generic point of its special fibre
(`AlgebraicGeometry.nonempty_genericSliceTrait`): the change of trait `Spec K⟦t⟧ ⟶ S'` has
invertible exchange (`NearbyCyclesModel.isIso_pullbackExchange_app_genericSliceTraitChangeHom`,
Th. finitude 3.7), and the slice `X ×_{𝔸¹_S} S' ⟶ X` over `S' ⟶ S` has split exchange
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_genericSliceTraitHom`, Lemme 3.4). -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  obtain ⟨D⟩ := nonempty_genericSliceTrait k'
  have h₁ := isIso_pullbackExchange_app_genericSliceTraitChangeHom D n i hB
  have h₂ := isSplitMono_pullbackExchange_app_genericSliceTraitHom D n i hB
  have htot : (genericSliceTraitChangeHom D n i).total ≫ (genericSliceTraitHom D n i).total =
      (affineSpaceSliceHom k' n i).total := genericSliceTraitChangeTotal_comp D n i
  have hgen : (genericSliceTraitChangeHom D n i).generic ≫ (genericSliceTraitHom D n i).generic =
      (affineSpaceSliceHom k' n i).generic := genericSliceTraitChangeGeneric_comp D n i
  have key := Hom.isSplitMono_pullbackExchange_app_of_comp (Profinite.padicAlgClRingObj ℓ)
    (genericSliceTraitChangeHom D n i) (genericSliceTraitHom D n i) (affineSpaceSliceHom k' n i)
    (genericSliceTraitChangeTotal_comp D n i) (genericSliceTraitChangeSpecial_comp D n i)
    htot hgen B
  have := key (by exact_mod_proofs h₁) (by exact_mod_proofs h₂)
  exact_mod_proofs this

/-- **Nearby cycles on the coordinate generic slices are retracts**: for a bounded constructible
complex `B` on `𝔸ⁿ⁺¹_S` and a coordinate `i`, the restriction `Lhᵢ,ₛ^* Ψ B` of its nearby cycles
to the geometric generic fibre `𝔸ⁿ_K` of the `i`-th coordinate projection of the special fibre is
a retract of the nearby cycles `Ψ_K (Lhᵢ^* B)` of its pullback to the slice `𝔸ⁿ_{K⟦t⟧}`, through
the pullback exchange
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`). -/
theorem nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    Nonempty (Retract
      ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
          (Profinite.padicAlgClRingObj ℓ)).obj B))
      (((affineSpaceModel (traitSliceField k') n).geometric.nearbyCycles
        (Profinite.padicAlgClRingObj ℓ)).obj
          ((L((affineSpaceSliceTotal k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))) :=
  have := isSplitMono_pullbackExchange_app_affineSpaceSliceHom n i hB
  ⟨⟨_, retraction (((affineSpaceSliceHom k' n i).pullbackExchange
    (Profinite.padicAlgClRingObj ℓ)).app B), IsSplitMono.id _⟩⟩

omit [Fact (ringChar k').Prime] in
set_option linter.unusedVariables false in
-- the hypotheses of the core case of the induction are not needed by the proof, see below
/-- **Deligne's criterion on the coordinate slices, core case** (SGA 4½, [Th. finitude], proof of
Thm. 3.2): suppose that for every coordinate `i` and every bounded constructible complex `B` on
`𝔸ⁿ⁺¹_S`, the restriction `Lhᵢ,ₛ^* Ψ B` of the nearby cycles to the geometric generic fibre of the
`i`-th coordinate projection of the special fibre is bounded constructible. Then the nearby cycles
of the extension by zero `v_! L = Rc_* j_{W!} Rc'_* L` of a lisse sheaf `L` along a locally
closed immersion `v : E ⟶ 𝔸ⁿ⁺¹_S` into the generic fibre are bounded constructible, in the case
not covered by the proper exchange: the closed subscheme `D` meets the special fibre and no
closed subscheme of `D` containing `W` is quasi-finite over `S`.

Since the nearby cycles of `𝔸ⁿ⁺¹_S` preserve bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`, deduced from
the case of finite coefficients), the hypotheses on the slices and on `D`, `W` are not needed:
`v_! L` is bounded constructible. They are kept so that the statement is the step of Deligne's
induction in `NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices (n : ℕ)
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
    (hc : ¬ Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' (n + 1)).i.base))
    (W : D.Opens)
    (hqf : ¬ ∃ (D' : Scheme.{u}) (ι : D' ⟶ D), IsClosedImmersion ι ∧
      (W : Set D) ⊆ Set.range ι.base ∧
      LocallyQuasiFinite (ι ≫ c ≫ (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')))
    (hW : (W : Set D) ⊆ c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)) (E : Scheme.{u})
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
  have : IsNoetherian (affineSpaceModel k' (n + 1)).total :=
    (isTraitModel_affineSpaceModel (k' := k') (n + 1)).isNoetherian_total
  exact boundedConstructible_nearbyCycles_affineSpace_obj_of_integral (n + 1)
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ c
      (boundedConstructible_lisseExtension_closed (n + 1) D c W E c' L hL))

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
