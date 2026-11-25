/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegralFactor

/-!

# The slice exchange of a model splits with `𝒪_E`-coefficients

Let `M` be a model of finite type over `S = Spec k'⟦t⟧` (`k'` separably closed of characteristic
`p ≠ ℓ`) with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and `M''` its geometric slice along `b` over
`Spec K⟦t⟧`, `K = k'(x)^alg`. This file proves that the pullback exchange
`α : Lσ_s^* Ψ_M A₀ ⟶ Ψ_{M''} A₀` of the morphism of models `M'' ⟶ M` with `𝒪_E`-coefficients is a
split monomorphism when `Lε^* A₀` is bounded constructible
(`NearbyCyclesModel.isSplitMono_pullbackExchange_baseChangeHom_traitSlice_padicIntegers`), the
integral form of SGA 4½, [Th. finitude], Lemme 3.3–3.4, needed by the induction with
`𝒪_E`-coefficients of Gabber's Künneth formula.

Following Deligne, the slice factors through a generic slice trait `S'`
(`AlgebraicGeometry.nonempty_genericSliceTrait`) as `τ ≫ σ`
(`NearbyCyclesModel.isSplitMono_pullbackExchange_baseChangeHom_traitSlice_of_coordinateSliceTrait`):
* the change of trait `τ : Spec K⟦t⟧ ⟶ S'` has invertible exchange by Th. finitude 3.7 with
  `𝒪_E`-coefficients
  (`NearbyCyclesModel.isIso_pullbackExchange_coordinateSliceTraitChangeHom_padicIntegers`);
* the slice `σ` over the generic slice trait has split exchange
  (`NearbyCyclesModel.isSplitMono_pullbackExchange_coordinateSliceTraitHom_padicIntegers`): it
  factors through its cartesian model, the second factor being weakly étale base change and the
  first the change of geometric generic fibres, a pro-`p` Galois layer up to universal
  homeomorphisms, whose unit is split with `𝒪_E`-coefficients
  (`NearbyCyclesModel.Hom.isSplitMono_unit_toCartesian_generic_of_sliceTrait_padicIntegers`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- **The slice over a generic slice trait splits, `𝒪_E`-coefficients** (SGA 4½, [Th. finitude],
Lemme 3.4): on the models of the geometric generic fibres, the pullback exchange of the slice
`σ : (X' over S') ⟶ (𝒳 over S)` of `M` along the coordinate `b` over a generic slice trait `S'`
is a split monomorphism at every bounded constructible `𝒪_E`-complex `C` on the geometric generic
fibre of `M`. Its cartesian factor is weakly étale base change, an isomorphism, and its change of
geometric generic fibres is split by the unit, the change of generic fibres being a pro-`p`
Galois layer up to universal homeomorphisms. -/
theorem isSplitMono_pullbackExchange_coordinateSliceTraitHom_padicIntegers
    (D : GenericSliceTrait k') (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) M.generic))}
    (hC : boundedConstructible _ C) :
    IsSplitMono (((coordinateSliceTraitHom hM b hb D).pullbackExchange
      (Profinite.padicIntegersRingObj ℓ E.1)).app C) := by
  -- finiteness properties of the geometric generic fibres
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have : QuasiCompact g := MorphismProperty.of_isPullback hM.isPullback_j ‹_›
  have : QuasiSeparated g := MorphismProperty.of_isPullback hM.isPullback_j inferInstance
  have : LocallyOfFiniteType g := MorphismProperty.of_isPullback hM.isPullback_j ‹_›
  have := QuasiCompact.compactSpace_of_compactSpace g
  have := quasiSeparatedSpace_of_quasiSeparated g
  have : IsNoetherian M.generic := isNoetherian_of_locallyOfFiniteType g
  have : IsAffine 𝔸(ULift.{u} (Fin 1); trait k') :=
    inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin 1); trait k'))
  have : QuasiCompact D.toAffineLine := inferInstance
  have : QuasiSeparated D.toAffineLine := inferInstance
  have : QuasiCompact (pullback.fst M.j (pullback.fst b D.toAffineLine)) := inferInstance
  have : QuasiSeparated (pullback.fst M.j (pullback.fst b D.toAffineLine)) := inferInstance
  have : CompactSpace (coordinateSliceTraitHom hM b hb D).cartesianModel.generic :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst M.j (pullback.fst b D.toAffineLine))
  have : QuasiSeparatedSpace (coordinateSliceTraitHom hM b hb D).cartesianModel.generic :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst M.j (pullback.fst b D.toAffineLine))
  have : C.IsGE hC.1.1.choose := hC.1.1.choose_spec
  -- the residual characteristic
  have hp : ∀ m : ℕ, (m : IsLocalRing.ResidueField (PowerSeries k')) = 0 → ringChar k' ∣ m :=
    fun m hm ↦ (ringChar.spec k' m).1
      ((PowerSeries.residueFieldEquiv k').injective (by rw [map_natCast, hm, map_zero]))
  have hq : (coordinateSliceTraitHom hM b hb D).total ≫ q =
      pullback.snd b D.toAffineLine ≫ Spec.map (CommRingCat.ofHom D.toSliceTrait.φ) := by
    rw [coordinateSliceTraitHom_total, coordinateSliceTrait_fst_comp b D hb]
    exact congrArg (pullback.snd b D.toAffineLine ≫ ·) D.spec_φ.symm
  have hunit := Hom.isSplitMono_unit_toCartesian_generic_of_sliceTrait_padicIntegers
    D.toSliceTrait (algebraMap_traitGenericField_injective k') (isAlgebraic_traitGenericField k')
    (coordinateSliceTraitHom hM b hb D) (q := pullback.snd b D.toAffineLine)
    (g := pullback.snd _ _) (q₁ := q) (g₁ := g)
    (IsPullback.of_hasPullback _ _) hM.isPullback_j hq (IsPullback.lift_snd _ _ _ _) hp
    (Fact.out : ringChar k' ≠ ℓ) E C (derivedCompleteIntegers_of_boundedConstructible hC)
    hC.1.1.choose
    (fun m ↦ plusEtaleOrigin_extendScalars_integersModPow_of_boundedConstructible E (m + 1) hC)
  have h𝒪 := Hom.isSplitMono_map_exchangeRight_app_toCartesian_of_isSplitMono_unit
    (Profinite.padicIntegersRingObj ℓ E.1) (coordinateSliceTraitHom hM b hb D) C
    (by exact_mod_proofs hunit)
  have h₂ := Hom.isSplitMono_pullbackExchange_app_of_isSplitMono_map_exchangeRight_app
    (Profinite.padicIntegersRingObj ℓ E.1) (coordinateSliceTraitHom hM b hb D).toCartesian C
    (by exact_mod_proofs h𝒪)
  have := Hom.isIso_pullbackExchange_fromCartesian_of_weaklyEtale
    (coordinateSliceTraitHom hM b hb D) (Profinite.padicIntegersRingObj ℓ E.1)
  have h := Hom.isSplitMono_pullbackExchange_app_of_cartesian (coordinateSliceTraitHom hM b hb D)
    (Profinite.padicIntegersRingObj ℓ E.1) C (NatIso.isIso_app_of_isIso _ C)
    (by exact_mod_proofs h₂)
  exact_mod_proofs h

/-- **The slice exchange splits with `𝒪_E`-coefficients** (SGA 4½, [Th. finitude], Lemme 3.3–3.4;
blueprint `proposition-external-kunneth-formula-nearby-cycles`, "Finite support"): for a model `M`
of finite type over `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, the pullback exchange
`α : Lσ_s^* Ψ_M A₀ ⟶ Ψ_{M''} A₀` with `𝒪_E`-coefficients to the nearby cycles of the geometric
slice `M''` of `M` along `b` (over `Spec K⟦t⟧`, `K = k'(x)^alg`) is a split monomorphism at every
`A₀` whose restriction `Lε^* A₀` to the geometric generic fibre is bounded constructible.

The generic slice factors through a generic slice trait `S'`
(`AlgebraicGeometry.nonempty_genericSliceTrait`), and the exchange factors accordingly
(`NearbyCyclesModel.isSplitMono_pullbackExchange_baseChangeHom_traitSlice_of_coordinateSliceTrait`)
into that of the change of trait `Spec K⟦t⟧ ⟶ S'`, invertible by Th. finitude 3.7
(`NearbyCyclesModel.isIso_pullbackExchange_coordinateSliceTraitChangeHom_padicIntegers`), and that
of the slice over `S'`, split by averaging over a pro-`p` group
(`NearbyCyclesModel.isSplitMono_pullbackExchange_coordinateSliceTraitHom_padicIntegers`). -/
theorem isSplitMono_pullbackExchange_baseChangeHom_traitSlice_padicIntegers
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hA₀ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) M.generic)
      (L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀)) :
    IsSplitMono (((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k'))).pullbackExchange
        (Profinite.padicIntegersRingObj ℓ E.1)).app A₀) := by
  obtain ⟨D⟩ := nonempty_genericSliceTrait k'
  have h₁ := isIso_pullbackExchange_coordinateSliceTraitChangeHom_padicIntegers hM b hb D E
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
      (coordinateSliceTraitGeneric hM b hb D) _ hA₀)
  have h₂ := isSplitMono_pullbackExchange_coordinateSliceTraitHom_padicIntegers hM b hb D E hA₀
  have h := isSplitMono_pullbackExchange_baseChangeHom_traitSlice_of_coordinateSliceTrait hM b hb
    D (Profinite.padicIntegersRingObj ℓ E.1) A₀ (by exact_mod_proofs h₁) (by exact_mod_proofs h₂)
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
