/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerStabilizationTorsionGenerated
public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationAssembly
public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationIntegralModel

/-!

# Stabilization of nearby cycles along the Galois layers from torsion finiteness

Let `N` be a model, `h : N.generic ⟶ Spec L` and `Ω/L` a Galois extension whose finite
subextensions have degrees prime to `ℓ`. Let `C` be a `ℚ̄_ℓ`-complex with an integral model of
`Lε^* C`: a finite subextension `E ⊆ ℚ̄_ℓ`, a bounded constructible `𝒪_E`-complex `K₀` on the
noetherian generic fibre and an isomorphism `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ Lε^* C` (as produced by
`ProEtale.exists_padicAlgCl_iso_integralModel`). If the nearby cycles of the Galois layer `N_Ω`
of the model `N.toGenericWithSpecial N.i` of the generic fibre at the reduction `𝔽_E ⊗ᴸ K₀` are
bounded constructible on the quasi-compact quasi-separated special fibre, then:

* the nearby cycles stabilize at a finite Galois layer `N_{L'}`
  (`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_integralModel`);
* `Gal(Ω/L')` acts trivially on `Ψ_{N_Ω} C` and the pullback exchange of `N_Ω ⟶ N` is split by
  the average over `Gal(L'/L)`
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel`).

The variant `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_forall`
assumes the bounded constructibility for the reductions of all bounded constructible
`𝒪_E`-complexes, and no integral model.

This is
`exists_retraction_pullbackExchange_galoisLayerHom_padicAlgCl_of_isNoetherianObject`
with the noetherianity of the torsion nearby cycles, which fails for pro-étale sheaves in general,
replaced by their bounded constructibility: the torsion stabilization is
`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_boundedConstructible`,
and the passage from `𝔽_E` to `ℚ̄_ℓ` at the given integral model is
`NearbyCyclesModel.isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_integralModel`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Nearby cycles stabilize at a finite Galois layer, `ℚ̄_ℓ`-coefficients**, from the bounded
constructibility of the torsion nearby cycles at an integral model. Let `Ω/L` be Galois with
finite subextensions of degree prime to `ℓ`, `C` a `ℚ̄_ℓ`-complex and `K₀` a bounded constructible
`𝒪_E`-complex on the noetherian generic fibre with `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ Lε^* C`. If the nearby
cycles with `𝔽_E`-coefficients of the Galois layer `N_Ω` of the model `N.toGenericWithSpecial N.i`
of the generic fibre at `L(𝟙)^* (𝔽_E ⊗ᴸ K₀)` are bounded constructible, there is a finite Galois
subextension `L'` such that the pullback exchange of `N_Ω ⟶ N_{L'}` is invertible at `C`. -/
theorem exists_isIso_pullbackExchange_galoisLayerRestrict_of_integralModel
    [IsNoetherian N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [QuasiCompact N.j] [QuasiSeparated N.j]
    (hdeg : ∀ M : IntermediateField L Ω, FiniteDimensional L M → ¬ ℓ ∣ Module.finrank L M)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))
    (e : (constructibleToPadicAlgCl N.generic ℓ E).obj
      ((boundedConstructibleExtendScalars N.generic ℓ E).obj K₀) ≅ ⟨_, hC⟩)
    (htors : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) X')
      ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
        (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
          (integersResidueField ℓ E.1)⟧).obj
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
              N.generic)).leftDerivedFunctor.obj K₀.obj)))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)).app C) := by
  have hC₀ := ObjectProperty.prop_of_iso _
    ((finiteCoefficientDerivedEquivalence N.generic (integersResidueField ℓ E.1)).functor.mapIso
      ((leftDerivedUpperStarId _ N.generic).app _).symm)
    (plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible E K₀.property)
  obtain ⟨L', hL'⟩ := (N.toGenericWithSpecial N.i)
    |>.exists_isIso_pullbackExchange_galoisLayerRestrict_of_boundedConstructible h Ω
      (integersResidueField ℓ E.1)
      (fun M hM ↦ isUnit_natCast_integersResidueField_of_not_dvd E.1 (hdeg M hM)) _ hC₀ htors
  refine ⟨L', N.isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_integralModel h Ω ℓ C hC
    E K₀ e L' ?_⟩
  have h₁ := isIsoRestrictedExchange_galoisLayerRestrict_of_toGenericWithSpecial _ N h Ω
    L'.toIntermediateField _ hL'
  refine isIso_map_app_of_iso _ _
    ((L(upperStar (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
      (N.galoisLayerHom h L'.toIntermediateField).generic)).mapIso
      ((leftDerivedUpperStarId (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
        N.generic).app _) ≪≫
    ((derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
      (N.galoisLayerHom h L'.toIntermediateField).generic).app K₀.obj).symm) ?_
  transport_exact h₁

/-- Transport stabilization along the identity pullback, then apply finite Galois averaging. -/
private theorem retraction_of_stabilization
    {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
    (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (L' : FiniteGaloisIntermediateField L Ω)
    [IsIso (Fintype.card (L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField) •
      𝟙 (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))]
    (hL' : IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app C)) :
    (∀ σ ∈ L'.toIntermediateField.fixingSubgroup,
      (N.galoisLayerAut h Ω σ).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C ≫ r =
        𝟙 _ ∧
      Fintype.card (L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField) •
          (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) =
        ∑ τ : L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField,
          (N.galoisLayerAut h Ω (τ.liftNormal Ω)).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  have e : C ≅ (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj C :=
    ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X).app C).symm
  have hstab := (NatTrans.isIso_app_iff_of_iso
    ((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)) e).1 hL'
  have key := N.exists_retraction_pullbackExchange_galoisLayerHom_of_isIso h Ω
    L'.toIntermediateField (Profinite.padicAlgClRingObj ℓ) C (by cast_proofs hstab)
    (fun τ ↦ τ.liftNormal Ω) (fun τ ↦ τ.restrict_liftNormal Ω)
  cast_proofs key

/-- **Nearby cycles of the Galois layer are the invariants of a finite quotient,
`ℚ̄_ℓ`-coefficients**, from the bounded constructibility of the torsion nearby cycles at an
integral model. Under the hypotheses of
`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_integralModel`, there is a
finite Galois subextension `L'` of `Ω/L` such that `Gal(Ω/L')` acts trivially on
`Ψ_{N_Ω} (L(𝟙)^* C)` and the pullback exchange `α` of the projection `N_Ω ⟶ N` has a retraction
`r` with `|Gal(L'/L)| • (r ≫ α) = ∑_{τ ∈ Gal(L'/L)} τ̃_*`, the sum of the actions of the lifts
`τ̃ = τ.liftNormal Ω`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel
    [IsNoetherian N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [QuasiCompact N.j] [QuasiSeparated N.j]
    (hdeg : ∀ M : IntermediateField L Ω, FiniteDimensional L M → ¬ ℓ ∣ Module.finrank L M)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))
    (e : (constructibleToPadicAlgCl N.generic ℓ E).obj
      ((boundedConstructibleExtendScalars N.generic ℓ E).obj K₀) ≅ ⟨_, hC⟩)
    (htors : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) X')
      ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
        (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
          (integersResidueField ℓ E.1)⟧).obj
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
              N.generic)).leftDerivedFunctor.obj K₀.obj)))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      (∀ σ ∈ L'.toIntermediateField.fixingSubgroup,
        (N.galoisLayerAut h Ω σ).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
      ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C ≫ r =
          𝟙 _ ∧
        Fintype.card (L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField) •
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) =
          ∑ τ : L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField,
            (N.galoisLayerAut h Ω (τ.liftNormal Ω)).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  refine (N.exists_isIso_pullbackExchange_galoisLayerRestrict_of_integralModel h Ω ℓ hdeg C hC E
    K₀ e htors).elim fun L' hL' ↦ ⟨L', ?_⟩
  -- Reuse the object fixed by hC instead of elaborating the derived pullback again.
  let K : PadicAlgClConstructible N.generic ℓ := ⟨_, hC⟩
  let : IsIso (Fintype.card (L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField) • 𝟙 K.obj) :=
    isIso_nsmul_id_derived_padicAlgClRingObj ℓ N.generic
      (Fintype.card_ne_zero (α := L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField)) K.obj
  exact retraction_of_stabilization N h Ω ℓ C L' hL'

/-- Eliminate integral models with a generic conclusion, keeping the elimination motive small. -/
private theorem integralModel_induction (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) [Fact ℓ.Prime] (K : PadicAlgClConstructible X ℓ) {P : Prop}
    (step : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)),
      ((constructibleToPadicAlgCl X ℓ E).obj
        ((boundedConstructibleExtendScalars X ℓ E).obj K₀) ≅ K) → P) : P := by
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel X ℓ K
  exact step E K₀ e

/-- **Nearby cycles of the Galois layer are the invariants of a finite quotient,
`ℚ̄_ℓ`-coefficients**, from the bounded constructibility of the torsion nearby cycles of all
bounded constructible integral complexes. This is
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel`, with the
hypothesis on the torsion nearby cycles assumed for every finite subextension `E ⊆ ℚ̄_ℓ` and every
bounded constructible `𝒪_E`-complex `K₀` on the generic fibre, applied to an integral model of
`Lε^* C` (`ProEtale.exists_padicAlgCl_iso_integralModel`). -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_forall
    [IsNoetherian N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [QuasiCompact N.j] [QuasiSeparated N.j]
    (hdeg : ∀ M : IntermediateField L Ω, FiniteDimensional L M → ¬ ℓ ∣ Module.finrank L M)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (htors : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology N.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))),
      boundedConstructible _ K₀ → boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) X')
        ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
          (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
            (integersResidueField ℓ E.1)⟧).obj
            ((Mod.extendScalars (coefficientMap
              (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                N.generic)).leftDerivedFunctor.obj K₀)))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      (∀ σ ∈ L'.toIntermediateField.fixingSubgroup,
        (N.galoisLayerAut h Ω σ).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
      ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C ≫ r =
          𝟙 _ ∧
        Fintype.card (L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField) •
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) =
          ∑ τ : L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField,
            (N.galoisLayerAut h Ω (τ.liftNormal Ω)).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  let K : PadicAlgClConstructible N.generic ℓ := ⟨_, hC⟩
  apply integralModel_induction N.generic ℓ K
  intro E K₀ e
  exact N.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel h Ω ℓ hdeg C hC E K₀ e
    (htors E K₀.obj K₀.property)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
