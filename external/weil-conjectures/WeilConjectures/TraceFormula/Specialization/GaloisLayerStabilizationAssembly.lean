/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerStabilizationTorsion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PadicAlgClNsmulCancel
public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationPadicAlgCl

/-!

# Stabilization of nearby cycles along the Galois layers, assembly

Let `N` be a model, `h : N.generic ⟶ Spec L` and `Ω/L` a Galois extension whose finite
subextensions have degrees prime to `ℓ`. For a `ℚ̄_ℓ`-complex `C` whose restriction `Lε^* C` to
the noetherian generic fibre is bounded constructible, the nearby cycles stabilize at a finite
Galois layer as soon as, for the torsion coefficients `𝔽_E = 𝒪_E/ϖ`, the nearby cycles of the
Galois layer `N_Ω` of the geometric generic fibre at the reductions of bounded constructible
`𝒪_E`-complexes have noetherian cohomology sheaves in a bounded range of degrees
(`exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_isNoetherianObject`).

This combines the torsion stabilization
(`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_isNoetherianObject`),
applied to the model `N.toGenericWithSpecial N.i` of the generic fibre, with the passage from
`𝔽_E` to `ℚ̄_ℓ` (`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace PadicAlgCl

/-- A natural number prime to `ℓ` is invertible in the residue field `𝔽_E` of a subfield
`E ⊆ ℚ̄_ℓ`, which has characteristic `ℓ`. -/
lemma isUnit_natCast_integersResidueField_of_not_dvd {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] {n : ℕ} (hn : ¬ ℓ ∣ n) :
    IsUnit (n : PadicAlgCl.integersResidueField ℓ E) := by
  rw [isUnit_iff_ne_zero]
  intro h
  rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _
    ((ringChar.spec _ ℓ).1 (PadicAlgCl.natCast_eq_zero_integersResidueField ℓ E)) with h₁ | h₁
  · exact CharP.ringChar_ne_one h₁
  · exact hn (h₁ ▸ (ringChar.spec _ n).1 h)

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- In the derived category of `ℚ̲̄_ℓ`-module objects on `X`, multiplication by a nonzero natural
number is invertible, the derived category being linear over the characteristic zero field
`ℚ̄_ℓ`. -/
lemma isIso_nsmul_id_derived_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) {n : ℕ}
    (hn : n ≠ 0) (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :
    IsIso (n • 𝟙 K) := by
  let _ := modLinear _ (Profinite.PadicAlgCl.constRingHom.{u} ℓ) X
  have hn' : (n : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨(n : PadicAlgCl ℓ)⁻¹ • 𝟙 K, ?_, ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul (PadicAlgCl ℓ), Linear.smul_comp, Linear.comp_smul,
      Category.comp_id, smul_smul, mul_inv_cancel₀ hn', one_smul]
  · rw [← Nat.cast_smul_eq_nsmul (PadicAlgCl ℓ), Linear.smul_comp, Linear.comp_smul,
      Category.comp_id, smul_smul, inv_mul_cancel₀ hn', one_smul]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

/-- The invertibility of the base change morphism `Lg^* Rj₁_* ⟶ Rj₂_* Lg'^*` of a commutative
square `sq`, restricted along `i`, at `K`. Stating it as a predicate in the morphisms lets the
unifier compare two instances of it argument by argument. -/
def IsIsoRestrictedExchange (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {Z T₁ T₂ G₁ G₂ : Scheme.{u}} (i : Z ⟶ T₂) (j₁ : G₁ ⟶ T₁) (j₂ : G₂ ⟶ T₂)
    {g' : G₂ ⟶ G₁} {g : T₂ ⟶ T₁} (sq : CommSq g' j₂ j₁ g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology G₁) Ab.{u + 1}) (condensedRingObj Λ G₁))) :
    Prop :=
  IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ j₁)
    (derivedUpperStarLowerStarAdjunction Λ j₂) (pullbackSquareComparison Λ sq)).app K))

/-- The pullback exchange of the change of Galois layers of the model
`N.toGenericWithSpecial N.i` of the generic fibre controls the restricted base change morphism of
the Galois layers of `N`: if it is invertible at `C`, then the base change morphism of `Rj_*`
along `N_Ω ⟶ N_{L'}`, restricted to the special fibre, is invertible at `Lg^* C`. The Galois
layers of both models have the same total spaces, generic fibres, `j` and `i`. -/
theorem isIsoRestrictedExchange_galoisLayerRestrict_of_toGenericWithSpecial
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
    (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]
    (L' : IntermediateField L Ω)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    (hC : IsIso ((((N.toGenericWithSpecial N.i).galoisLayerRestrict h Ω L').pullbackExchange
      Λ).app C)) :
    IsIso ((L(((N.galoisLayer h Ω).i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ (N.galoisLayer h L').j)
      (derivedUpperStarLowerStarAdjunction Λ (N.galoisLayer h Ω).j)
      (pullbackSquareComparison Λ (N.galoisLayerRestrict h Ω L').commSq_j)).app
        ((L(((N.galoisLayerHom h L').generic)^*⟦Λ⟧)).obj C))) := by
  have hε : (N.galoisLayerHom h L').generic ≫ 𝟙 N.generic =
      ((N.toGenericWithSpecial N.i).galoisLayer h L').ε := by
    simp [galoisLayer]
  have h₁ := Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_app Λ _ C hC
  refine isIso_map_app_of_iso _ _ ((leftDerivedUpperStarCompOfEq Λ hε).app C ≪≫
    (L(((N.galoisLayerHom h L').generic)^*⟦Λ⟧)).mapIso ((leftDerivedUpperStarId Λ _).app C)) ?_
  have h₂ : IsIsoRestrictedExchange Λ ((N.toGenericWithSpecial N.i).galoisLayer h Ω).i
      ((N.toGenericWithSpecial N.i).galoisLayer h L').j
      ((N.toGenericWithSpecial N.i).galoisLayer h Ω).j
      ((N.toGenericWithSpecial N.i).galoisLayerRestrict h Ω L').commSq_j
      ((L((((N.toGenericWithSpecial N.i).galoisLayer h L').ε)^*⟦Λ⟧)).obj C) := by
    unfold IsIsoRestrictedExchange
    exact_mod_proofs h₁
  have h₃ : IsIsoRestrictedExchange Λ (N.galoisLayer h Ω).i (N.galoisLayer h L').j
      (N.galoisLayer h Ω).j (N.galoisLayerRestrict h Ω L').commSq_j
      ((L(upperStar Λ (X := (N.galoisLayer h L').generic) (Y := N.generic)
        ((N.toGenericWithSpecial N.i).galoisLayer h L').ε)).obj C) := h₂
  unfold IsIsoRestrictedExchange at h₃
  exact_mod_proofs h₃

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
  (ℓ : ℕ) [Fact ℓ.Prime]

-- the statement and the proof involve several large derived functor objects
/-- **Nearby cycles stabilize at a finite Galois layer, `ℚ̄_ℓ`-coefficients**, from the
finiteness of the torsion nearby cycles. Let `Ω/L` be Galois with finite subextensions of degree
prime to `ℓ`, and `C` a `ℚ̄_ℓ`-complex whose restriction `Lε^* C` to the noetherian generic fibre
is bounded constructible. Assume that for every finite subextension `E ⊆ ℚ̄_ℓ` and every bounded
constructible `𝒪_E`-complex `K₀` on `N.generic`, the cohomology sheaves of the nearby cycles with
`𝔽_E`-coefficients of the Galois layer `N_Ω` of the model `N.toGenericWithSpecial N.i` of the
generic fibre, at `L(𝟙)^* (𝔽_E ⊗ᴸ K₀)`, are noetherian and vanish outside some `[a, b]`. Then
there is a finite Galois subextension `L'` such that the pullback exchange of `N_Ω ⟶ N_{L'}` is
invertible at `C`. -/
theorem exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_isNoetherianObject
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
      boundedConstructible _ K₀ → ∃ a b : ℤ,
        (∀ q, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
            (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
              (integersResidueField ℓ E.1)⟧).obj
              ((Mod.extendScalars (coefficientMap
                (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                  N.generic)).leftDerivedFunctor.obj K₀))))) ∧
        ∀ q, IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
          ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
            (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
              (integersResidueField ℓ E.1)⟧).obj
              ((Mod.extendScalars (coefficientMap
                (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                  N.generic)).leftDerivedFunctor.obj K₀))))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)).app C) := by
  refine N.exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl h Ω ℓ C hC
    fun E K₀ hK₀ ↦ ?_
  refine (htors E K₀ hK₀).elim fun a hb ↦ hb.elim fun b hab ↦ ?_
  have hC₀ := ObjectProperty.prop_of_iso _
    ((finiteCoefficientDerivedEquivalence N.generic (integersResidueField ℓ E.1)).functor.mapIso
      ((leftDerivedUpperStarId _ N.generic).app _).symm)
    (plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible E hK₀)
  refine ((N.toGenericWithSpecial N.i)
    |>.exists_isIso_pullbackExchange_galoisLayerRestrict_of_isNoetherianObject h Ω
      (integersResidueField ℓ E.1)
      (fun M hM ↦ isUnit_natCast_integersResidueField_of_not_dvd E.1 (hdeg M hM)) _ hC₀ a b
      hab.1 hab.2).elim fun L' hL' ↦ ⟨L', ?_⟩
  have h₁ := isIsoRestrictedExchange_galoisLayerRestrict_of_toGenericWithSpecial _ N h Ω
    L'.toIntermediateField _ hL'
  refine isIso_map_app_of_iso _ _
    ((L(upperStar (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
      (N.galoisLayerHom h L'.toIntermediateField).generic)).mapIso
      ((leftDerivedUpperStarId (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
        N.generic).app _) ≪≫
    ((derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
      (N.galoisLayerHom h L'.toIntermediateField).generic).app K₀).symm) ?_
  transport_exact h₁

-- the statement involves several large derived functor objects
/-- **Nearby cycles of the Galois layer are the invariants of a finite quotient,
`ℚ̄_ℓ`-coefficients.** Under the hypotheses of
`exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_isNoetherianObject`,
there is a finite Galois subextension `L'` of `Ω/L` such that `Gal(Ω/L')` acts trivially on
`Ψ_{N_Ω} (L(𝟙)^* C)` and the pullback exchange `α` of the projection `N_Ω ⟶ N` has a retraction
`r` with `|Gal(L'/L)| • (r ≫ α) = ∑_{τ ∈ Gal(L'/L)} τ̃_*`, the sum of the actions of the lifts
`τ̃ = τ.liftNormal Ω`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_padicAlgCl_of_isNoetherianObject
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
      boundedConstructible _ K₀ → ∃ a b : ℤ,
        (∀ q, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
            (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
              (integersResidueField ℓ E.1)⟧).obj
              ((Mod.extendScalars (coefficientMap
                (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                  N.generic)).leftDerivedFunctor.obj K₀))))) ∧
        ∀ q, IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
          ((((N.toGenericWithSpecial N.i).galoisLayer h Ω).nearbyCycles
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
            (L((𝟙 N.generic)^*⟦Profinite.continuousMapRingObj.{u}
              (integersResidueField ℓ E.1)⟧).obj
              ((Mod.extendScalars (coefficientMap
                (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                  N.generic)).leftDerivedFunctor.obj K₀))))) :
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
  refine (N.exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl_of_isNoetherianObject h Ω
    ℓ hdeg C hC htors).elim fun L' hL' ↦ ⟨L', ?_⟩
  have := isIso_nsmul_id_derived_padicAlgClRingObj ℓ N.generic
    (Fintype.card_ne_zero (α := L'.toIntermediateField ≃ₐ[L] L'.toIntermediateField))
    (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)
  have e : C ≅ (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj C :=
    ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X).app C).symm
  have hstab := (NatTrans.isIso_app_iff_of_iso
    ((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)) e).1 hL'
  have key := N.exists_retraction_pullbackExchange_galoisLayerHom_of_isIso h Ω
    L'.toIntermediateField (Profinite.padicAlgClRingObj ℓ) C (by cast_proofs hstab)
    (fun τ ↦ τ.liftNormal Ω) (fun τ ↦ τ.restrict_liftNormal Ω)
  exact_mod_proofs key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
