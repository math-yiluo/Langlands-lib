/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ResidueFieldBaseChangeLift
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerStabilization
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeIntegral

/-!

# Stabilization of nearby cycles along the Galois layers, `ℚ̄_ℓ`-coefficients

Let `N` be a model, `h : N.generic ⟶ Spec L` and `Ω/L` a Galois extension. For a complex `C`
with `ℚ̄_ℓ`-coefficients whose restriction `Lε^* C` to the generic fibre is bounded
constructible, the nearby cycles stabilize at a finite Galois layer as soon as they do for the
torsion coefficients `𝔽_E = 𝒪_E/ϖ` at the reductions of all integral complexes: if for every
finite subextension `E ⊆ ℚ̄_ℓ` and every bounded constructible `𝒪_E`-complex `K₀` on `N.generic`
there is a finite Galois subextension `L'` such that the base change morphism of `Rj_*` along
`N_Ω ⟶ N_{L'}`, restricted to the special fibre, is invertible at `𝔽_E ⊗ᴸ Lg^* K₀`, then there
is a finite Galois subextension `L'` such that the pullback exchange of `N_Ω ⟶ N_{L'}` is
invertible at `C`
(`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl`).

The subextension `L'` depends on `K₀`, so the hypothesis is only used at the integral model `K₀`
of `Lε^* C` (`ProEtale.exists_padicAlgCl_iso_integralModel`): derived Nakayama passes from `𝔽_E`
to `𝒪_E` at the derived complete `Lg^* K₀`, and flat extension of scalars from `𝒪_E` to `E` to
`ℚ̄_ℓ` (`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_residueField`); the
pullback `Lg^*` commutes with the extensions of scalars
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_leftDerivedUpperStar_of_iso_extendScalars`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- Forgetting constructibility identifies an integral model with its two scalar extensions. -/
private lemma integralModel_scalarExtension_iso (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T))
    (K : PadicAlgClConstructible T ℓ)
    (e : (constructibleToPadicAlgCl T ℓ E).obj
      ((boundedConstructibleExtendScalars T ℓ E).obj K₀) ≅ K) :
    Nonempty ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) T)).leftDerivedFunctor.obj K₀.obj) ≅
            K.obj) := by
  exact ⟨(boundedConstructible (padicAlgClRingObj T ℓ)).ι.mapIso e⟩

/-- Lift residue-field base change at a pulled-back integral model, then transport it
along the isomorphism identifying its scalar extensions with the given complex. -/
private lemma isIso_restrictedBaseChange_of_residueModel
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {T X Y X' Y' Z : Scheme.{u}} [IsNoetherian T]
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    [QuasiCompact p] [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p']
    (sq : CommSq g' p' p g) (i : Z ⟶ Y') (ε : X ⟶ T)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)))
    (hK : boundedConstructible _ K)
    (e : (constructibleToPadicAlgCl T ℓ E).obj
      ((boundedConstructibleExtendScalars T ℓ E).obj K₀) ≅ ⟨K, hK⟩)
    (h : IsIso ((L((i)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)).map
      ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p)
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p')
        (pullbackSquareComparison
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) sq)).app
        ((Mod.extendScalars (coefficientMap
          (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj
            ((L((ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀.obj))))) :
    IsIso ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app
        ((L((ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K))) := by
  have hK₀ : boundedConstructible _ K₀.obj := by exact_mod_proofs K₀.property
  obtain ⟨n, hn⟩ := hK₀.1.1
  have hεn := isGE_leftDerivedUpperStar_obj _ ε K₀.obj n
  have hc := derivedCompleteIntegers_leftDerivedUpperStar_obj ε
    (derivedCompleteIntegers_of_boundedConstructible hK₀)
  have h₃ := isIso_map_baseChangeMap_app_padicAlgCl_of_residueField ℓ E sq i _ n hc
    (by exact_mod_proofs h)
  have e' := integralModel_scalarExtension_iso T ℓ E K₀ ⟨K, hK⟩ e
  have hgen := isIso_map_baseChangeMap_app_leftDerivedUpperStar_of_iso_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) sq i ε K₀.obj (K := K)
    (by exact_mod_proofs e') (by exact_mod_proofs h₃)
  exact_mod_proofs hgen

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L))

/-- The projection `N_{L'} ⟶ N` of a Galois layer is affine on generic fibres: it is the base
change of `Spec L' ⟶ Spec L`. -/
instance isAffineHom_galoisLayerHom_generic (L' : Type u) [Field L'] [Algebra L L'] :
    IsAffineHom (N.galoisLayerHom h L').generic :=
  MorphismProperty.pullback_fst _ _ (isAffineHom_of_isAffine _)

/-- The generic fibre of a Galois layer of a model whose generic fibre is quasi-compact and
quasi-separated is quasi-compact. -/
lemma compactSpace_galoisLayer_generic [CompactSpace N.generic] (L' : Type u) [Field L']
    [Algebra L L'] : CompactSpace (N.galoisLayer h L').generic :=
  QuasiCompact.compactSpace_of_compactSpace (N.galoisLayerHom h L').generic

/-- The generic fibre of a Galois layer of a model whose generic fibre is quasi-separated is
quasi-separated. -/
lemma quasiSeparatedSpace_galoisLayer_generic [QuasiSeparatedSpace N.generic] (L' : Type u)
    [Field L'] [Algebra L L'] : QuasiSeparatedSpace (N.galoisLayer h L').generic :=
  quasiSeparatedSpace_of_quasiSeparated (N.galoisLayerHom h L').generic

/-- The open immersion of the generic fibre of a Galois layer is quasi-compact if that of the
model is. -/
lemma quasiCompact_galoisLayer_j [QuasiCompact N.j] (L' : Type u) [Field L'] [Algebra L L'] :
    QuasiCompact (N.galoisLayer h L').j :=
  inferInstanceAs (QuasiCompact ((N.galoisLayerHom h L').generic ≫ N.j))

/-- The open immersion of the generic fibre of a Galois layer is quasi-separated if that of the
model is. -/
lemma quasiSeparated_galoisLayer_j [QuasiSeparated N.j] (L' : Type u) [Field L'] [Algebra L L'] :
    QuasiSeparated (N.galoisLayer h L').j :=
  inferInstanceAs (QuasiSeparated ((N.galoisLayerHom h L').generic ≫ N.j))

variable (Ω : Type u) [Field Ω] [Algebra L Ω] (ℓ : ℕ) [Fact ℓ.Prime]

/-- Residue-field stabilization at one integral model gives the desired pullback exchange. -/
private lemma isIso_galoisLayerRestrict_of_residueModel
    [IsNoetherian N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [QuasiCompact N.j] [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))
    (e : (constructibleToPadicAlgCl N.generic ℓ E).obj
      ((boundedConstructibleExtendScalars N.generic ℓ E).obj K₀) ≅ ⟨_, hC⟩)
    (L' : FiniteGaloisIntermediateField L Ω)
    (hL' : IsIso ((L(((N.galoisLayer h Ω).i)^*⟦Profinite.continuousMapRingObj.{u}
            (integersResidueField ℓ E.1)⟧)).map
          ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayer h L'.toIntermediateField).j)
            (derivedUpperStarLowerStarAdjunction
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayer h Ω).j)
            (pullbackSquareComparison
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayerRestrict h Ω L'.toIntermediateField).commSq_j)).app
            ((Mod.extendScalars (coefficientMap
              (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                (N.galoisLayer h L'.toIntermediateField).generic)).leftDerivedFunctor.obj
              ((L(upperStar (Profinite.padicIntegersRingObj ℓ E.1)
                (N.galoisLayerHom h L'.toIntermediateField).generic)).obj K₀.obj))))) :
    IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app C) := by
  -- Normalize the coefficient instances before specializing the geometric argument.
  revert C hC E K₀ e hL'
  normalize_precoherent
  intro C hC E K₀ e hL'
  -- finiteness properties of the Galois layers
  have i₁ := N.compactSpace_galoisLayer_generic h L'.toIntermediateField
  have i₂ := N.quasiSeparatedSpace_galoisLayer_generic h L'.toIntermediateField
  have i₃ := N.compactSpace_galoisLayer_generic h Ω
  have i₄ := N.quasiSeparatedSpace_galoisLayer_generic h Ω
  have i₅ := N.quasiCompact_galoisLayer_j h L'.toIntermediateField
  have i₆ := N.quasiSeparated_galoisLayer_j h L'.toIntermediateField
  have i₇ := N.quasiCompact_galoisLayer_j h Ω
  have i₈ := N.quasiSeparated_galoisLayer_j h Ω
  have i₉ : CompactSpace (N.galoisLayer h L'.toIntermediateField).total :=
    inferInstanceAs (CompactSpace N.total)
  have i₁₀ : QuasiSeparatedSpace (N.galoisLayer h L'.toIntermediateField).total :=
    inferInstanceAs (QuasiSeparatedSpace N.total)
  have i₁₁ : CompactSpace (N.galoisLayer h Ω).total := inferInstanceAs (CompactSpace N.total)
  have i₁₂ : QuasiSeparatedSpace (N.galoisLayer h Ω).total :=
    inferInstanceAs (QuasiSeparatedSpace N.total)
  have hgen := isIso_restrictedBaseChange_of_residueModel ℓ E
    (N.galoisLayerRestrict h Ω L'.toIntermediateField).commSq_j (N.galoisLayer h Ω).i
    (N.galoisLayerHom h L'.toIntermediateField).generic K₀ _ hC e
    (by exact_mod_proofs hL')
  -- reduction to the restricted base change map at `Lg^* (Lε^* C)`
  refine Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app _ _ C ?_
  refine isIso_map_app_of_iso _ _ (A := L(upperStar (Profinite.padicAlgClRingObj ℓ)
      (N.galoisLayerHom h L'.toIntermediateField).generic).obj
        (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) ((leftDerivedUpperStarComp _
    (N.galoisLayerHom h L'.toIntermediateField).generic N.ε).app C).symm ?_
  clear e hL' K₀ E hC
  revert C hgen
  normalize_precoherent
  intro C hgen
  exact hgen

/-- **Nearby cycles stabilize at a finite Galois layer, `ℚ̄_ℓ`-coefficients**. Let `C` be a
`ℚ̄_ℓ`-complex whose restriction `Lε^* C` to the noetherian generic fibre is bounded constructible.
Assume that for every finite subextension `E ⊆ ℚ̄_ℓ` and every bounded constructible
`𝒪_E`-complex `K₀` on `N.generic` there is a finite Galois subextension `L'` of `Ω/L` such that
the base change morphism `Rj_{N_{L'}*} ⟶ Rj_{N_Ω*}` of the change of Galois layers
`N_Ω ⟶ N_{L'}`, restricted to the special fibre, is invertible with `𝔽_E`-coefficients at the
reduction `𝔽_E ⊗ᴸ Lg^* K₀` of the pullback of `K₀` along `g : N_{L'}.generic ⟶ N.generic` (this
is the torsion stabilization, e.g.
`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_isNoetherianObject`).
Then there is a finite Galois subextension `L'` such that the pullback exchange of
`N_Ω ⟶ N_{L'}` is invertible at `C`.

The hypothesis is applied to an integral model `K₀` of `Lε^* C`
(`ProEtale.exists_padicAlgCl_iso_integralModel`) only; the invertibility then passes from `𝔽_E`
to `ℚ̄_ℓ` by `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_residueField`
(derived Nakayama for the derived complete `Lg^* K₀`, then flat extension of scalars), and to the
pullback exchange by
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app`. -/
theorem exists_isIso_pullbackExchange_galoisLayerRestrict_padicAlgCl [IsNoetherian N.generic]
    [CompactSpace N.total] [QuasiSeparatedSpace N.total] [CompactSpace X']
    [QuasiSeparatedSpace X'] [QuasiCompact N.j] [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (hres : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology N.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))),
      boundedConstructible _ K₀ → ∃ L' : FiniteGaloisIntermediateField L Ω,
        IsIso ((L(((N.galoisLayer h Ω).i)^*⟦Profinite.continuousMapRingObj.{u}
            (integersResidueField ℓ E.1)⟧)).map
          ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayer h L'.toIntermediateField).j)
            (derivedUpperStarLowerStarAdjunction
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayer h Ω).j)
            (pullbackSquareComparison
              (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
              (N.galoisLayerRestrict h Ω L'.toIntermediateField).commSq_j)).app
            ((Mod.extendScalars (coefficientMap
              (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                (N.galoisLayer h L'.toIntermediateField).generic)).leftDerivedFunctor.obj
              ((L(upperStar (Profinite.padicIntegersRingObj ℓ E.1)
                (N.galoisLayerHom h L'.toIntermediateField).generic)).obj K₀))))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)).app C) := by
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel N.generic ℓ ⟨_, hC⟩
  obtain ⟨L', hL'⟩ := hres E K₀.obj (by exact_mod_proofs K₀.property)
  exact ⟨L', isIso_galoisLayerRestrict_of_residueModel N h Ω ℓ C hC E K₀ e L'
    (by exact_mod_proofs hL')⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
