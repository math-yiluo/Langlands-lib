/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMonoTorsion

/-!
# Split pullback exchanges of nearby cycles from integral and torsion coefficients

The pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a morphism of models `φ : M ⟶ N` is, up to
isomorphisms, the base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric
generic fibres restricted to the special fibre of `M`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app`). This file
shows that it is a split monomorphism with `ℚ̄_ℓ`-coefficients at `B ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` as
soon as the restricted base change morphism with `𝒪_E/ℓⁿ⁺¹`-coefficients has unique retractions
with a property preserved by reduction, for instance Galois invariance
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_unique_retractions`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

section Abstract

/-- The pullback exchange, in abstract categories: with `θi`, `θε` invertible, it is a split
monomorphism at `o` if `IM` of the base change morphism `β` is one at `E_N o`; `β` is given
together with `β'` and a proof of `β' = β`. -/
private lemma isSplitMono_pullbackExchange_app_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β β' : JNs ⋙ T ⟶ G ⋙ JMs)
    (h : β' = β) (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM)
    (o : DY) (hβ : IsSplitMono (IM.map (β'.app (EN.obj o)))) : IsSplitMono (α.app o) := by
  subst h hα
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  infer_instance

/-- Transport a mapped component along an isomorphism of its input object. -/
private lemma isSplitMono_map_app_of_iso_aux {C D E : Type*}
    [Category C] [Category D] [Category E] {F G : C ⥤ D}
    (η : F ⟶ G) (H : D ⥤ E) {o o' : C} (e : o ≅ o')
    (h : IsSplitMono (H.map (η.app o))) : IsSplitMono (H.map (η.app o')) :=
  NatTrans.isSplitMono_app_of_iso (Functor.whiskerRight η H) e.symm h

/-- Transport a split component through two coefficient changes commuting with pullback. -/
private lemma isSplitMono_map_app_of_two_pullIsos
    {C₀ C₁ C₂ D₀ D₁ D₂ A B : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
    [Category A] [Category B]
    {T₀ : C₀ ⥤ C₁} {T₁ : C₁ ⥤ C₂} {U₀ : D₀ ⥤ D₁} {U₁ : D₁ ⥤ D₂}
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁} {P₂ : C₂ ⥤ D₂}
    (α : P₀ ⋙ U₀ ≅ T₀ ⋙ P₁) (β : P₁ ⋙ U₁ ≅ T₁ ⋙ P₂)
    {F G : D₂ ⥤ A} (η : F ⟶ G) (H : A ⥤ B)
    (o : C₀) {o' : C₂} (e : T₁.obj (T₀.obj o) ≅ o')
    (h : IsSplitMono (H.map (η.app (U₁.obj (U₀.obj (P₀.obj o)))))) :
    IsSplitMono (H.map (η.app (P₂.obj o'))) :=
  isSplitMono_map_app_of_iso_aux η H
    (U₁.mapIso (α.app o) ≪≫ β.app (T₀.obj o) ≪≫ P₂.mapIso e) h

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} in
/-- **The split pullback exchange on the special fibre**: the pullback exchange `α_f` of a
morphism of models is a split monomorphism at `K` as soon as the base change morphism
`Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres, restricted to the
special fibre by `Li_M^*`, is one at `Lε_N^* K`. -/
theorem isSplitMono_pullbackExchange_app_of_isSplitMono_map_exchangeRight_app (φ : M.Hom N f f')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : IsSplitMono ((L((M.i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ N.j) (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j)).app ((L((N.ε)^*⟦Λ⟧)).obj K)))) :
    IsSplitMono ((φ.pullbackExchange Λ).app K) :=
  isSplitMono_pullbackExchange_app_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    _ ((baseChangeMap_eq_exchangeRight Λ φ.commSq_j).symm.trans
      (φ.baseChangeMap_commSq_j_eq_mateEquiv Λ))
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl K hK

variable {ℓ : ℕ} [Fact ℓ.Prime] {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

open PadicAlgCl in
/-- **Split pullback exchanges from the integral case** (the mechanism of SGA 4½,
[Th. finitude], Lemme 3.4, for `ℚ̄_ℓ`-coefficients). Let `φ : M ⟶ N` be a morphism of models
whose schemes are quasi-compact and quasi-separated, and let `B ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)`
with `K₀` a derived complete, bounded below `𝒪_E`-complex on `Y`. If the base change morphism
`Li_M^* BC(Lε_N^* K₀)` of `Rj_*` with `𝒪_E`-coefficients, restricted to the special fibre of `M`,
is a split monomorphism, then the pullback exchange `α_φ` with `ℚ̄_ℓ`-coefficients is a split
monomorphism at `B`. -/
theorem isSplitMono_pullbackExchange_app_of_isSplitMono_padicIntegers (φ : M.Hom N f f')
    [QuasiCompact N.j] [QuasiSeparated N.j] [QuasiCompact M.j] [QuasiSeparated M.j]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace N.generic]
    [QuasiSeparatedSpace N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace M.generic] [QuasiSeparatedSpace M.generic] [CompactSpace M.total]
    [QuasiSeparatedSpace M.total] [CompactSpace X'] [QuasiSeparatedSpace X']
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (n₀ : ℤ) [K₀.IsGE n₀]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (e : (L(Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      Y))).obj ((L(Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) Y))).obj K₀) ≅ B)
    (h𝒪 : IsSplitMono ((L((M.i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) N.j)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) M.j)
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) φ.commSq_j)).app
          ((L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)))) :
    IsSplitMono ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have hn₀ := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) N.ε K₀ n₀
  have hE := isSplitMono_map_baseChangeMap_app_padicSubfield_of_padicIntegers ℓ E φ.commSq_j M.i
    _ n₀ hn₀ (by exact_mod_proofs h𝒪)
  have hnE := isGE_leftDerivedFunctor_extendScalars_obj
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    ((L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀) n₀
  have hA := isSplitMono_map_baseChangeMap_app_padicAlgCl_of_padicSubfield ℓ E φ.commSq_j M.i
    _ n₀ hnE (by exact_mod_proofs hE)
  have h := isSplitMono_map_app_of_two_pullIsos
    (derivedPullIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) N.ε)
    (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) N.ε)
    (Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) N.j)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) M.j)
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) φ.commSq_j))
      (L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)) K₀ e (by exact_mod_proofs hA)
  have := isSplitMono_pullbackExchange_app_of_isSplitMono_map_exchangeRight_app
    (Profinite.padicAlgClRingObj ℓ) φ B (by exact_mod_proofs h)
  exact_mod_proofs this

open PadicAlgCl in
/-- **Split pullback exchanges from unique torsion retractions** (the mechanism of SGA 4½,
[Th. finitude], Lemme 3.4, for `ℚ̄_ℓ`-coefficients). Let `φ : M ⟶ N` be a morphism of models
whose schemes are quasi-compact and quasi-separated, and let `B ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)`
with `K₀` a derived complete, bounded below `𝒪_E`-complex on `Y`. If the base change morphism
`Li_M^* BC(Lε_N^* K₀)` of `Rj_*` with `𝒪_E`-coefficients, restricted to the special fibre of `M`,
has unique torsion retractions (`ProEtale.CondensedRing.HasUniqueTorsionRetractions`; for nearby
cycles, the retractions invariant under the inertia group), then the
pullback exchange `α_φ` with `ℚ̄_ℓ`-coefficients is a split monomorphism at `B`. -/
theorem isSplitMono_pullbackExchange_app_of_unique_retractions (φ : M.Hom N f f')
    [QuasiCompact N.j] [QuasiSeparated N.j] [QuasiCompact M.j] [QuasiSeparated M.j]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace N.generic]
    [QuasiSeparatedSpace N.generic] [CompactSpace N.total] [QuasiSeparatedSpace N.total]
    [CompactSpace M.generic] [QuasiSeparatedSpace M.generic] [CompactSpace M.total]
    [QuasiSeparatedSpace M.total] [CompactSpace X'] [QuasiSeparatedSpace X']
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (hK₀ : derivedCompleteIntegers ℓ E Y K₀) (n₀ : ℤ) [K₀.IsGE n₀]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (e : (L(Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      Y))).obj ((L(Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) Y))).obj K₀) ≅ B)
    (hT : HasUniqueTorsionRetractions ℓ E ((L((M.i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) N.j)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) M.j)
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) φ.commSq_j)).app
          ((L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)))) :
    IsSplitMono ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have h𝒪 :=
    isSplitMono_map_baseChangeMap_app_padicIntegers_of_hasUniqueTorsionRetractions ℓ E
    φ.commSq_j M.i _ (derivedCompleteIntegers_leftDerivedUpperStar_obj N.ε hK₀)
    (by exact_mod_proofs hT)
  exact isSplitMono_pullbackExchange_app_of_isSplitMono_padicIntegers φ E K₀ n₀ e
    (by exact_mod_proofs h𝒪)

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
