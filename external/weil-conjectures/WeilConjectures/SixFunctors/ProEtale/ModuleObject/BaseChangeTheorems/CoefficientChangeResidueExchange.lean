/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidue
public import WeilConjectures.Tactic.TransportModProofs

/-!
# The derived reduction of the exchange morphism of `D(𝒪_E)`

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and a bounded below complex `K` of `𝒪_{E,X}`-module objects, the first derived reduction
`(Lg^* Rf_* K ⟶ Rf'_* Lg'^* K) ⊗ᴸ 𝔽_E` of the exchange morphism on the ambient derived categories
and the pro-étale base-change morphism with coefficients `𝔽_E` at the first derived reduction of
`K` are isomorphic arrows
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`). This is the
ambient form of the last assertion of blueprint `lemma-naturality-pasting-comparison` for the
residue map `𝒪_E ⟶ 𝔽_E`.

It is the composite of the transfer of exchange morphisms along the non-flat coefficient change
`𝒪_E ⟶ 𝔽_E` (`nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'`), whose
(Push) comparisons are invertible on bounded below complexes
(`isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`), and of the transport along
residue field module sheaves
(`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap`). The two
elaborations of the coefficient ring `𝔽̲_E` in these statements differ by the proof of
`Precoherent Profinite` in `coherentTopology Profinite`, which `transport_mod_proofs` identifies.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- unifying objects of the derived categories of module objects is slow
/-- The first derived reduction of the exchange morphism `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` of the
ambient derived categories of `𝒪_E`-module objects and the pro-étale base-change morphism with
coefficients `𝔽_E` at the first derived reduction of `K` are isomorphic arrows, for every
commutative square and every bounded below `K`. -/
theorem nonempty_arrowIso_derivedReduction_map_exchangeRight (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℤ) [K.IsGE n] :
    Nonempty (Arrow.mk ((derivedReduction Y' ℓ E).map ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f')
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq)).app K)) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) sq).app
        ((derivedReduction X ℓ E).obj K))) := by
  have h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E) f).app K) :=
    isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f K n
  have : ((g')^*⟦Profinite.padicIntegersRingObj ℓ E⟧.leftDerivedFunctor.obj K).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ g' K n
  have h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E) f').app
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E⟧.leftDerivedFunctor.obj K)) :=
    isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E⟧.leftDerivedFunctor.obj K) n
  -- `obtain` would make the elaborator unfold the types; we use `Nonempty.some` instead
  have k₂ := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'
    (Profinite.padicIntegersRingObjToResidueField ℓ E)
    (derivedUpperStarExtendScalarsIsoCompCoherence
      (Profinite.padicIntegersRingObjToResidueField ℓ E)) sq K h₁ h₂
  have k₂' : Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToResidueField ℓ E) Y')).leftDerivedFunctor.map
        ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f)
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f')
          (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq)).app K)) ≅
      Arrow.mk ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f')
        (pullbackSquareComparison
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) sq)).app
        ((Mod.extendScalars (coefficientMap
          (Profinite.padicIntegersRingObjToResidueField ℓ E) X)).leftDerivedFunctor.obj K))) := by
    transport_mod_proofs k₂
  have k₃ := ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap
    (ℓ := ℓ) (E := E) sq ((Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToResidueField ℓ E) X)).leftDerivedFunctor.obj K)
  exact ⟨(residueFieldModuleSheaf Y' ℓ E).mapDerivedCategory.mapArrow.mapIso k₂'.some ≪≫ k₃.some⟩

end AlgebraicGeometry.ProEtale.CondensedRing
