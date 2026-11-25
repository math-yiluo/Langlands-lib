/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.Tactic.ExactModProofs

/-!
# The reduction modulo `ϖ` of integral smooth base change maps

Let `E ⊆ ℚ̄_ℓ` be a finite subextension with ring of integers `𝒪_E`, uniformizer `ϖ` and residue
field `𝔽_E`. For a commutative square of schemes and a bounded below complex `K` of
`𝒪_{E,X}`-module objects, the first derived reduction `(Lg^* Rf_* K ⟶ Rf'_* Lg'^* K) ⊗ᴸ 𝔽_E` of the
integral base change map is, as an arrow, the base change map with coefficients
`𝔽̲_E = C(-, 𝔽_E)` at `K ⊗ᴸ 𝔽_E`
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedExtendScalars_residueField_map_baseChangeMap`).
Hence, along a smooth morphism with `ℓ` invertible on the base, the first derived reduction of the
integral base change map is invertible at every bounded below `K` whose reduction is bounded
constructible, by smooth base change with finite coefficients
(`ProEtale.CondensedRing.isIso_derivedExtendScalars_residueField_map_baseChangeMap_app_of_smooth`).

Consequently `ϖ` acts invertibly on the cone of the integral base change map
(`ProEtale.CondensedRing.isIso_derivedRegularEndSMul_obj₃_of_isIso_derivedExtendScalars_map`
and `ProEtale.CondensedRing.isIso_derivedRegularEndSMul_cone_baseChangeMap_app_of_smooth`): the
cone `C` satisfies `C ⊗ᴸ 𝔽_E = 0`, and the reduction triangle `C --ϖ--> C ⟶ C ⊗ᴸ 𝔽_E ⟶ C[1]` is
distinguished.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section Square

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- unifying objects of the derived categories of module objects is slow
/-- **The first derived reduction of the integral base change map**: for every commutative square
and every bounded below `K ∈ D(𝒪_{E,X})`, the reduction `(Lg^* Rf_* K ⟶ Rf'_* Lg'^* K) ⊗ᴸ 𝔽_E` of
the base change map with coefficients `𝒪_E` and the base change map with coefficients
`𝔽̲_E = C(-, 𝔽_E)` at `K ⊗ᴸ 𝔽_E` are isomorphic arrows. It is the transfer of exchange morphisms
along the non-flat coefficient change `𝒪_E ⟶ 𝔽_E`
(`nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'`), whose (Push)
comparisons are invertible on bounded below complexes
(`isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`). -/
theorem nonempty_arrowIso_derivedExtendScalars_residueField_map_baseChangeMap
    (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℤ) [K.IsGE n] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E) Y')).leftDerivedFunctor.map
        ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq).app K)) ≅
      Arrow.mk ((baseChangeMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
        sq).app ((Mod.extendScalars (coefficientMap
          (Profinite.padicIntegersRingObjToResidueField ℓ E) X)).leftDerivedFunctor.obj K))) := by
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
  have k₂ := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'
    (Profinite.padicIntegersRingObjToResidueField ℓ E)
    (derivedUpperStarExtendScalarsIsoCompCoherence
      (Profinite.padicIntegersRingObjToResidueField ℓ E)) sq K h₁ h₂
  unfold baseChangeMap
  transport_mod_proofs k₂

end Square

section Constructible

variable {X T : Scheme.{u}}

/-- A complex `K` of `𝒪_{E,X}`-module objects whose reduction `K ⊗ᴸ 𝔽_E` (over the condensed ring
`𝔽̲_E`) is bounded constructible has a first derived reduction `K₁` (over sheaves of
`𝔽_E`-modules) of étale origin. This is the second half of
`ProEtale.boundedConstructible_derivedReduction_obj`, which needs no noetherian hypothesis. -/
theorem boundedConstructible_derivedReduction_obj_of_derivedExtendScalars
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hL : boundedConstructible (residueFieldRingObj X ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj K) := by
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E)))
  rw [← DerivedCategory.boundedConstructibleIntrinsic_eq]
  refine ⟨(residueFieldModuleSheaf X ℓ E).bounded_mapDerivedCategory_obj hL.1, fun n ↦ ?_⟩
  refine isConstructible_of_iso
    (((residueFieldModuleSheaf X ℓ E).mapDerivedCategoryHomologyFunctorIso n).app _) ?_
  exact isConstructible_of_iso
    (((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).app _).symm)
    (isConstructible_finiteCoefficientModEquivalence_functor_obj (integersResidueField ℓ E)
      (hL.2 n))

/-- For a morphism `ε : X ⟶ T` to a noetherian scheme and a bounded constructible `𝒪_E`-complex
`K₀` on `T`, the reduction `(Lε^* K₀) ⊗ᴸ 𝔽_E` is bounded constructible: it is
`Lε^* (K₀ ⊗ᴸ 𝔽_E)` (`derivedUpperStarExtendScalarsIso`), and both the reduction on the noetherian
`T` (`ProEtale.boundedConstructible_derivedExtendScalars_residueField`) and the pullback
(`boundedConstructible_leftDerivedUpperStar_obj_of_scheme`) preserve bounded constructible
complexes. -/
theorem boundedConstructible_derivedExtendScalars_residueField_leftDerivedUpperStar_obj
    [IsNoetherian T] (ε : X ⟶ T)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) T)))
    (hK₀ : boundedConstructible _ K₀) :
    boundedConstructible (residueFieldRingObj X ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj
        ((L((ε)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K₀)) :=
  (boundedConstructible _).prop_of_iso
    ((derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToResidueField ℓ E)
      ε).app K₀).symm
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ ε _
      (boundedConstructible_derivedExtendScalars_residueField T ℓ E K₀ hK₀))

end Constructible

variable {S W Y X : Scheme.{u}} {p : X ⟶ S} {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X}

/-- **The reduction of integral smooth base change**: for a cartesian square `e ≫ g = h ≫ p` with
`p` smooth, `g` quasi-compact and quasi-separated and `ℓ` invertible on `S`, the reduction
`(Lp^* Rg_* K ⟶ Rh_* Le^* K) ⊗ᴸ 𝔽_E` of the integral base change map is invertible at every
bounded below `K` whose reduction `K ⊗ᴸ 𝔽_E` is bounded constructible. Its first derived reduction
is the base change map with coefficients `𝔽_E` at the first derived reduction of `K`
(`nonempty_arrowIso_derivedReduction_map_exchangeRight`), invertible by smooth base change with
finite coefficients (`ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`). -/
theorem isIso_derivedExtendScalars_residueField_map_baseChangeMap_app_of_smooth [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(S, ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W))) (n : ℤ) [K.IsGE n]
    (hK : boundedConstructible (residueFieldRingObj W ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField W ℓ E)).leftDerivedFunctor.obj K)) :
    IsIso ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map
      ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq).app K)) := by
  unfold baseChangeMap
  apply isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map
  have α := (nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E sq.toCommSq K n).some
  have hfin := ProEtale.isIso_derivedBaseChangeMap_app_of_smooth _ p sq ℓ
    (Fact.out : ℓ.Prime).ne_zero (ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E) hℓ _
    (boundedConstructible_derivedReduction_obj_of_derivedExtendScalars ℓ E K hK)
  have key := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).2
  simp only [MorphismProperty.isomorphisms.iff] at key
  exact_mod_proofs key (by exact_mod_proofs hfin)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`ϖ` acts invertibly on the cone of a morphism with invertible reduction**: in a distinguished
triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of `𝒪_{E,X}`-complexes whose first morphism becomes invertible
after `- ⊗ᴸ 𝔽_E`, the multiplication by a uniformizer `ϖ` is invertible on `K₃`: the triangulated
functor `- ⊗ᴸ 𝔽_E` kills `K₃`, and the reduction triangle `K₃ --ϖ--> K₃ ⟶ K₃ ⊗ᴸ 𝔽_E ⟶ K₃[1]` is
distinguished. -/
theorem isIso_derivedRegularEndSMul_obj₃_of_isIso_derivedExtendScalars_map
    {T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))} (hT : T ∈ distTriang _)
    (hT₁ : IsIso ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map
      T.mor₁))
    (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    IsIso ((Mod.derivedRegularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)).app T.obj₃) :=
  Mod.isIso_derivedRegularEndSMul_of_isZero_derivedExtendScalars
    (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ)
    ((Triangle.isZero₃_iff_isIso₁ _ ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)
      ).leftDerivedFunctor.map_distinguished _ hT)).2 hT₁)

/-- **`ϖ` acts invertibly on the cone of integral smooth base change**: for a cartesian square
`e ≫ g = h ≫ p` with `p` smooth, `g` quasi-compact and quasi-separated and `ℓ` invertible on `S`,
and a bounded below `K` whose reduction `K ⊗ᴸ 𝔽_E` is bounded constructible, the multiplication by
a uniformizer `ϖ` is invertible on the cone `C` of the integral base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K`. -/
theorem isIso_derivedRegularEndSMul_cone_baseChangeMap_app_of_smooth [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(S, ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W))) (n : ℤ) [K.IsGE n]
    (hK : boundedConstructible (residueFieldRingObj W ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField W ℓ E)).leftDerivedFunctor.obj K))
    {C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} {v : _ ⟶ C} {δ : C ⟶ _}
    (hT : Triangle.mk ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq).app K)
      v δ ∈ distTriang _)
    (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    IsIso ((Mod.derivedRegularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)).app C) :=
  isIso_derivedRegularEndSMul_obj₃_of_isIso_derivedExtendScalars_map ℓ E hT
    (isIso_derivedExtendScalars_residueField_map_baseChangeMap_app_of_smooth ℓ E sq hℓ K n hK)
    ϖ hϖ

end AlgebraicGeometry.ProEtale.CondensedRing
