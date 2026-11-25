/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.Etale.Derived.FieldExtension.DirectImageBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!
# Pro-étale direct images commute with base change along field extensions

Let `k'/k` be a field extension, `S` a scheme over `k` with base change `S' = S ×_k k'`
(`p : S' ⟶ S`), and fix a cartesian square of schemes

```
T' --e--> T
|         |
h         g
v         v
S' --p--> S
```

with `g` quasi-compact and quasi-separated. This file transfers Stacks 0F1C
(`AlgebraicGeometry.Etale.isIso_baseChange_app_of_fieldExtension`) from étale sheaves with
finite coefficients to the pro-étale setting, following the smooth base change chain:

* for a coefficient ring `Λ` killed by a nonzero integer invertible in `k`, the pro-étale exchange
  map `p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism at every bounded constructible `K`
  (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_fieldExtension`), by
  conjugating the étale statement by the site comparison;
* with coefficients `𝒪_E` for a finite subextension `E ⊆ ℚ̄_ℓ` and `ℓ` invertible in `k`, the base
  change map `Lp^* Rg_* K ⟶ Rh_* Le^* K` of module objects is an isomorphism at every bounded
  constructible `K`
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_fieldExtension`),
  by derived completeness and derived Nakayama;
* with coefficients `ℚ̄_ℓ`, by integral models
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension`).

## References

- Stacks Project, Lemma 59.89.4, <https://stacks.math.columbia.edu/tag/0F1C>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {S T S' T' : Scheme.{u}} (σ : S ⟶ Spec (.of k)) {g : T ⟶ S} {p : S' ⟶ S}
  (σ' : S' ⟶ Spec (.of k'))
  (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  {e : T' ⟶ T} {h : T' ⟶ S'}

include σ σ' hS in
/-- **Pro-étale direct images commute with base change along field extensions, finite
coefficients** (Stacks 0F1C): let `p : S' ⟶ S` be the base change of `σ : S ⟶ Spec k` along a field
extension `k ⟶ k'`, `g` quasi-compact and quasi-separated, and `Λ` killed by a nonzero integer
`N` invertible in `k`. Then the pro-étale exchange map `p^* Rg_* K ⟶ Rh_* e^* K` is an
isomorphism for every bounded constructible pro-étale complex `K` (that is, of étale origin). -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_fieldExtension (Λ : Type (u + 1))
    [CommRing Λ] [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p) (N : ℕ)
    (hN₀ : N ≠ 0) (hN : (N : Λ) = 0) (hNK : IsUnit (N : Γ(Spec (.of k), ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hK : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hK
  let L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨K', hK'.1.1⟩
  let eK' : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K := eK
  rw [← NatTrans.isIso_app_iff_of_iso _ eK']
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) :=
    Etale.isIso_baseChange_app_of_fieldExtension Λ σ σ' hS sq L fun _ ↦
      IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀ hN hNK _
  have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated h :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso g p Λ).app L)
      ((ProEtale.baseChangeTargetComparisonIso e h Λ).app L) hαβ.symm)).1 this

namespace ProEtale.CondensedRing

open PadicAlgCl

section Generic

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]

/-- The base change map with coefficients `Λ₃` is invertible at `K` as soon as `K` is isomorphic
to `T_b (T_a K₀)` for a bounded below `K₀` at which the base change map with coefficients `Λ₁` is
invertible, provided that the invertibility of the base change map passes from `M` to
`T_b (T_a M)` for bounded below `M`. -/
lemma isIso_baseChangeMap_app_of_iso_extendScalars {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X)))
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₃ X))}
    (e : Nonempty ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀) ≅ K))
    (n : ℤ) (hn : K₀.IsGE n)
    (hpad : ∀ (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ₁ X))) (n : ℤ), M.IsGE n → IsIso ((baseChangeMap Λ₁ sq).app M) →
        IsIso ((baseChangeMap Λ₃ sq).app
          ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj M))))
    (hint : IsIso ((baseChangeMap Λ₁ sq).app K₀)) :
    IsIso ((baseChangeMap Λ₃ sq).app K) :=
  (NatTrans.isIso_app_iff_of_iso _ e.some).1 (hpad K₀ n hn hint)

end Generic

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

include σ σ' hS in
/-- For `p : S' ⟶ S` the base change of `σ : S ⟶ Spec k` along a field extension `k ⟶ k'`, `g`
quasi-compact and quasi-separated, `T` noetherian and `ℓ` invertible in `k`, the first derived
reduction of the integral exchange morphism at a bounded constructible `K` is invertible: it is
the base change map with coefficients `𝔽_E` at the first derived reduction of `K`, a bounded
constructible complex of étale origin. -/
lemma isIso_derivedReduction_map_exchangeRight_app_of_fieldExtension [QuasiCompact g]
    [QuasiSeparated g] [IsNoetherian T] (sq : IsPullback e h g p)
    (hℓ : IsUnit (ℓ : Γ(Spec (.of k), ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) T)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) T) K) :
    IsIso ((derivedReduction S' ℓ E).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) g)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) h)
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq)).app K)) := by
  have : K.IsGE hK.1.1.choose := hK.1.1.choose_spec
  have α := (nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E sq.toCommSq K
    hK.1.1.choose).some
  have hfin := ProEtale.isIso_derivedBaseChangeMap_app_of_fieldExtension σ σ' hS _ sq ℓ
    (Fact.out : ℓ.Prime).ne_zero (ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E) hℓ _
    (ProEtale.boundedConstructible_derivedReduction_obj T ℓ E K hK)
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).2 hfin

include σ σ' hS in
/-- **Integral direct images commute with base change along field extensions** (Stacks 0F1C,
`𝒪_E`-coefficients): let `p : S' ⟶ S` be the base change of `σ : S ⟶ Spec k` along a field
extension `k ⟶ k'`, with `S`, `S'`, `T'` quasi-compact and quasi-separated, `g` quasi-compact and
quasi-separated, `T` noetherian and `ℓ` invertible in `k`. Then the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `𝒪_E` is an isomorphism at every bounded
constructible `K`. -/
theorem isIso_baseChangeMap_app_padicIntegers_of_fieldExtension [QuasiCompact g]
    [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace S']
    [QuasiSeparatedSpace S'] [CompactSpace T'] [QuasiSeparatedSpace T'] [IsNoetherian T]
    (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(Spec (.of k), ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) T)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) T) K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq).app K) := by
  have hK₀ : derivedCompleteIntegers ℓ E T K := derivedCompleteIntegers_of_boundedConstructible hK
  have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj p
    (derivedCompleteIntegers_rightDerivedLowerStar_obj g hK₀)
  have htgt := derivedCompleteIntegers_rightDerivedLowerStar_obj h
    (derivedCompleteIntegers_leftDerivedUpperStar_obj e hK₀)
  have r₁ := isIso_derivedReduction_map_exchangeRight_app_of_fieldExtension σ σ' hS ℓ E sq hℓ K hK
  have hsrc' : derivedCompleteIntegers ℓ E S' ((R((g)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
      L((p)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
    rw [Functor.comp_obj]; exact hsrc
  have htgt' : derivedCompleteIntegers ℓ E S' ((L((e)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
      R((h)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
    rw [Functor.comp_obj]; exact htgt
  have r₃ : IsIso ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) g)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) h)
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq)).app K) :=
    isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map _ hsrc' htgt' r₁
  have t := isIso_baseChangeMap_app_of_isIso_exchangeRight
    (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq K
  -- the two statements carry different proofs of `Precoherent Profinite`
  revert r₃ t
  normalize_precoherent
  intro r₃ t
  exact t r₃

include σ σ' hS in
/-- **`ℓ`-adic direct images commute with base change along field extensions** (Stacks 0F1C,
`ℚ̄_ℓ`-coefficients): let `p : S' ⟶ S` be the base change of `σ : S ⟶ Spec k` along a field
extension `k ⟶ k'`, with `S`, `S'`, `T'` quasi-compact and quasi-separated, `g` quasi-compact and
quasi-separated, `T` noetherian and `ℓ` invertible in `k`. Then the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `ℚ̄_ℓ` is an isomorphism at every bounded
constructible `K`. By integral models, this is
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_fieldExtension`. -/
theorem isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension [QuasiCompact g]
    [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace S']
    [QuasiSeparatedSpace S'] [CompactSpace T'] [QuasiSeparatedSpace T'] [IsNoetherian T]
    (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(Spec (.of k), ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)))
    (hK : boundedConstructible _ K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq.toCommSq).app K) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated h :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel T ℓ ⟨K, hK⟩
  -- the integral model as an object of the ambient derived category, `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ K`
  have hobj : (ObjectProperty.ι _).obj (⟨K, hK⟩ : PadicAlgClConstructible T ℓ) = K := rfl
  have i₁ := (ObjectProperty.liftCompιIso (boundedConstructible (padicAlgClRingObj T ℓ))
    ((boundedConstructible (padicSubfieldRingObj T ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl T ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K)).app
      ((boundedConstructibleExtendScalars T ℓ E).obj K₀)
  have i₂ := (derivedExtendScalarsToPadicAlgCl T ℓ E).mapIso
    ((boundedConstructibleExtendScalarsCompatibility T ℓ E).app K₀)
  have e' := Nonempty.intro ((i₁ ≪≫ i₂).symm ≪≫ (ObjectProperty.ι _).mapIso e ≪≫ eqToIso hobj)
  have hK₀ : boundedConstructible _ K₀.obj := by exact_mod_proofs K₀.property
  obtain ⟨n, hn⟩ := hK₀.1.1
  have hh := isIso_baseChangeMap_app_padicIntegers_of_fieldExtension σ σ' hS ℓ E.1 sq hℓ
    K₀.obj hK₀
  have hpad := isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers ℓ E sq.toCommSq
  have hgen := isIso_baseChangeMap_app_of_iso_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) sq.toCommSq K₀.obj (K := K)
  -- the hypotheses carry different proofs of `Precoherent Profinite`, which are identified
  clear i₁ i₂ hobj e hK₀
  revert E K₀ n hn hh hpad hgen e'
  normalize_precoherent
  intro E K₀ e' n hn hh hpad hgen
  exact hgen e' n hn hpad hh

end ProEtale.CondensedRing

end AlgebraicGeometry
