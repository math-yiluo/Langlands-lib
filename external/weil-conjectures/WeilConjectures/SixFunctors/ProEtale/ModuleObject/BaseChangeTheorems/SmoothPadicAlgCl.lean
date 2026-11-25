/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChange
public import WeilConjectures.Tactic.ExactModProofs

/-!
# The base change map on the ambient derived categories and the coefficient change `𝒪_E ⟶ ℚ̄_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and write
`Φ = ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} -)` for the extension of scalars along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`. For a
commutative square of schemes

```
X' --g'--> X
|          |
p'         p
v          v
Y' --g---> Y
```

with `p` and `p'` quasi-compact and quasi-separated (no finiteness assumption on the schemes), the
base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` with coefficients `ℚ̄_ℓ` is invertible at `Φ K₀` as soon
as the integral base change map is invertible at the bounded below `𝒪_E`-complex `K₀`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`). This is the
transfer of base change maps along flat coefficient changes on the ambient derived categories
(`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars`), the (Push)
comparisons for `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ` being invertible on bounded below complexes along
quasi-compact quasi-separated morphisms.

The concrete coefficient rings carry instance arguments elaborated in different contexts, which
differ by proofs only; the tactic `exact_mod_proofs` bridges them.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A morphism isomorphic, as an arrow, to the image of an isomorphism under a functor is an
isomorphism. -/
lemma isIso_of_nonempty_arrowIso_map {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B : C} {f : A ⟶ B} (hf : IsIso f) {A' B' : D} {g : A' ⟶ B'}
    (e : Nonempty (Arrow.mk (F.map f) ≅ Arrow.mk g)) : IsIso g := by
  obtain ⟨e⟩ := e
  exact ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff e).1
    ((MorphismProperty.isomorphisms.iff _).2 inferInstance)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Flat

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The derived extension of scalars along a flat coefficient change, being exact, preserves
bounded below complexes. -/
lemma isGE_leftDerivedFunctor_extendScalars_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (n : ℤ) [K.IsGE n] :
    ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K).IsGE n := by
  have := (Mod.extendScalars (coefficientMap a X)).isGE_mapDerivedCategory_obj K n
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorIsoMapDerivedCategory.app K).symm n

/-- The base change map of module objects is the exchange morphism of the pullback square
comparison. The two sides only differ by the unfolding of `baseChangeMap`, whose instance
arguments were elaborated in another context (comparing them at default transparency times
out). -/
lemma baseChangeMap_eq_exchangeRight (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' p' p g) :
    baseChangeMap Λ sq = Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ p)
      (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq) := by
  delta baseChangeMap
  with_reducible_and_instances rfl

/-- **The base change map under a flat change of coefficients**: if the comparisons
`derivedPullIso a` are compatible with composition and the (Push) comparisons along `p` at `K` and
along `p'` at `Lg'^* K` are invertible, then the invertibility of the base change map with
coefficients `Λ` at `K` implies that of the base change map with coefficients `Λ'` at the
extension of scalars of `K`. -/
lemma isIso_baseChangeMap_app_derivedExtendScalars (H : DerivedPullIsoCompCoherence a)
    (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsIso ((baseChangeMap Λ sq).app K)) :
    IsIso ((baseChangeMap Λ' sq).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)) := by
  rw [baseChangeMap_eq_exchangeRight] at hK ⊢
  exact isIso_of_nonempty_arrowIso_map _ hK
    (nonempty_arrowIso_map_exchangeRight_derivedExtendScalars a H sq K h₁ h₂)

end Flat

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
  [QuasiCompact p] [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p']

/-- **The base change map and the coefficient change `𝒪_E ⟶ E`**: for a commutative square whose
vertical morphisms are quasi-compact and quasi-separated, if the base change map with
coefficients `𝒪_E` is invertible at a bounded below complex `K₀`, then the base change map with
coefficients `E` is invertible at `E ⊗ᴸ_{𝒪_E} K₀`. -/
theorem isIso_baseChangeMap_app_padicSubfield_of_padicIntegers (sq : CommSq g' p' p g)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) (hn : K₀.IsGE n)
    (hK₀ : IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app K₀)) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj E.1) sq).app
      ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        X)).leftDerivedFunctor.obj K₀)) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) g' K₀ n
  have h := isIso_baseChangeMap_app_derivedExtendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (derivedPullIsoCompCoherence _) sq K₀
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K₀ n)
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n)
  exact_mod_proofs h hK₀

/-- **The base change map and the coefficient change `E ⟶ ℚ̄_ℓ`**: for a commutative square whose
vertical morphisms are quasi-compact and quasi-separated, if the base change map with
coefficients `E` is invertible at a bounded below complex `K`, then the base change map with
coefficients `ℚ̄_ℓ` is invertible at `ℚ̄_ℓ ⊗ᴸ_E K`. -/
theorem isIso_baseChangeMap_app_padicAlgCl_of_padicSubfield (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) (n : ℤ) (hn : K.IsGE n)
    (hK : IsIso ((baseChangeMap (Profinite.continuousMapRingObj E.1) sq).app K)) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj K)) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj E.1) g' K n
  have h := isIso_baseChangeMap_app_derivedExtendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (derivedPullIsoCompCoherence _) sq K
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p'
      ((g')^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj K) n)
  exact_mod_proofs h hK

/-- **The base change map and the coefficient change `𝒪_E ⟶ ℚ̄_ℓ`**: for a commutative square
whose vertical morphisms are quasi-compact and quasi-separated, if the base change map with
coefficients `𝒪_E` is invertible at a bounded below complex `K₀`, then the base change map with
coefficients `ℚ̄_ℓ` is invertible at `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)`. -/
theorem isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers (sq : CommSq g' p' p g)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) (hn : K₀.IsGE n)
    (hK₀ : IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app K₀)) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj K₀))) :=
  isIso_baseChangeMap_app_padicAlgCl_of_padicSubfield ℓ E sq _ n
    (isGE_leftDerivedFunctor_extendScalars_obj (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      K₀ n)
    (isIso_baseChangeMap_app_padicSubfield_of_padicIntegers ℓ E sq K₀ n hn hK₀)

end AlgebraicGeometry.ProEtale.CondensedRing
