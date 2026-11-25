/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!

# Base change at pulled back integral models

Let `ε : X ⟶ T` be a morphism of schemes and `p : X ⟶ Y` be quasi-compact and quasi-separated,
with a commutative square of `p` along `g : Y' ⟶ Y` whose other vertical morphism is quasi-compact
and quasi-separated. For a bounded constructible `ℚ̄_ℓ`-complex `K` on a topologically noetherian
scheme `T`, the `ℚ̄_ℓ`-base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` is invertible at `Lε^* K` as soon
as, for every finite subextension `E ⊆ ℚ̄_ℓ` and every bounded constructible `𝒪_E`-complex `K₀` on
`T`, the integral base change map is invertible at `Lε^* K₀`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_integral`).

Indeed `K ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for an integral model `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`), the pullback `Lε^*` commutes with both
extensions of scalars (`ProEtale.CondensedRing.derivedPullIso`), and the passage `𝒪_E ⟶ ℚ̄_ℓ` of
base change maps along qcqs morphisms is
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Generic

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))]
  {T X Y X' Y' : Scheme.{u}}

/-- The pullback `Lε^*` commutes with two successive flat extensions of scalars:
`Lε^* (T_b (T_a K₀)) ≅ T_b (T_a (Lε^* K₀))`. -/
noncomputable def leftDerivedUpperStarExtendScalarsExtendScalarsIso (ε : X ⟶ T)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₁ T))) :
    (L((ε)^*⟦Λ₃⟧)).obj ((Mod.extendScalars (coefficientMap b T)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor.obj K₀)) ≅
      (Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj
          ((L((ε)^*⟦Λ₁⟧)).obj K₀)) :=
  ((derivedPullIso b ε).app _).symm ≪≫
    (Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.mapIso
      ((derivedPullIso a ε).app K₀).symm

/-- The base change map with coefficients `Λ₃` is invertible at `Lε^* (T_b (T_a K₀))` as soon as
it is invertible at `T_b (T_a (Lε^* K₀))`. -/
lemma isIso_baseChangeMap_app_leftDerivedUpperStar_extendScalars {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g) (ε : X ⟶ T)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₁ T)))
    (h : IsIso ((baseChangeMap Λ₃ sq).app
      ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj
          ((L((ε)^*⟦Λ₁⟧)).obj K₀))))) :
    IsIso ((baseChangeMap Λ₃ sq).app ((L((ε)^*⟦Λ₃⟧)).obj
      ((Mod.extendScalars (coefficientMap b T)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor.obj K₀)))) :=
  (NatTrans.isIso_app_iff_of_iso _
    (leftDerivedUpperStarExtendScalarsExtendScalarsIso a b ε K₀)).2 h

/-- The base change map with coefficients `Λ₃` is invertible at `Lε^* K` as soon as `K` is
isomorphic to `T_b (T_a K₀)` for a bounded below `K₀` at whose pullback `Lε^* K₀` the base change
map with coefficients `Λ₁` is invertible, provided that the invertibility of the base change map
passes from `M` to `T_b (T_a M)` for bounded below `M`. -/
lemma isIso_baseChangeMap_app_leftDerivedUpperStar_of_iso_extendScalars {p : X ⟶ Y}
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g) (ε : X ⟶ T)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₁ T)))
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₃ T))}
    (e : Nonempty ((Mod.extendScalars (coefficientMap b T)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor.obj K₀) ≅ K))
    (n : ℤ) (hn : K₀.IsGE n)
    (hpad : ∀ (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ₁ X))) (n : ℤ), M.IsGE n → IsIso ((baseChangeMap Λ₁ sq).app M) →
        IsIso ((baseChangeMap Λ₃ sq).app
          ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj M))))
    (hint : IsIso ((baseChangeMap Λ₁ sq).app ((L((ε)^*⟦Λ₁⟧)).obj K₀))) :
    IsIso ((baseChangeMap Λ₃ sq).app ((L((ε)^*⟦Λ₃⟧)).obj K)) := by
  refine (NatTrans.isIso_app_iff_of_iso _ (Functor.mapIso _ e.some)).1 ?_
  exact isIso_baseChangeMap_app_leftDerivedUpperStar_extendScalars a b sq ε K₀
    (hpad _ n (isGE_leftDerivedUpperStar_obj Λ₁ ε K₀ n) hint)

end Generic

variable (ℓ : ℕ) [Fact ℓ.Prime] {T X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
  {p' : X' ⟶ Y'} {g' : X' ⟶ X} [QuasiCompact p] [QuasiSeparated p] [QuasiCompact p']
  [QuasiSeparated p']

/-- **The `ℚ̄_ℓ`-base change map at pulled back complexes, from integral models**: for a
commutative square whose vertical morphisms are quasi-compact and quasi-separated, a morphism
`ε : X ⟶ T` to a topologically noetherian scheme and a bounded constructible `ℚ̄_ℓ`-complex `K` on
`T`, the base change map is invertible at `Lε^* K` if the integral base change maps are invertible
at `Lε^* K₀` for all bounded constructible `𝒪_E`-complexes `K₀` on `T`. -/
theorem isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_integral
    (sq : CommSq g' p' p g) (ε : X ⟶ T) [TopologicalSpace.NoetherianSpace T]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hK : boundedConstructible _ K)
    (h : ∀ (E : FiniteIntermediateField ℓ) (K₀ : DerivedCategory (Mod
      (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T))),
      boundedConstructible _ K₀ →
        IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app
          ((L((ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀))) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app
      ((L((ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
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
  have hh := h E K₀.obj hK₀
  have hpad := isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers ℓ E sq
  have hgen := isIso_baseChangeMap_app_leftDerivedUpperStar_of_iso_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    sq ε K₀.obj (K := K)
  -- the hypotheses carry different proofs of `Precoherent Profinite`, which are identified
  clear i₁ i₂ hobj e hK₀
  revert E K₀ n hn hh hpad hgen e'
  normalize_precoherent
  intro E K₀ e' n hn hh hpad hgen
  exact hgen e' n hn hpad hh

end AlgebraicGeometry.ProEtale.CondensedRing
