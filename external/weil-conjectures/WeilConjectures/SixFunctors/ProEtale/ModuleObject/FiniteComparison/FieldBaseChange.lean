/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport
import WeilConjectures.Tactic.ExactModProofs
import WeilConjectures.Tactic.TransportExact

/-!
# Generic base change over a field for module objects with finite coefficients

Let `k` be a field, `aX : X ⟶ Spec k` quasi-compact and quasi-separated, `aY : Y ⟶ Spec k` locally
of finite type and quasi-compact, and `W = X ×_k Y` with projections `p₁ : W ⟶ X`, `p₂ : W ⟶ Y`.
For a coefficient ring killed by an integer `n` invertible in `k`, the base change morphism
`aY^* Ra_{X*} ⟶ Rp₂_* p₁^*` is an isomorphism on bounded below complexes (of étale origin on the
pro-étale site). This is the base change towards spectra of fields (blueprint
`lemma-kunneth-field-coefficients--1`,
`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`), assembled in three steps:

* on the étale site, for every bounded below complex
  (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_field`): by dévissage to sheaves placed in
  degree `0`, where it is the degreewise base-change property of `aY`;
* on the pro-étale site, at every complex of étale origin
  (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_field`), by conjugating with the
  site comparison (`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`);
* for module objects over `T̲ = C(-, T)`, `T` a finite discrete ring, at every complex `A` with
  `Φ A` bounded below of étale origin
  (`AlgebraicGeometry.ProEtale.CondensedRing.isIso_baseChangeMap_app_of_field_finiteCoefficient`),
  via `AlgebraicGeometry.ProEtale.isIso_baseChangeMap_app_finiteCoefficient_iff`. The case
  `T = 𝔽_E` for `ringChar k ≠ ℓ` is
  `AlgebraicGeometry.ProEtale.CondensedRing.isIso_baseChangeMap_app_of_field_residueField`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X Y W : Scheme.{u}} {aX : X ⟶ Spec (.of k)}
  {aY : Y ⟶ Spec (.of k)} {p₁ : W ⟶ X} {p₂ : W ⟶ Y}

/-- **Base change towards a field, étale, bounded below**: for `aX : X ⟶ Spec k` quasi-compact
and quasi-separated, `aY : Y ⟶ Spec k` locally of finite type and quasi-compact, and a
coefficient ring `Λ` killed by an integer `n` invertible in `k`, the derived base change map
`aY^* Ra_{X*} K ⟶ Rp₂_* p₁^* K` of `W = X ×_k Y` is an isomorphism for every `K ∈ D⁺(X_ét, Λ)`.
By dévissage it suffices to treat sheaves placed in degree `0`, where this is the base-change
property of `aY` (blueprint `lemma-kunneth-field-coefficients--1`). -/
theorem Etale.isIso_baseChange_app_of_field (Λ : Type (u + 1)) [CommRing Λ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [QuasiCompact aX] [QuasiSeparated aX]
    (sq : IsPullback p₁ p₂ aX aY) (n : ℕ) (hn : IsUnit (n : k)) (hΛ : (n : Λ) = 0)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  DerivedCategory.Plus.isIso_app_of_forall_homology _ ⊤
    (fun F _ ↦ (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
      (Etale.universalBaseChangeProperty_of_field Λ aY n hn hΛ q).baseChangeProperty aX p₁ p₂
        sq F)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ aY aX K n q hq)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ p₁ p₂ K n q hq) K
    fun _ ↦ trivial

/-- **Base change towards a field, pro-étale, finite coefficients**: in the situation of
`AlgebraicGeometry.Etale.isIso_baseChange_app_of_field`, the pro-étale derived base change map
`Laᵧ^* Ra_{X*} K ⟶ Rp₂_* Lp₁^* K` is an isomorphism at every complex `K` bounded below of étale
origin. It is the étale one at `K = ν^* L`, conjugated by the site comparison
(`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`). -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_field (Λ : Type (u + 1)) [CommRing Λ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [QuasiCompact aX] [QuasiSeparated aX]
    (sq : IsPullback p₁ p₂ aX aY) (n : ℕ) (hn : IsUnit (n : k)) (hΛ : (n : Λ) = 0)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hK
  let L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨K', hK'⟩
  let eK' : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K := eK
  rw [← NatTrans.isIso_app_iff_of_iso _ eK']
  have := Etale.isIso_baseChange_app_of_field Λ sq n hn hΛ L
  have : QuasiCompact p₂ := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated p₂ :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso aX aY Λ).app L)
      ((ProEtale.baseChangeTargetComparisonIso p₁ p₂ Λ).app L) hαβ.symm)).1 this

namespace ProEtale.CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Generic base change over a field for module objects with finite coefficients**: let `T` be
a finite discrete ring killed by an integer `n` invertible in `k`, `aX : X ⟶ Spec k`
quasi-compact and quasi-separated, `aY : Y ⟶ Spec k` locally of finite type and quasi-compact,
and `W = X ×_k Y`. For every complex `A` of module objects over `T̲_X` bounded below of étale
origin, the base change morphism `Laᵧ^* Ra_{X*} A ⟶ Rp₂_* Lp₁^* A` is an isomorphism. This is
`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_field` read through the
finite-coefficient comparison (`ProEtale.isIso_baseChangeMap_app_finiteCoefficient_iff`). -/
theorem isIso_baseChangeMap_app_of_field_finiteCoefficient [LocallyOfFiniteType aY]
    [QuasiCompact aY] [QuasiCompact aX] [QuasiSeparated aX] (sq : IsPullback p₁ p₂ aX aY)
    (n : ℕ) (hn : IsUnit (n : k)) (hT : (n : T) = 0)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj A)) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj T) (CommSq.mk sq.w)).app A) := by
  have hΛ : (n : ULift.{u + 1} T) = 0 := ULift.ext hT
  have h := isIso_derivedBaseChangeMap_app_of_field (ULift.{u + 1} T) sq n hn hΛ _ hA
  have h2 := (isIso_baseChangeMap_app_finiteCoefficient_iff sq.toCommSq A).2 h
  exact_mod_proofs h2

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- **Generic base change over a field with coefficients `𝔽_E`**: for `ringChar k ≠ ℓ`, the base
change morphism `Laᵧ^* Ra_{X*} A ⟶ Rp₂_* Lp₁^* A` of `W = X ×_k Y` is an isomorphism at every
complex `A` of module objects over `𝔽̲_{E,X}` bounded below of étale origin
(`isIso_baseChangeMap_app_of_field_finiteCoefficient` with `n = ℓ`). -/
theorem isIso_baseChangeMap_app_of_field_residueField [Fact (ringChar k ≠ ℓ)]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [QuasiCompact aX] [QuasiSeparated aX]
    (sq : IsPullback p₁ p₂ aX aY)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
        X)))
    (hA : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E))) X
      ((finiteCoefficientDerivedEquivalence X (PadicAlgCl.integersResidueField ℓ E)).functor.obj
        A)) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
      (CommSq.mk sq.w)).app A) := by
  have hℓ : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ ?_
    rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h) with h₁ | h₁
    · exact CharP.ringChar_ne_one h₁
    · exact (Fact.out : ringChar k ≠ ℓ) h₁
  have h := isIso_baseChangeMap_app_of_field_finiteCoefficient
    (PadicAlgCl.integersResidueField ℓ E) sq ℓ hℓ
    (PadicAlgCl.natCast_eq_zero_integersResidueField ℓ E) A hA
  transport_exact h

end ProEtale.CondensedRing

end AlgebraicGeometry
