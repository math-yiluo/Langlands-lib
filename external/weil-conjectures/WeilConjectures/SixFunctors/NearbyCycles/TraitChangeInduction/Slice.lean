/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Defs
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SlicePoints
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceStep
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisRestriction

/-!

# The slice step of Deligne's induction for the change of trait

Step (A) of SGA 4½, [Th. finitude], proof of 3.7: on the generic slice of a coordinate, the
change of trait is the change of trait of the slices, in smaller chart dimension, up to the
inclusion of invariants under the pro-`p` wild inertia groups.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} [IsLocalHom ι]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **The slice step** (SGA 4½, [Th. finitude], proof of 3.7, step (A)). In the situation of
`NearbyCyclesModel.TraitChangeInvariance`, let `cN : 𝒳_N ⟶ 𝔸¹_{S₁}` be a coordinate over `S₁`
whose slices `𝒳_N ×_{𝔸¹_{S₁}} S'` locally embed into `𝔸ᵐ_{S'}`, and assume Prop. 3.7 in chart
dimension `m`. Let `cM : 𝒳_M ⟶ 𝔸¹_{S₂}` be its base change and `cX : X' ⟶ 𝔸¹_κ` the coordinate
of the special fibre of `M`. Then there is a morphism `h : W ⟶ X'` whose image contains every
point of `X'` lying over the generic point of `𝔸¹_κ`, at which the pullback of the exchange of
`φ.toGeneric` is invertible: `W` is the special fibre of the slice of `M` over the strict
localization of `𝔸¹_{S₂}` at the generic point of its special fibre. -/
theorem Hom.exists_isIso_map_pullbackExchange_slice {m : ℕ} (ih : TraitChangeInvariance.{u} T m)
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [LocallyOfFiniteType q₁] [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)))
    (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
    (hm : ∀ {S' : Scheme.{u}} (σ : S' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁))),
      (pullback.snd cN σ).LocallyEmbedsInAffineSpace m)
    (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
    (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
    (cX : X' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hcX : cX ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) = M.i ≫ cM)
    (hcXp : cX ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K)) :
    ∃ (W : Scheme.{u}) (h : W ⟶ X'),
      (∀ x : X', IsGenericPoint (cX x) ⊤ → x ∈ Set.range h) ∧
      IsIso ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).map
        ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)) := by
  let := a₁.toAlgebra
  let := a₂.toAlgebra
  have hb₁ := ker_comp_eq_maximalIdeal ι b₂ hb₂
  refine ⟨_, 𝟙 _ ≫ sliceTraitSpecial
    (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂) M cM hcM' hMi,
    fun x hx ↦ ?_, ?_⟩
  · obtain ⟨w, hw⟩ := mem_range_sliceTraitSpecial_of_isGenericPoint ha₂ halg₂ hb₂ M hMi cM hcM' cX
      hcX hcXp x hx
    exact ⟨w, by rw [Category.id_comp]; exact hw⟩
  have hκ : IsIso (Spec.map (CommRingCat.ofHom
      (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂).κMap)) := by
    rw [sliceTraitOfStrictLocalizationHom_κMap]
    have : IsIso (CommRingCat.ofHom (RingHom.id (traitSliceField κ))) :=
      ⟨CommRingCat.ofHom (RingHom.id _), by ext; rfl, by ext; rfl⟩
    infer_instance
  have hsub₁ := (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
    hb₁).subsingleton_primeSpectrum ha₁ halg₁
  have hsub₂ := (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂
    hb₂).subsingleton_primeSpectrum ha₂ halg₂
  have hp₂ : ∀ n : ℕ, (n : ResidueField R₂) = 0 → p ∣ n := fun n hn ↦
    hp n ((ResidueField.map ι).injective (by rw [map_natCast, map_zero, hn]))
  have hdeg₁ := (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
    hb₁).exists_finrank_eq_pow hp
  have hdeg₂ := (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂
    hb₂).exists_finrank_eq_pow hp₂
  have hclosed := sliceTraitOfStrictLocalizationHom_mem_range_algebraMap ι hι c ha₁ halg₁ ha₂ halg₂
    hc hb₂
  have : LocallyOfFiniteType (cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁)) := by
    rw [hcN]; infer_instance
  have : QuasiCompact (cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁)) := by
    rw [hcN]; infer_instance
  have : IsSeparated (cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁)) := by
    rw [hcN]; infer_instance
  have : LocallyOfFiniteType cN :=
    locallyOfFiniteType_of_comp cN (𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁))
  have : QuasiCompact cN := QuasiCompact.of_comp cN
    (𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁))
  have : IsSeparated cN := IsSeparated.of_comp cN
    (𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁))
  have : FaithfulSMul (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁ hb₁).R
      (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁ hb₁).Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (SliceTrait.injective_a _)
  have : FaithfulSMul (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).R
      (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (SliceTrait.injective_a _)
  have : Algebra.IsAlgebraic
      (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁ hb₁).R
      (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁ hb₁).Ω :=
    SliceTrait.isAlgebraic_a _
  have : Algebra.IsAlgebraic (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).R
      (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).Ω :=
    SliceTrait.isAlgebraic_a _
  have hs' : f' ≫ p₁ = p₂ ≫ Spec.map (CommRingCat.ofHom (RingHom.id κ)) := by
    rw [hs, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  have hc' : c.comp (algebraMap R₁ Ω₁) = (algebraMap R₂ Ω₂).comp ι := hc
  have hNj' : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))) := hNj
  have hMj' : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom (algebraMap R₂ Ω₂))) := hMj
  with_reducible
    have key := isIso_map_pullbackExchange_sliceTraitSpecial T
      (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂) hc' φ cN hcN hNj' hNi
      cM hcM' hMj' hMi hcM hgen ih hun p hp hpT
      (fun L' ↦ by obtain ⟨k, hk⟩ := hdeg₁ L'; rw [hk, Nat.cast_pow]; exact hpT.pow k)
      (fun L' ↦ by obtain ⟨k, hk⟩ := hdeg₂ L'; rw [hk, Nat.cast_pow]; exact hpT.pow k)
      hclosed hφ (hm _) (RingHom.id κ) hs' rfl K hK
  exact_mod_proofs key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
