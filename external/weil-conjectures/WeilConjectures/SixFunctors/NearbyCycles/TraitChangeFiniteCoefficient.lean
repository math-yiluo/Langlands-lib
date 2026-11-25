/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.Tactic.TransportExact

/-!

# Invariance of nearby cycles under change of trait, finite coefficients

The pullback exchange form of Deligne's theorem (SGA 4½, [Th. finitude], Prop. 3.7) with
coefficients a finite discrete ring `T` in which the residual characteristic is invertible
(`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`): for a change of
strictly henselian traits the pullback exchange `α : Lf'^* Ψ_N B ⟶ Ψ_M (Lf^* B)` is invertible
at every `B` whose restriction to the geometric generic fibre of `N` is bounded below of étale
origin. It is `NearbyCyclesModel.traitChangeInvariance` after replacing the special fibre of `N`
by its fibre over the residue field of the target trait, which does not change the base change
morphism of `Rj_*` on the special fibre of `M`
`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_toGenericWithSpecial`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂}
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Invariance of nearby cycles under change of strictly henselian trait, finite coefficients
`T`**: in the situation of `NearbyCyclesModel.TraitChangeInvariance`, with the special fibre of
`N` arbitrary, the pullback exchange `Lf'^* Ψ_N B ⟶ Ψ_M (Lf^* B)` is invertible at every `B`
whose restriction to the geometric generic fibre of `N` is bounded below of étale origin. -/
theorem isIso_pullbackExchange_app_of_isPullback_trait_finite [IsLocalHom ι]
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)))
    (hB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T⟧).obj B))) :
    IsIso ((φ.pullbackExchange (Profinite.continuousMapRingObj T)).app B) := by
  refine (Scheme.Hom.exists_locallyEmbedsInAffineSpace q₁).elim fun m hm ↦ ?_
  have hw : (M.i ≫ φ.total) ≫ q₁ = p₂ ≫ Spec.map (CommRingCat.ofHom (b₂.comp ι)) := by
    rw [Category.assoc, hφ.w, reassoc_of% hMi.w, CommRingCat.ofHom_comp, Spec.map_comp]
  have h := (NearbyCyclesModel.traitChangeInvariance T m).isIso ι hι hun p hp hpT a₁ a₂ c ha₁
    ha₂ halg₁ halg₂ hc b₂ hb₂ (φ.toGenericWithSpecial (pullback.fst _ _)
      (pullback.lift (M.i ≫ φ.total) p₂ hw) (pullback.lift_fst _ _ _)) q₁ inferInstance
    inferInstance inferInstance hm g₁ hNj (pullback.snd _ _) (IsPullback.of_hasPullback _ _) q₂
    g₂ hMj p₂ hMi hφ hgen (pullback.lift_snd _ _ _) _ hB
  have h' :=
    NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_toGenericWithSpecial
      _ φ _ _ _ _ h
  have h₃ := NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app _ φ B
    (by transport_exact h')
  exact_mod_proofs h₃


end AlgebraicGeometry.ProEtale.CondensedRing
