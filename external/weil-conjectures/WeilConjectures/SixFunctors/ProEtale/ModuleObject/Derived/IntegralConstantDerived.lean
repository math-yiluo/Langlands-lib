/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantRegularEnd
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Derived tensor products and duals of constant `𝒪_E`-modules

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with uniformizer `ϖ`, and let
`C = ⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` be a constant module object over `𝒪_{E,V}` on a scheme `V`
(`ProEtale.integralConstantModule`). Each `𝒪_E/ϖ^e` has the free resolution
`𝒪_E --ϖ^e--> 𝒪_E`, so:

* the derived tensor product `C[0] ⊗ᴸ C'[0]` of two constant modules has locally finitely
  presented cohomology sheaves (the constant modules `Tor_i^{𝒪_E}`), concentrated in degrees
  `-1` and `0` (`ProEtale.CondensedRing.integralConstantModule_tensorObj_homology`);
* `C[q]` is dualizable in `D(Mod_{𝒪_{E,V}})`, with a dual concentrated in degrees `[-q, 1 - q]`
  whose cohomology sheaves are locally finitely presented
  (`ProEtale.CondensedRing.exists_exactPairing_integralConstantModule`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A finitely presented module object is pro-étale locally finitely presented, for the identity
cover. -/
private lemma isLocallyFinitelyPresented_of_isFinitelyPresented'
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M :=
  (isLocallyFinitelyPresented_iff M).2 ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _),
    fun _ ↦ IsFinitelyPresented.upperStar Λ _ hM⟩

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (V : Scheme.{u}) (ϖ : PadicAlgCl.integers ℓ E)
  (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})

/-- The property of being a finitely presented module object over `𝒪_{E,V}`. -/
private abbrev isFinitelyPresentedProperty : ObjectProperty
    (Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)) :=
  fun M ↦ Mod.IsFinitelyPresented _ M

private instance : (isFinitelyPresentedProperty ℓ E V).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ h.of_iso e⟩

omit [FiniteDimensional ℚ_[ℓ] E] in
omit [FiniteDimensional ℚ_[ℓ] E] in
include hϖ in
/-- The multiplication by a power of a uniformizer on `𝒪_{E,V}` is a monomorphism. -/
private lemma mono_padicIntegersRegularEndOfAlgebra_pow (a : ℕ) :
    Mono (padicIntegersRegularEndOfAlgebra V ℓ E (ϖ ^ a)) :=
  mono_padicIntegersRegularEndOfAlgebra V ℓ E (pow_ne_zero a fun h ↦
    PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E (by rw [hϖ, h, Ideal.span_singleton_eq_bot]))

omit [FiniteDimensional ℚ_[ℓ] E] in
omit [FiniteDimensional ℚ_[ℓ] E] in
include hϖ in
/-- The derived tensor product of two constant `𝒪_E`-modules placed in degree `0` has finitely
presented cohomology sheaves, concentrated in degrees `-1` and `0`. -/
private lemma torConcentrated_integralConstantModule (k r k' r' : ℕ) (e : Fin k → ℕ)
    (e' : Fin k' → ℕ) :
    DerivedCategory.TorConcentrated (isFinitelyPresentedProperty ℓ E V)
      (integralConstantModule ℓ E V ϖ k r e) (integralConstantModule ℓ E V ϖ k' r' e') := by
  have := mono_padicIntegersRegularEndOfAlgebra_pow ℓ E V ϖ hϖ
  exact DerivedCategory.torConcentrated_biprod_cokernel_unit
    (P := isFinitelyPresentedProperty ℓ E V)
    (fun _ hX ↦ Mod.IsFinitelyPresented.of_isZero hX) (fun _ _ hX hY ↦ hX.biprod hY)
    (fun a ↦ padicIntegersRegularEndOfAlgebra V ℓ E (ϖ ^ a)) (fun a b hab ↦ by
      rw [← pow_sub_mul_pow ϖ hab, padicIntegersRegularEndOfAlgebra_mul]
      exact comp_whiskerRight_cokernel_eq_zero _ _)
    (fun _ ↦ Mod.isFinitelyPresented_cokernel_regular _) Mod.isFinitelyPresented_regular e e'

omit [FiniteDimensional ℚ_[ℓ] E] in
include hϖ in
/-- The derived tensor product of two constant `𝒪_E`-modules placed in degree `0` has locally
finitely presented cohomology sheaves, concentrated in degrees `-1` and `0`. -/
theorem integralConstantModule_tensorObj_homology (k r k' r' : ℕ) (e : Fin k → ℕ)
    (e' : Fin k' → ℕ) (n : ℤ) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k r e) ⊗
            (DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k' r' e'))) ∧
      ((n < -1 ∨ 0 < n) → IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k r e) ⊗
            (DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k' r' e')))) :=
  have h := torConcentrated_integralConstantModule ℓ E V ϖ hϖ k r k' r' e e' n
  ⟨isLocallyFinitelyPresented_of_isFinitelyPresented' h.1, h.2⟩

omit [FiniteDimensional ℚ_[ℓ] E] in
include hϖ in
/-- A constant `𝒪_E`-module placed in degree `q` is dualizable in `D(Mod_{𝒪_{E,V}})`, with a
left dual concentrated in degrees `[-q, 1 - q]` whose cohomology sheaves are locally finitely
presented. -/
theorem exists_exactPairing_integralConstantModule (k r : ℕ) (e : Fin k → ℕ) (q : ℤ) :
    ∃ D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)),
      D.IsGE (-q) ∧ D.IsLE (1 - q) ∧
      (∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)
        ((DerivedCategory.homologyFunctor _ n).obj D)) ∧
      Nonempty (ExactPairing D
        ((DerivedCategory.singleFunctor _ q).obj (integralConstantModule ℓ E V ϖ k r e))) := by
  have := mono_padicIntegersRegularEndOfAlgebra_pow ℓ E V ϖ hϖ
  obtain ⟨D, ha, hb, hP, hp⟩ := DerivedCategory.hasBoundedDual_singleFunctor_biprod_cokernel_unit
    (P := isFinitelyPresentedProperty ℓ E V) (fun _ hX ↦ Mod.IsFinitelyPresented.of_isZero hX)
    (fun _ _ hX hY ↦ hX.biprod hY) (fun _ ↦ Mod.isFinitelyPresented_cokernel_regular _)
    Mod.isFinitelyPresented_regular (fun a ↦ padicIntegersRegularEndOfAlgebra V ℓ E (ϖ ^ a))
    (r := r) e q
  rw [neg_add_eq_sub] at hb
  exact ⟨D, ha, hb, fun n ↦ isLocallyFinitelyPresented_of_isFinitelyPresented' (hP n), hp⟩

end AlgebraicGeometry.ProEtale.CondensedRing
