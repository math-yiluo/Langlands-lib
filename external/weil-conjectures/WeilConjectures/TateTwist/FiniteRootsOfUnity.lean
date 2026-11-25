/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CartierReductionData
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReading
public import WeilConjectures.TateTwist.RootsOfUnityPullback

/-!
# Roots of unity with finite coefficients

Let `T` be a finite discrete commutative ring and `X` a scheme on which `N` is invertible. The
free `Λ_X = p_X^* T̲`-module `Λ_X ⊗ μ_N` on the pro-étale sheaf of `N`-th roots of unity, read as
a pro-étale sheaf of `T`-modules (`ProEtale.finiteCoefficientModEquivalence`), is the pullback
`ν^*(T ⊗_ℤ μ_N)` of the étale sheaf `T ⊗_ℤ μ_N`
(`ProEtale.finiteCoefficientModEquivalenceFreeRootsOfUnityIso`).

This follows from the isomorphism of functors
`ProEtale.comparisonUpperStarFreeIso : (Λ_X ⊗ ν^* -) ≅ ν^*(T ⊗_ℤ -)`, both sides being left
adjoint to "take the underlying abelian sheaf and restrict to the étale site", and from the
comparison `ν^* μ_N^ét ≅ μ_N^proét` (`ProEtale.comparisonUpperStarRootsOfUnityIso`).

We also compute the characteristic of the coefficient ring `𝒪_E ⧸ ℓⁿ`
(`ProEtale.CondensedRing.ringChar_integersModPowCoeff`): it is `ℓⁿ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- A natural number `m` vanishes in `𝒪_E ⧸ ℓⁿ` if and only if `ℓⁿ ∣ m`: the norm of `m` in
`ℚ̄_ℓ` is its `ℓ`-adic norm. -/
lemma natCast_eq_zero_integersModPow_iff (n m : ℕ) :
    (m : integersModPow ℓ E n) = 0 ↔ ℓ ^ n ∣ m := by
  rw [← map_natCast (integersModPowMk ℓ E n), integersModPowMk_eq_zero_iff]
  have hm : ((m : integers ℓ E) : E) = (m : E) := by simp
  rw [hm, norm_algebraMap_natCast, ← zpow_natCast, ← zpow_neg_one, ← zpow_mul,
    neg_one_mul, ← Int.cast_natCast, Padic.norm_int_le_pow_iff_dvd]
  exact_mod_cast Iff.rfl

instance charP_integersModPow (n : ℕ) : CharP (integersModPow ℓ E n) (ℓ ^ n) :=
  ⟨natCast_eq_zero_integersModPow_iff ℓ E n⟩

lemma ringChar_integersModPow (n : ℕ) : ringChar (integersModPow ℓ E n) = ℓ ^ n :=
  ringChar.eq _ _

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

section RootsOfUnity

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] (X : Scheme.{u})

/-- Under `finiteCoefficientModEquivalence`, the forgetful functor from module objects over
`Λ_X` corresponds to taking the underlying abelian sheaf. -/
noncomputable def finiteCoefficientModEquivalenceInverseCompForgetIso :
    (finiteCoefficientModEquivalence X T).inverse ⋙
        Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) X) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) Ab.{u + 1}) :=
  Functor.isoWhiskerLeft _
      (eqToIso (finiteCoefficientModEquivalence_functor_comp_sheafCompose X T).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteCoefficientModEquivalence X T).counitIso _ ≪≫
    Functor.leftUnitor _

/-- **Free modules over `Λ_X` and extension of scalars on étale sheaves commute with `ν^*`**:
`Λ_X ⊗ ν^* F ≅ ν^*(T ⊗_ℤ F)` for an étale abelian sheaf `F`, the left-hand side read as a
pro-étale sheaf of `T`-modules. Both functors are left adjoint to the functor taking a pro-étale
sheaf of `T`-modules to the restriction to the étale site of its underlying abelian sheaf. -/
noncomputable def comparisonUpperStarFreeIso :
    ν^*(X)[Ab.{u + 1}] ⋙ Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) X) ⋙
        (finiteCoefficientModEquivalence X T).functor ≅
      Etale.extendScalars (ULift.{u + 1} T) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  (((comparisonAdjunction Ab.{u + 1} X).comp
    (Mod.freeForgetAdjunction (condensedRingObj (Profinite.continuousMapRingObj T) X))).comp
      (finiteCoefficientModEquivalence X T).toAdjunction).leftAdjointUniq
    (((Etale.extendScalarsAdjunction (ULift.{u + 1} T) X).comp
      (comparisonAdjunction _ X)).ofNatIsoRight
      ((NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
        Functor.isoWhiskerRight (finiteCoefficientModEquivalenceInverseCompForgetIso T X).symm
          ν_*(X)[Ab.{u + 1}]))

end RootsOfUnity

variable (X : Scheme.{u}) (N : ℕ)

/-- The pro-étale sheaf of roots of unity `U ↦ μ_N(Γ(U, 𝒪_U))` is isomorphic to the kernel of
`N` on `𝔾ₘ`. -/
noncomputable def rootsOfUnitySheafIsoKernel :
    rootsOfUnitySheaf X N ≅ Scheme.ProEt.rootsOfUnitySheaf X N :=
  rootsOfUnitySheafIso X N ≪≫
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (rootsOfUnityPresheafIsoKernel X N)

/-- **`ν^* μ_N ≅ μ_N`**: if `N` is invertible on `X`, the pullback to the pro-étale site of the
étale sheaf of `N`-th roots of unity is the pro-étale sheaf of `N`-th roots of unity. -/
noncomputable def comparisonUpperStarRootsOfUnityIso (hN : 0 < N) (hX : IsUnit (N : Γ(X, ⊤))) :
    ν^*(X)[Ab.{u + 1}].obj (X.rootsOfUnitySheaf N) ≅ rootsOfUnitySheaf X N :=
  cartierRootsIso X N hN hX ≪≫ (rootsOfUnitySheafIsoKernel X N).symm

/-- **`Λ_X ⊗ μ_N ≅ ν^*(T ⊗_ℤ μ_N)`**: if `N` is invertible on `X`, the free `Λ_X`-module on
the pro-étale sheaf `μ_N`, read as a pro-étale sheaf of `T`-modules, is the pullback of the étale
sheaf of `T`-modules `T ⊗_ℤ μ_N`. -/
noncomputable def finiteCoefficientModEquivalenceFreeRootsOfUnityIso (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T]
    (hN : 0 < N) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence X T).functor.obj
        ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) X)).obj
          (rootsOfUnitySheaf X N)) ≅
      ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
        ((Etale.extendScalars (ULift.{u + 1} T) X).obj (X.rootsOfUnitySheaf N)) :=
  (finiteCoefficientModEquivalence X T).functor.mapIso
      ((Mod.freeFunctor _).mapIso (comparisonUpperStarRootsOfUnityIso X N hN hX).symm) ≪≫
    (comparisonUpperStarFreeIso T X).app (X.rootsOfUnitySheaf N)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- The characteristic of the coefficient ring `𝒪_E ⧸ ℓⁿ` is `ℓⁿ`. -/
lemma ringChar_integersModPowCoeff : ringChar (integersModPowCoeff.{u} ℓ E n) = ℓ ^ n :=
  ringChar.eq _ _

instance : NeZero (ringChar (integersModPowCoeff.{u} ℓ E n)) :=
  ⟨by
    rw [ringChar_integersModPowCoeff]
    exact pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩

end AlgebraicGeometry.ProEtale.CondensedRing
