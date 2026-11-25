/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.FiniteLocallyConstantCokernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible.FinitelyPresented
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible.Regular

/-!
# Constructible module objects with finite coefficients are constructible sheaves

Let `T` be a finite discrete commutative ring and `X` a scheme. A module object `M` over
`Λ_X = p_X^* T̲` is constructible (`ProEtale.IsConstructibleModuleObject`) if on the strata of a
stratification of `X` it is pro-étale locally finitely presented. This file shows that the
corresponding sheaf of `T`-modules (`ProEtale.finiteCoefficientModEquivalence`) is constructible
in the intrinsic sense of `ProEtale.IsConstructible`: on the strata it is locally constant with
finite stalks. Indeed, on a member `W` of a pro-étale covering family of a stratum the pullback is
the cokernel of a morphism of free modules `Λ_W^m ⟶ Λ_W^n`, which corresponds to a morphism of
constant sheaves `(T^m)_W ⟶ (T^n)_W`, whose cokernel is locally constant with finite stalks
(`ProEtale.isFiniteLocallyConstant_cokernel`).

## Main statements

- `ProEtale.isConstructible_finiteCoefficientModEquivalence_functor_obj`: a constructible module
  object over `Λ_X` is a constructible sheaf of `T`-modules.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X : Scheme.{u}}

/-- A constructible module object over `Λ_X = p_X^* T̲` is a constructible sheaf of `T`-modules:
on the strata of a stratification of `X` it is locally constant with finite stalks. -/
theorem isConstructible_finiteCoefficientModEquivalence_functor_obj
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)}
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj T) X) M) :
    IsConstructible (ULift.{u + 1} T) ((finiteCoefficientModEquivalence X T).functor.obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hS a
  refine IsFiniteLocallyConstant.of_cover (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.f i.down) ?_
    fun i ↦ ?_
  · have h : Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down)
        (fun i ↦ 𝒰.f i.down) = 𝒰.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
      exact Presieve.ofArrows.mk (⟨i⟩ : ULift.{u + 1} 𝒰.I₀)
    rw [h]
    exact 𝒰.mem₀
  · exact isFiniteLocallyConstant_of_iso
      ((upperStarFiniteCoefficientModEquivalenceIso (𝒰.f i.down) T).app _ ≪≫
        ((𝒰.f i.down)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]).mapIso
          ((upperStarFiniteCoefficientModEquivalenceIso (S.immersion a) T).app M))
      (isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj T _
        (isFinitelyPresented_upperStar_obj_upperStar_obj _ _ _ (h𝒰 i.down)))

end AlgebraicGeometry.ProEtale
