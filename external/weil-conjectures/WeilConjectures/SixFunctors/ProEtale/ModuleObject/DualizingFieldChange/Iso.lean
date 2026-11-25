/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Global
public import WeilConjectures.CategoryTheory.Adjunction.IsIsoOfMap

/-!

# Base change of dualizing complexes: invertibility from an abstract isomorphism

Let `X` be a proper `k₁`-scheme, `X'` a proper `k₂`-scheme with a cartesian square
`π ≫ a = a' ≫ πₛ` over `πₛ : Spec k₂ ⟶ Spec k₁`, and `φ : π^* ω_X ⟶ ω_{X'}` the comparison of the
dualizing complexes (`ProEtale.CondensedRing.dualizingComplexBaseChange`). This file proves that
`φ` is an isomorphism as soon as `π^* ω_X` and `ω_{X'}` are isomorphic in any way
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_iso`).

Indeed, for an isomorphism `ψ : π^* ω_X ≅ ω_{X'}`, the endomorphism `ψ⁻¹ ≫ φ` of `ω_{X'}` is
invertible on global sections
(`ProEtale.CondensedRing.isIso_lowerStar_map_dualizingComplexBaseChange`),
and an endomorphism of the dualizing complex `ω_{X'} = Ra'^! ℚ̄_ℓ` of a proper scheme which is
invertible on global sections is invertible
(`ProEtale.CondensedRing.isIso_of_isIso_lowerStar_map_dualizingComplex`, an instance of
`CategoryTheory.Adjunction.isIso_of_isIso_map_leftAdjoint` for `Ra'_* ⊣ Ra'^!`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **An endomorphism of the dualizing complex of a proper scheme which is invertible on global
sections is invertible**: `ω_X = Ra^! ℚ̄_ℓ` for the adjunction `Ra_* ⊣ Ra^!`, and
`CategoryTheory.Adjunction.isIso_of_isIso_map_leftAdjoint` applies. -/
theorem isIso_of_isIso_lowerStar_map_dualizingComplex {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsProper (toPoint X).left] (f : dualizingComplex ℓ X ⟶ dualizingComplex ℓ X)
    [IsIso ((boundedConstructibleLowerStar ℓ (toPoint X)).map f)] : IsIso f :=
  (properLowerStarUpperShriekAdjunction ℓ X).isIso_of_isIso_map_leftAdjoint (d := 𝟙_ _) f

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left]
  {X' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left]
  {π : X'.left ⟶ X.left} {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)}
  (e : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
    𝟙_ _)

/-- **Base change of dualizing complexes from an abstract isomorphism**: if `π^* ω_X` and
`ω_{X'}` are isomorphic, then the comparison `φ : π^* ω_X ⟶ ω_{X'}` is an isomorphism. -/
theorem isIso_dualizingComplexBaseChange_of_iso [IsIso e]
    (sq : IsPullback π (toPoint X').left (toPoint X).left πₛ)
    (ψ : (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj (dualizingComplex ℓ X) ≅
      dualizingComplex ℓ X') :
    IsIso (dualizingComplexBaseChange ℓ e sq) := by
  have := isIso_lowerStar_map_dualizingComplexBaseChange ℓ e sq
  have : IsIso ((boundedConstructibleLowerStar ℓ (toPoint X')).map
      (ψ.inv ≫ dualizingComplexBaseChange ℓ e sq)) := by
    rw [Functor.map_comp]
    infer_instance
  have := isIso_of_isIso_lowerStar_map_dualizingComplex ℓ X'
    (ψ.inv ≫ dualizingComplexBaseChange ℓ e sq)
  exact IsIso.of_isIso_comp_left ψ.inv _

end AlgebraicGeometry.ProEtale.CondensedRing
