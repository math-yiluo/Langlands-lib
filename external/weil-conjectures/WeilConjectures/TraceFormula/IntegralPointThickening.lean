/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.TraceFormula.Dualizing

/-!

# Integration over a nilpotent thickening of a rational point

Let `B` be a proper `k`-scheme whose underlying space is a single rational point `b : s ⟶ B`,
for instance a nilpotent thickening of `s = Spec k`. Then the integral
`∫_B : BorelMooreSection ℓ B ⟶ End ℚ̄_ℓ,s` is injective
(`ProEtale.CondensedRing.BorelMooreSection.integral_injective`).

The point `b` is a section of the separated structure morphism `a : B ⟶ s`, hence a closed
immersion, and it is surjective, so it is a finite universal homeomorphism. By topological
invariance (`ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`)
the unit of `Lb^* ⊣ Rb_*` is an isomorphism; since `La^* ⋙ Lb^* ≅ L(b ≫ a)^* = L(𝟙 s)^* ≅ 𝟭`
is fully faithful, the unit of `La^* ⊣ Ra_*` is an isomorphism
(`ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction_of_section`).
The integral is the composition with this unit, followed by isomorphisms and the bijection
`α ↦ α^♭`, hence injective.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section RationalPoint

variable {k : Type u} [Field k] {B : Over (Spec (.of k))}

/-- A rational point `b : s ⟶ B` is a closed immersion, being a section of the structure
morphism of `B` over the one-point space `s`. -/
instance isClosedImmersion_left_rationalPoint (b : RationalPoint B) : IsClosedImmersion b.left :=
  isClosedImmersion_of_comp_eq_id B.hom b.left (by simp)

/-- A surjective rational point `b : s ⟶ B` is a universal homeomorphism: it is a closed
immersion, hence integral and universally injective. -/
lemma isUniversalHomeomorphism_left_of_range_eq_univ (b : RationalPoint B)
    (hb : Set.range b.left.base = Set.univ) : IsUniversalHomeomorphism b.left :=
  have : Surjective b.left := ⟨Set.range_eq_univ.mp hb⟩
  {}

end RationalPoint

section Unit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {B : Over (Spec (.of k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- If `B` has a surjective rational point `b : s ⟶ B`, the unit `𝟭 ⟶ La^* ⋙ Ra_*` of the
adjunction `La^* ⊣ Ra_*` for the structure morphism `a : B ⟶ s` is an isomorphism: `b` is a
finite universal homeomorphism, so the unit of `Lb^* ⊣ Rb_*` is an isomorphism by topological
invariance, and `La^* ⋙ Lb^* ≅ L(b ≫ a)^* = L(𝟙 s)^* ≅ 𝟭` is fully faithful. -/
theorem isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction_toPoint
    (b : RationalPoint B) (hb : Set.range b.left.base = Set.univ) :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint B)).unit := by
  have := isUniversalHomeomorphism_left_of_range_eq_univ b hb
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction ℓ b
  have h : b ≫ toPoint B = 𝟙 (point k) := toPoint_ext _ _
  let e : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint B) ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b ≅ 𝟭 _ :=
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ b (toPoint B)).symm ≪≫
      eqToIso (by rw [h]) ≪≫
      boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)
  have := Functor.Full.of_iso e.symm
  have := Functor.Faithful.of_iso e.symm
  exact Adjunction.isIso_unit_of_fullyFaithful_comp _
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ b)

end Unit

namespace BorelMooreSection

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]

/-- **Integration over a thickened point is injective**: if the proper `k`-scheme `B` has a
rational point `b : s ⟶ B` whose image is all of `B`, for instance if `B` is a nilpotent
thickening of `s`, then the integral `α ↦ ∫_B α` of Borel–Moore sections is injective. -/
theorem integral_injective (b : RationalPoint B) (hb : Set.range b.left.base = Set.univ) :
    Function.Injective (integral (ℓ := ℓ) (X := B)) := by
  intro α β h
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction_toPoint ℓ b hb
  unfold integral at h
  have h' := congrArg End.asHom h
  rw [cancel_epi, cancel_epi, cancel_epi] at h'
  exact Equiv.injective _ h'

end BorelMooreSection

end AlgebraicGeometry.ProEtale.CondensedRing
