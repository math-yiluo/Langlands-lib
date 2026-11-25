/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Basic

/-!

# Fixed rational points along an open–closed decomposition

For an open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under an
endomorphism `Φ` of `X`, the rational points of `X` fixed by `Φ` are the disjoint union of those
of `U` fixed by `Φ_U` and those of `Z` fixed by `Φ_Z`
(`ProEtale.CondensedRing.fixedRationalPointsSumEquiv`, the fixed-point side of blueprint
`lemma-additivity-open-subscheme-complement`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A morphism from a reduced scheme whose image lies in the image of a closed immersion factors
through it: the base change of the closed immersion is a surjective closed immersion onto a
reduced scheme, hence an isomorphism (used in blueprint `lemma-additivity-open-subscheme-complement`
for the rational points of the closed piece). -/
lemma exists_comp_eq_of_isClosedImmersion_of_isReduced {T X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : T ⟶ X) [IsReduced T] (h : Set.range g ⊆ Set.range i) :
    ∃ l : T ⟶ Z, l ≫ i = g := by
  have : Surjective (pullback.snd i g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Set.preimage_eq_univ_iff]
    exact h⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i g)
  exact ⟨inv (pullback.snd i g) ≫ pullback.fst i g, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

namespace ProEtale.CondensedRing

variable {k : Type u} [Field k] {X U Z : Over (Spec (.of k))}

/-- A rational point of `X` whose image lies in the image of `j.left` factors through `j`, for an
open immersion or a closed immersion `j` (blueprint
`lemma-additivity-open-subscheme-complement`). -/
lemma RationalPoint.exists_comp_eq_of_exists_lift (j : U ⟶ X) (x : RationalPoint X)
    (h : ∃ l : Spec (.of k) ⟶ U.left, l ≫ j.left = x.left) : ∃ y : RationalPoint U, y ≫ j = x := by
  obtain ⟨l, hl⟩ := h
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w j, reassoc_of% hl, Over.w x]

/-- The image of the unique point of `Spec k` under a rational point. -/
lemma RationalPoint.range_left_subset_iff (x : RationalPoint X) (s : Set X.left)
    (p : Spec (.of k)) :
    Set.range x.left.base ⊆ s ↔ x.left.base p ∈ s := by
  refine ⟨fun h ↦ h ⟨p, rfl⟩, ?_⟩
  rintro h _ ⟨q, rfl⟩
  have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rwa [Subsingleton.elim q p]

/-- Composition with a morphism whose underlying morphism of schemes is a monomorphism is
injective on rational points. -/
lemma RationalPoint.comp_injective (j : U ⟶ X) [Mono j.left] :
    Function.Injective (fun y : RationalPoint U ↦ y ≫ j) := fun _ _ h ↦
  Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg CommaMorphism.left h))

/-- A rational point of `U` is fixed by `Φ_U` if and only if its image in `X` is fixed by `Φ`, for
`Φ_U ≫ j = j ≫ Φ` with `j.left` a monomorphism. -/
lemma RationalPoint.comp_eq_self_iff {Φ : X ⟶ X} {ΦU : U ⟶ U} (j : U ⟶ X) [Mono j.left]
    (hj : ΦU ≫ j = j ≫ Φ) (y : RationalPoint U) : (y ≫ j) ≫ Φ = y ≫ j ↔ y ≫ ΦU = y := by
  rw [Category.assoc, ← hj, ← Category.assoc]
  exact (RationalPoint.comp_injective j).eq_iff

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left]

/-- The map from the fixed rational points of `U` and of `Z` to those of `X`. -/
noncomputable def fixedRationalPointsSumMap (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) :
    {y : RationalPoint U // y ≫ ΦU = y} ⊕ {z : RationalPoint Z // z ≫ ΦZ = z} →
      {x : RationalPoint X // x ≫ Φ = x}
  | .inl y => ⟨y.1 ≫ j, (RationalPoint.comp_eq_self_iff j hj y.1).2 y.2⟩
  | .inr z => ⟨z.1 ≫ i, (RationalPoint.comp_eq_self_iff i hi z.1).2 z.2⟩

/-- **The fixed rational points along an open–closed decomposition** (blueprint
`lemma-additivity-open-subscheme-complement`, the fixed-point side): for an open immersion
`j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under `Φ`, the rational points of `X`
fixed by `Φ` are the disjoint union of those of `U` fixed by `Φ_U` and those of `Z` fixed by
`Φ_Z`, through `y ↦ y ≫ j` and `z ↦ z ≫ i`. -/
noncomputable def fixedRationalPointsSumEquiv
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) :
    {y : RationalPoint U // y ≫ ΦU = y} ⊕ {z : RationalPoint Z // z ≫ ΦZ = z} ≃
      {x : RationalPoint X // x ≫ Φ = x} :=
  Equiv.ofBijective (fixedRationalPointsSumMap hj hi) <| by
    have p : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨?_, ?_⟩
    · rintro (y | z) (y' | z') h <;> simp only [fixedRationalPointsSumMap, Subtype.mk.injEq] at h
      · exact congrArg Sum.inl (Subtype.ext (RationalPoint.comp_injective j h))
      · refine (Set.disjoint_left.1 hcompl.disjoint ⟨y.1.left.base p, rfl⟩ ?_).elim
        refine ⟨z'.1.left.base p, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← h]
        rfl
      · refine (Set.disjoint_left.1 hcompl.disjoint ⟨y'.1.left.base p, rfl⟩ ?_).elim
        refine ⟨z.1.left.base p, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
        rfl
      · exact congrArg Sum.inr (Subtype.ext (RationalPoint.comp_injective i h))
    · rintro ⟨x, hx⟩
      rcases hcompl.codisjoint.top_le (Set.mem_univ (x.left.base p)) with h | h
      · obtain ⟨y, rfl⟩ := RationalPoint.exists_comp_eq_of_exists_lift j x
          ⟨IsOpenImmersion.lift j.left x.left ((x.range_left_subset_iff _ p).2 h),
            IsOpenImmersion.lift_fac _ _ _⟩
        exact ⟨.inl ⟨y, (RationalPoint.comp_eq_self_iff j hj y).1 hx⟩, rfl⟩
      · have : IsReduced (point k).left := inferInstanceAs (IsReduced (Spec (.of k)))
        obtain ⟨z, rfl⟩ := RationalPoint.exists_comp_eq_of_exists_lift i x
          (exists_comp_eq_of_isClosedImmersion_of_isReduced i.left x.left
            ((x.range_left_subset_iff _ p).2 h))
        exact ⟨.inr ⟨z, (RationalPoint.comp_eq_self_iff i hi z).1 hx⟩, rfl⟩

/-- The fixed point of `X` attached to a fixed point `y` of `U` is `y ≫ j`. -/
@[simp]
lemma fixedRationalPointsSumEquiv_inl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (y : {y : RationalPoint U // y ≫ ΦU = y}) :
    fixedRationalPointsSumEquiv hcompl hj hi (.inl y) =
      ⟨y.1 ≫ j, (RationalPoint.comp_eq_self_iff j hj y.1).2 y.2⟩ :=
  rfl

/-- The fixed point of `X` attached to a fixed point `z` of `Z` is `z ≫ i`. -/
@[simp]
lemma fixedRationalPointsSumEquiv_inr
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (z : {z : RationalPoint Z // z ≫ ΦZ = z}) :
    fixedRationalPointsSumEquiv hcompl hj hi (.inr z) =
      ⟨z.1 ≫ i, (RationalPoint.comp_eq_self_iff i hi z.1).2 z.2⟩ :=
  rfl

end ProEtale.CondensedRing

end AlgebraicGeometry
