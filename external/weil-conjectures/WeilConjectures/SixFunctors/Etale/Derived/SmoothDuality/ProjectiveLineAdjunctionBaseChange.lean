/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.LowerShriekTraceCounitBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineTraceBaseChange

/-!
# The projective-line adjunction commutes with base change

For a normalized Tate twist, the projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]` of
`q : ℙ¹_S ⟶ S` (`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`) commutes with every
base change `S' ⟶ S`, in the sense of
`AlgebraicGeometry.Etale.ProjectiveLineAdjunctionBaseChange` (blueprint
`proposition-adjunction-projective-line`, subsection `proposition-adjunction-projective-line`): the
counits of these adjunctions are the trace counits built from the trace of the projective line,
which commutes with base change
(`AlgebraicGeometry.Etale.projectiveLineTrace_lowerShriek_baseChange`), and so do the projection map
and the identification `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K`
(`AlgebraicGeometry.Etale.lowerShriekTraceCounit_twistShift_baseChange`).

## Implementation notes

The definition of the trace `AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace` carries
auxiliary proofs of the instances it uses; they are replaced by the instances themselves
(`AlgebraicGeometry.Etale.proof_eq_instance`) before the trace is compared with the statements of
other files, so that the kernel compares syntactically equal terms.

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace_baseChange`
- `AlgebraicGeometry.Etale.projectiveLineCounit_baseChange`
- `AlgebraicGeometry.Etale.projectiveLineAdjunctionBaseChange_of_isNormalized`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

set_option checkBinderAnnotations false in
/-- A proof of a proposition `T` is the proof of `T` found by instance search. Rewriting with it
replaces an auxiliary proof (for instance one abstracted from the body of a definition) by the
corresponding instance. -/
theorem proof_eq_instance {T : Prop} [h : T] (p : T) : p = h :=
  rfl

section Counit

variable {Λ} [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] {S S' : Scheme.{u}}
  [HasInvertibleExponent Λ S] [HasInvertibleExponent Λ S']

omit [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes is the unit comparison of the
monoidal structure of `Lf^*`. -/
theorem leftDerivedUpperStarConstantComplexIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom :=
  leftDerivedUpperStarOplaxMonoidal_η _ f

section Braided

-- The braiding of `ModuleCat Λ` used in the definition of
-- `AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

omit [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- Composites with target the unit `𝟙_` of the derived tensor product are composites with target
the constant complex. -/
theorem comp_tensorUnit_eq_comp_constantComplex {X : Scheme.{u}}
    {A B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (g : B ⟶ A)
    (f : A ⟶ constantComplex Λ X) :
    @CategoryStruct.comp _ _ B A (𝟙_ _) g f =
      @CategoryStruct.comp _ _ B A (constantComplex Λ X) g f :=
  rfl

end Braided

set_option linter.auxLemma false in
/-- **Base change of the trace of the projective line** on the compactly supported direct image:
for `g : S' ⟶ S` with base change `g' : ℙ¹_{S'} ⟶ ℙ¹_S`, the trace
`t_q : Rq_! Λ(1)[2] ⟶ Λ_S` (`AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace`) pulled
back along `g` is `Ex_!` followed by `Lg'^*(Λ(1)[2]) ≅ Λ(1)[2]` and the trace of `ℙ¹_{S'}`
(`AlgebraicGeometry.Etale.projectiveLineTrace_lowerShriek_baseChange`). -/
theorem projectiveLineLowerShriekTrace_baseChange (g : S' ⟶ S) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (projectiveLineLowerShriekTrace Λ S) ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom =
      (rightDerivedLowerShriekBaseChangeMap Λ
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g)).app _ ≫
        (R((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_![ModuleCat.{u + 1} Λ]).map
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)).hom ≫
          projectiveLineLowerShriekTrace Λ S' := by
  have htr := projectiveLineTrace_lowerShriek_baseChange Λ g
  rw [projectiveLineLowerShriekTrace, projectiveLineLowerShriekTrace,
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_2 Λ S),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_4 Λ S),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_5 Λ S),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_3 S),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_6 S),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_1 Λ S),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_2 Λ S'),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_4 Λ S'),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_5 Λ S'),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_3 S'),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_6 S'),
    proof_eq_instance (projectiveLineLowerShriekTrace._proof_1 Λ S'),
    proof_eq_instance (lowerShriekTraceCounit._proof_2 Λ (X := S)),
    proof_eq_instance (lowerShriekTraceCounit._proof_1 Λ (X := S)),
    proof_eq_instance (lowerShriekTraceCounit._proof_2 Λ (X := S')),
    proof_eq_instance (lowerShriekTraceCounit._proof_1 Λ (X := S'))]
  simp only [comp_tensorUnit_eq_comp_constantComplex]
  rw [htr, ← leftDerivedUpperStarConstantComplexIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Braided

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the definition of
-- `AlgebraicGeometry.Etale.projectiveLineCounit`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

/-- **Base change of the projective-line counit** (blueprint
`proposition-adjunction-projective-line`). For `g : S' ⟶ S` with base change `g' : ℙ¹_{S'} ⟶ ℙ¹_S`,
the counits `ε_K : Rq_!(q^* K(1)[2]) ⟶ K` of `AlgebraicGeometry.Etale.projectiveLineCounit` are
compatible with `Ex_!` and `Lg'^*(Lq^* K(1)[2]) ≅ Lq'^* Lg^* K(1)[2]`: the trace commutes with base
change (`AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace_baseChange`), and so do the
projection map and the identification `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K`
(`AlgebraicGeometry.Etale.lowerShriekTraceCounit_twistShift_baseChange`). -/
theorem projectiveLineCounit_baseChange (g : S' ⟶ S)
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ
        (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g)).app
        ((twistShift Λ _ 1).obj
          ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (R((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarTwistShiftIso Λ
            (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) 1 _).hom ≫
          (twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1).map
            ((derivedSquareUpperStarIso _
              (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).inv.app
                K)) ≫
        projectiveLineCounit Λ S' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((g)^*[ModuleCat.{u + 1} Λ])).map (projectiveLineCounit Λ S K) := by
  rw [projectiveLineCounit, projectiveLineCounit]
  exact lowerShriekTraceCounit_twistShift_baseChange _ 1 (projectiveLineLowerShriekTrace Λ S)
    (projectiveLineLowerShriekTrace Λ S') (projectiveLineLowerShriekTrace_baseChange g) K

end Braided

end Counit

/-- Compatibility required from `proposition-adjunction-projective-line`:
blueprint `proposition-adjunction-projective-line`.

**The projective-line adjunction commutes with base change.** For a normalized Tate twist and
every scheme `S` on which the exponent of `Λ` is invertible, the adjunctions
`Rq_! ⊣ Lq^*(1)[2]` of the projective line `q : ℙ¹_S ⟶ S` and of its base change along any
`g : S' ⟶ S` have counits compatible with the compact-support base change, in the sense of
`AlgebraicGeometry.Etale.ProjectiveLineAdjunctionBaseChange`: the counits are the trace counits
of `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`, built from the trace and the
projection formula, both of which commute with base change
(`AlgebraicGeometry.Etale.projectiveLineCounit_baseChange`). -/
theorem projectiveLineAdjunctionBaseChange_of_isNormalized [inst : HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] : ProjectiveLineAdjunctionBaseChange Λ := by
  obtain ⟨κ, rfl, hκ⟩ := HasTateTwist.IsNormalized.exists_hasKummerClass (Λ := Λ) (inst := inst)
  intro S _ S' g
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
  have : HasInvertibleExponent Λ S' := .of_hom g
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S') := .of_hom (_ ↘ S')
  obtain ⟨adj, hadj⟩ := exists_projectiveLineAdjunction Λ S
  obtain ⟨adj', hadj'⟩ := exists_projectiveLineAdjunction Λ S'
  refine ⟨adj, adj', fun K ↦ ?_⟩
  rw [hadj, hadj']
  exact projectiveLineCounit_baseChange g K

end Etale

end AlgebraicGeometry
