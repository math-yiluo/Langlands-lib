/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.IntegralPointThickening
public import WeilConjectures.TraceFormula.Specialization.DeformationSpecialFibreComp
public import WeilConjectures.TraceFormula.Specialization.SpecialFixedLocus
public import WeilConjectures.TraceFormula.Specialization.ComponentModelHom
public import WeilConjectures.TraceFormula.Specialization.DeformationProperPoint

/-!

# The special fibre of a component of the fixed locus

Let `c` be contracting at `y`, `F` a fixed locus of `c` and `j : B ⟶ F` with a rational point `b`
of `B` over `y` (`b ≫ j ≫ ι = y`). The closed model morphism `componentModelHom` gives on special
fibres `b'' : B'' = N_b B ⊗ k' ⟶ C' = N_y C ⊗ k'`. Since `c₁ ∘ ι ∘ j = c₂ ∘ ι ∘ j`, the two special
legs agree on `B''`, so `b''` factors through the special fixed locus `F'`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.componentSpecialLift`).

If `B ⊂ F ⊂ C` is a closed immersion, the factorization `B'' ⟶ F'` is a closed immersion which is
surjective (`F'` is a single point and `B''` contains the vertex), hence a finite universal
homeomorphism (`isUniversalHomeomorphism_componentSpecialLift`). By topological invariance the
unit of `L(·)^* ⊣ R(·)_*` is then an isomorphism
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.isIso_unit_componentSpecialLift`, in
`ComponentSpecialLiftUnit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Functions vanishing at `y` pull back along `f` to functions vanishing at `x` if `x ≫ f = y`. -/
lemma map_siteIdeal_ker_le_of_comp_eq {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) {x : RationalPoint X} {y : RationalPoint Y} (h : x ≫ f = y) :
    ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1),
      (y.left.ker.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤ x.left.ker.siteIdeal U' :=
  IdealSheafData.map_siteIdeal_le_of_comap_le _ (by
    rw [IdealSheafData.comap_le_ker_iff, ← Over.comp_left, h])

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)

/-- The morphism of special fibres `b'' : B'' ⟶ C'` over `B ⊂ F ⊂ C`, the special component of
`componentModelHom`. -/
noncomputable abbrev componentSpecialFibreMap :
    deformationSpecialFibre B b.left.ker k' ⟶ deformationSpecialFibre c.C y.left.ker k' :=
  deformationSpecialFibreMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k'

include hc in
/-- The two special legs agree on the special fibre `B''` of the deformation of `B`. -/
lemma componentSpecialFibreMap_specialLeg :
    componentSpecialFibreMap k' j hb ≫ hc.specialLeg₁ k' =
      componentSpecialFibreMap k' j hb ≫ hc.specialLeg₂ k' := by
  rw [deformationSpecialFibreMap_comp k' _ _ _ _
      (map_siteIdeal_ker_le_of_comp_eq _ (by rw [← Category.assoc, hb])),
    deformationSpecialFibreMap_comp k' _ _ _ _
      (map_siteIdeal_ker_le_of_comp_eq _ (by rw [← Category.assoc, hb, hc.comp_c₁_eq_comp_c₂]))]
  exact deformationSpecialFibreMap_eq_of_eq k' _ _ (by simp only [Category.assoc, F.w]) _

/-- If `B ⊂ F ⊂ C` is a closed immersion, so is `b'' : B'' ⟶ C'`: it is the base change of the
closed immersion of total spaces `isClosedImmersion_componentModelHom_total`. -/
lemma isClosedImmersion_componentSpecialFibreMap [IsClosedImmersion (j ≫ F.ι).left] :
    IsClosedImmersion (componentSpecialFibreMap k' j hb).left := by
  have : IsClosedImmersion (deformationTotalMap (j ≫ F.ι)
      (map_siteIdeal_le_ker_component j hb) k') := isClosedImmersion_componentModelHom_total k' j hb
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_deformationSpecialFibreMap k' (j ≫ F.ι) _) this

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- The factorization `B'' ⟶ F'` of `b'' : B'' ⟶ C'` through the special fixed locus. -/
noncomputable def componentSpecialLift :
    deformationSpecialFibre B b.left.ker k' ⟶ (hc.specialFixedLocus k').F :=
  Fork.IsLimit.lift (hc.specialFixedLocus k').isLimit (componentSpecialFibreMap k' j hb)
    (hc.componentSpecialFibreMap_specialLeg k' j hb)

@[reassoc (attr := simp)]
lemma componentSpecialLift_ι :
    hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').ι =
      componentSpecialFibreMap k' j hb :=
  Fork.IsLimit.lift_ι' _ _ _

/-- If `B ⊂ F ⊂ C` is a closed immersion, the factorization `B'' ⟶ F'` is a closed immersion. -/
lemma isClosedImmersion_componentSpecialLift [IsClosedImmersion (j ≫ F.ι).left] :
    IsClosedImmersion (hc.componentSpecialLift k' j hb).left := by
  have := isClosedImmersion_componentSpecialFibreMap k' j hb
  have : IsClosedImmersion (hc.specialFixedLocus k').ι.left :=
    inferInstanceAs
      (IsClosedImmersion (fixedLocusOfDiag.ι (hc.specialLeg₁ k') (hc.specialLeg₂ k')).left)
  have : IsClosedImmersion
      ((hc.componentSpecialLift k' j hb).left ≫ (hc.specialFixedLocus k').ι.left) := by
    rwa [← Over.comp_left, componentSpecialLift_ι]
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (hc.specialFixedLocus k').ι.left

/-- The factorization `B'' ⟶ F'` is surjective: `F'` has at most one point
(`subsingleton_specialFixedLocus`) and `B''` contains the vertex of the tangent cone at `b`. -/
lemma surjective_componentSpecialLift : Surjective (hc.componentSpecialLift k' j hb).left := by
  have := hc.subsingleton_specialFixedLocus k'
  obtain ⟨p⟩ : Nonempty (point k').left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k')⟩
  exact ⟨fun _ ↦ ⟨(deformationVertex b k').left p, Subsingleton.elim _ _⟩⟩

/-- If `B ⊂ F ⊂ C` is a closed immersion, the factorization `B'' ⟶ F'` is a universal
homeomorphism, being a surjective closed immersion. -/
lemma isUniversalHomeomorphism_componentSpecialLift [IsClosedImmersion (j ≫ F.ι).left] :
    IsUniversalHomeomorphism (hc.componentSpecialLift k' j hb).left :=
  have := hc.isClosedImmersion_componentSpecialLift k' j hb
  have := hc.surjective_componentSpecialLift k' j hb
  {}

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
