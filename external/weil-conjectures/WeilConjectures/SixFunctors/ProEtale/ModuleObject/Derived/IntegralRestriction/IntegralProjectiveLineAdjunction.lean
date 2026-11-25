/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionFunctors

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelContractions
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-! # Integral diagonal-kernel adjunction for a projective line

Source: current blueprint, sk-thm-int-restriction-line.proof.md, paragraph (1).
(blueprint: lem-sfb-integral-projective-line-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

@[instance_reducible]
private def projectiveResidueUnits (k : Type u) [Field k]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    ∀ x : X, Invertible (ℓ : X.residueField x) := by
  have hl : (ℓ : k) ≠ 0 := by
    intro hz
    exact (Fact.out : ringChar k ≠ ℓ)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) hz)
  intro x
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation x).hom
  exact (show IsUnit (ℓ : X.residueField x) by
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hl).map φ).invertible

open CategoryTheory.MonoidalCategory

private theorem diagonalIntegral_map {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (F : C ⥤ D) (M U S T : C) (e : U ≅ 𝟙_ C)
    (s : U ⟶ S) (d : S ⟶ T) (t : T ⟶ U)
    (h : s ≫ d ≫ t = 𝟙 U) :
    F.map ((ρ_ M).inv ≫ (M ◁ (e.inv ≫ s ≫ d ≫ t ≫ e.hom)) ≫
      (ρ_ M).hom) = 𝟙 (F.obj M) := by
  have hs := congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) h
  simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id] at hs
  simp only [hs, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]
  exact F.map_id M
private theorem diagonalIntegral {C : Type*} [Category C] [MonoidalCategory C]
    (M U S T : C) (e : U ≅ 𝟙_ C)
    (s : U ⟶ S) (d : S ⟶ T) (t : T ⟶ U)
    (h : s ≫ d ≫ t = 𝟙 U) :
    (ρ_ M).inv ≫ (M ◁ (e.inv ≫ s ≫ d ≫ t ≫ e.hom)) ≫
      (ρ_ M).hom = 𝟙 M := by
  have hs := congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) h
  simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id] at hs
  simp only [hs, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

/-- The projective-line diagonal and its normalized integral trace give the
adjunction between the two specified restricted functors.

Source: sk-thm-int-restriction-line.proof.md, paragraph (1).
(blueprint: lem-sfb-integral-projective-line-adjunction).

Proof: write P = P1_Y and W = P times_Y P. Properness of both projections
and exactness of closed direct image identify the diagonal support with
Delta_* on the unbounded ambient categories. The integral diagonal tower and
coefficient extension give delta and the three traces, with both projection
integrals equal to identity. Tensor the inverse diagonal projection comparison
with delta and push along p2. Proper exchange and the p2 projection comparison
identify the result with a natural map M -> q*Rq*M(1)[2]. The counit is inverse
q-projection followed by identity tensor the q-trace. Trace base change along
p1 rewrites the first triangle as the pushforward of identity tensor the first
diagonal integral; section normalization cancels the diagonal projection map.
It is identity. The second trace-base-change rearrangement and the p2 section
normalization give identity tensor the second integral, hence identity again.
The shifts are even, so no Koszul sign remains. The specified preservation
witnesses restrict these natural transformations to the full localizing
subcategories. Their naturality and the two triangle identities give an
adjunction by the unit-counit construction. -/
theorem integralProjectiveLine_adjunction
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K)) :
    Nonempty (restrictedPush ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) hr ⊣
      restrictedPull ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1 hq) := by
  let : (ProjectiveLine Y).Over (Spec (.of k)) := inferInstance
  let : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨pullback.fst _ _ ≫ (ProjectiveLine Y ↘ Spec (.of k))⟩
  let : ∀ x : ProjectiveLine Y,
      Invertible (ℓ : (ProjectiveLine Y).residueField x) :=
    projectiveResidueUnits ℓ k _
  let : ∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x) :=
    projectiveResidueUnits ℓ k _
  obtain ⟨family, href⟩ := integralNormalizedFamily_exists ℓ k Y
  obtain ⟨a, hnorm, _⟩ := integralUnitCounit_existsUnique ℓ E k Y hq hr family
  obtain ⟨h₁, h₂⟩ := integralKernel_contractions ℓ E k Y hq hr family href a hnorm
  refine ⟨Adjunction.mkOfUnitCounit
    { unit := a.1
      counit := a.2
      left_triangle := ?_
      right_triangle := ?_ }⟩
  · apply NatTrans.ext
    funext M
    apply ObjectProperty.hom_ext
    have hs := diagonalIntegral_map
      (moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y ↘ Y)) M.obj _ _ _
      (RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y)) _ _ _ (family.integral E).integration₁
    have h := (h₁ M).trans hs
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp, NatTrans.id_app',
      ObjectProperty.FullSubcategory.id_hom, Functor.comp_obj, Functor.id_obj,
      restrictedPush, ObjectProperty.lift, ObjectProperty.ι_obj, IntegralCompactSupport.push,
      moduleDerivedPushforward, moduleObjectDerivedPushforward] using h
  · apply NatTrans.ext
    funext K
    apply ObjectProperty.hom_ext
    have hs := diagonalIntegral
      (((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj) _ _ _
      (RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y)) _ _ _ (family.integral E).integration₂
    have h := (h₂ K).trans hs
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Category.id_comp, NatTrans.id_app',
      ObjectProperty.FullSubcategory.id_hom, Functor.comp_obj, Functor.id_obj] using h

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
