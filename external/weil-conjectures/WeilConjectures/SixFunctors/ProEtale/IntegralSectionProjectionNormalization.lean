/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction
public import WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentation
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares

/-! # Quotient projections of the normalized integral section comparison

Source: blueprint integral-criterion-reductions, final coefficient interpretation.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralPresentation

attribute [local irreducible] upperStarFromPoint

private theorem topology_transport (B : Type u) [Ring B]
    (t₁ t₂ : TopologicalSpace B) (ht : t₁ = t₂)
    (h₁ : @IsTopologicalRing B t₁ _) (h₂ : @IsTopologicalRing B t₂ _) :
    ∃ h : @Profinite.continuousCoefficientRingSheaf.{u} B t₁ _ h₁ =
        @Profinite.continuousMapRingSheafOfUniverse.{u, u} B t₂ _ h₂,
      (continuousRingTopologyIso B t₁ t₂ ht h₁ h₂).hom = eqToHom h := by
  subst t₂
  refine ⟨rfl, ?_⟩
  ext S f
  rfl

private theorem source_transport (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (h : (upperStarFromPoint X).obj (DerivedNakayama.integerRing l E) =
      (upperStarFromPoint X).obj (sfbCondensedIntegers l E).X) :
    eqToHom h = (upperStarFromPoint X).map (integerPointIso l E).hom := by
  obtain ⟨ht, hh⟩ := topology_transport (Padic.coefficientExtensionIntegers l E) _ _
    (congrArg (fun t : TopologicalSpace E ↦ TopologicalSpace.induced
      (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t)
        (DerivedNakayama.coefficientTopology l E).symm) _ _
  let V := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hpoint : (integerPointIso l E).hom = eqToHom (congrArg V.obj ht) := by
    change V.map (integerPointRingIso l E).hom = _
    rw [show (integerPointRingIso l E).hom = eqToHom ht from hh, eqToHom_map]
  rw [hpoint, eqToHom_map]

/-- The fixed normalized integral ring comparison commutes with every finite quotient.
Source: blueprint integral-criterion-reductions, final coefficient interpretation;
Stacks 00YV and 03EK
(auxiliary; not a blueprint node).

Proof: forget to abelian sheaves. Under the point inverse-image adjunction, the
mate of the left side is postcomposition of continuous maps with the quotient.
The mate of the right side has the same value on every profinite test: the
SfbIntegralComparison equation gives its finite-label representation, and the
finite encoding normalization identifies constants with their continuous sections.
Every continuous map into a finite discrete quotient is locally constant on its
clopen fibres. On each fibre both maps therefore give that constant quotient
value. Sheaf separation gives equality of the mates, the adjunction gives equality
of abelian sheaf maps, and faithfulness of forgetting ring structure gives the
stated commutative-ring equality. Empty fibres need no sections. -/
theorem integral_section_projection_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (A : Encoding l E X)
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    (he : SfbIntegralComparison l E X e)
    (hsrc : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)) =
        (coefficientRing X (sfbCondensedIntegers l E)).X)
    (htgt : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X) =
        sfbCompletedIntegersAb l E X)
    (hc : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map A.ringIso.hom =
          eqToHom hsrc ≫ e.hom ≫ eqToHom htgt.symm) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (n : ℕ) (f : FiniteEncoding l E X n),
    InternalAbelianSheafModule.sectionScalarMap (Scheme.ProEt.topology X)
        (AdicCompletion.quotient l E X n) =
      A.ringIso.hom ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n ≫
        f.ringIso.hom := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro n f
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let := DerivedNakayama.quotientDiscrete l E (n + 1)
  obtain ⟨_, _, a, c, j, hq, _, hn⟩ := he
  have hb := integral_projection_back l E X n a c j hq e (fun S g ↦ hn S g n)
  let F := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})
  apply (cancel_mono f.ringIso.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply F.map_injective
  rw [F.map_comp, F.map_comp, hc, finiteBack_ringIso X _ a f]
  have hs : eqToHom hsrc = (upperStarFromPoint X).map (integerPointIso l E).hom :=
    source_transport l E X hsrc
  have ht : eqToHom htgt.symm = 𝟙 (sfbCompletedIntegersAb l E X) := eqToHom_refl _ _
  rw [hs, ht, Category.comp_id]
  have hh := congrArg (fun k ↦ (upperStarFromPoint X).map
    (integerPointIso l E).hom ≫ k) hb
  have hcancel : (upperStarFromPoint X).map (integerPointIso l E).hom ≫
      (upperStarFromPoint X).map
        ((integerPointIso l E).inv ≫ DerivedNakayama.reductionRing l E (n + 1)) =
      (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1)) := by
    rw [← Functor.map_comp, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hcancel] at hh
  change (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1)) ≫
    finiteBack X (Padic.coefficientExtensionRing l E (n + 1)) a = _
  exact hh

end AlgebraicGeometry.ProEtale.IntegralPresentation
