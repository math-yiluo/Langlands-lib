/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictRepresentatives

/-! Normalization after transported coefficient extension.

Source: Stacks 07A4, 06YY and 0941; the scalar-extension step of
`lem-trf-transported-reduction-systems-normalized`.
(blueprint: stage3-trf-transported-scalar-normalized)

The proof compares the specified scalar model with the normalized
semilinear coefficient-extension model on the entire quotient system. -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe c v r w₁ w₂
open CategoryTheory

private noncomputable def scalarModelIso
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} {φ ψ : R ⟶ S}
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w₂}
      (SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (h : φ = ψ) (A : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (B : SheafOfModules.DerivedChangeOfRingsCochainModel ψ) : A.T ≅ B.T := by
  subst ψ
  let a : A.E ≅ B.E := NatIso.ofComponents
    (fun M ↦ eqToIso ((A.obj_eq M).trans (B.obj_eq M).symm)) (by
      intro M N f
      simp only [eqToIso.hom, A.map_eq, B.map_eq, Category.assoc,
        eqToHom_trans_assoc, eqToHom_trans])
  letI := A.universal
  letI := B.universal
  exact Functor.leftDerivedNatIso A.T B.T A.ε B.ε
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

private theorem coefficientSequenceNormalized_of_iso (W : Scheme.{t})
    {X Y : coefficientSequenceDerived l E W} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence l E W X) :
    IsNormalizedCoefficientSequence l E W Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
  let G := normalizedDVRRes l E W h
  have hn := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y =
    (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

/-- The transported scalar extension of every normalized reduction is normalized.
Source: Stacks 07A4, 06YY and 0941; scalar-extension step of the parent proof.
(blueprint: stage3-trf-transported-scalar-normalized)
Proof: choose the semilinear coefficient-extension reduction model for the
actual quotient-ring map.  Its normalized field supplies the transition
bijections for the scalar extension of the source reduction.  The universal
counit-compatible comparison with `integralComparisonSequenceScalarModel` is
an isomorphism commuting with all evaluations and transitions.  Conjugating
the bijections through this comparison gives normalization of the specified
whole-system scalar functor, including ramified and identity extensions. -/
theorem transportedReductionSystems_scalar_normalized
    {Y : Scheme.{t}}
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K)) := by
  classical
  obtain ⟨D⟩ := SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
    (Scheme.ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y)
    (coefficientSequenceCommRingTransition l E Y)
  let A : CoefficientExtensionSystems l E L ι Y :=
    D.coefficientExtension (integralCoefficientCommRingSheaf l L Y)
      (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y)
  have hφ : SemilinearSections.systemMap.{t + 1, t, max u (t + 1)}
      (Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y) (coefficientSequenceCommRingTransition l E Y)
      (integralCoefficientCommRingSheaf l L Y) (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y) =
        integralComparisonSequenceScalarMap l E L ι Y := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (SemilinearSections.systemMap_existsUnique.{t + 1, t, max u (t + 1)}
      (Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y) (coefficientSequenceCommRingTransition l E Y)
      (integralCoefficientCommRingSheaf l L Y) (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y)).exists.choose_spec
        U.unop.1 (Opposite.op U.unop.2)
  let a : A.scalar.T ≅ integralComparisonDerivedSequenceScalar l E L ι Y :=
    scalarModelIso hφ A.scalar.model (integralComparisonSequenceScalarModel l E L ι Y)
  obtain ⟨association⟩ := coefficientExtensionFiniteAssociation_exists l E L ι Y A
  obtain ⟨_, _, _, _, _, hn⟩ := coefficientExtensionStrictRepresentative_exists
    l E L ι Y A SY association.association association.association_section
  intro K
  exact coefficientSequenceNormalized_of_iso l L Y (a.app (SY.reduction.obj K))
    (hn K)

end WeilConjectures
