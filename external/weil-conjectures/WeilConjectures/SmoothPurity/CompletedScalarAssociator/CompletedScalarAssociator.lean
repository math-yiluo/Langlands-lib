/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.CompletedScalarAssociator.PrescribedScalarAssociator
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.CompletedScalarAssociator.CompletedScalarPresentation

/-! # Normalized associators for the recorded completed coefficient extensions

Source: Stacks Tags 06YY and 07A4; blueprint Proof (3).
(blueprint: lem-pur-completed-scalar-associator-exists).

The comparison uses the actual ordinary functors, derived functors and universal
counits already recorded for completed coefficient sheaves. No new scalar-extension
model or completion construction is introduced.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedScalarAssociator

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)
  (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

section AssociatorProof

open SheafOfModules.SuccessiveDerivedQuotient

attribute [local semireducible] completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  completedOrdinaryScalarComplex

private theorem completedCoefficientMap_comp :
    completedCoefficientMap l E F ι X ≫ completedCoefficientMap l F G j X =
      completedCoefficientMap l E G (j.comp ι) X := by
  apply (completedCoefficientMap_existsUnique l E G (j.comp ι) X).unique
  · intro n
    rw [Category.assoc, completedCoefficientMap_projection]
    rw [← Category.assoc, completedCoefficientMap_projection, Category.assoc]
    congr 1
    unfold integralScalarQuotientSheafMap
    erw [← Functor.map_comp]
    congr 1
    ext x
    obtain ⟨x⟩ := x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  · simpa only [completedCoefficientMap] using
      (completedCoefficientMap_existsUnique l E G (j.comp ι) X).exists.choose_spec

private theorem completedScalarComposition :
    letI := scalarSiteDerived.{t, u} X
    letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
    letI := integralCoefficientAbLocallyBijective.{t, u} X
    letI := integralCoefficientAbSheafify.{t, u} X
    Nonempty (ScalarComposition (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (canonicalPresentation l E X F ι)
      (canonicalPresentation l F X G j) (canonicalPresentation l E X G (j.comp ι))) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
  let hD := scalarSiteDerived.{t, u} X
  let p : ∀ {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X)
      CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
      Presentation (J := AlgebraicGeometry.Scheme.ProEt.topology X) a :=
    fun {R S} a ↦ scalarPresentation (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := R) (S := S) a
  have h := scalarCompositionData p
    (completedCoefficientMap l E F ι X) (completedCoefficientMap l F G j X)
    (completedCoefficientMap l E G (j.comp ι) X)
    (completedCoefficientMap_comp l E X F ι G j)
  simpa only [p, scalarPresentation, canonicalPresentation, chosenPresentation,
    completedOrdinaryScalarExtension, completedDerivedScalarExtension] using h

private theorem quotient_Qh_obj {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (P : CochainComplex A ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) =
      DerivedCategory.Q.obj P := rfl

attribute [local irreducible] completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection

private theorem good_isKFlat
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P.obj := P.property.1

attribute [local irreducible] integralOperationsGoodComplex

omit [FiniteDimensional ℚ_[l] F] in
private theorem counit_hom_ext
    {H : DerivedCategory (integralTowerModules l E X) ⥤
      DerivedCategory (integralTowerModules l G X)}
    (f g : H ⟶ completedDerivedScalarExtension l E G (j.comp ι) X)
    (h : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      f.app (DerivedCategory.Q.obj P.obj) ≫ completedScalarCounit l E G (j.comp ι) X P.obj =
        g.app (DerivedCategory.Q.obj P.obj) ≫ completedScalarCounit l E G (j.comp ι) X P.obj) :
    f = g := by
  let Q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  have : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  apply Localization.natTrans_ext Q W
  intro P
  have hi : IsIso (completedScalarCounit l E G (j.comp ι) X P.obj) := by
    rw [← completedScalarCochainModel_counit]
    have h := (completedScalarCochainModel l E G (j.comp ι) X).computes
      P.obj (good_isKFlat l E X P)
    dsimp only [completedDerivedScalarExtension, completedOrdinaryScalarComplex,
      completedOrdinaryScalarExtension, completedScalarChangeData] at h ⊢
    convert h using 0
    delta completedDerivedScalarExtension completedOrdinaryScalarComplex
      completedOrdinaryScalarExtension completedScalarChangeData
    rfl
  exact (cancel_mono (completedScalarCounit l E G (j.comp ι) X P.obj)).mp (h P)

/-- The recorded scalar extensions have normalized ordinary and derived associators.
Source: Stacks Tags 06YY and 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-scalar-associator-exists).
Proof: completed coefficient maps compose because their finite quotient projections do.
Bundle the recorded extension functors and universal counits as presentations. Their
extension-restriction adjunctions compose, and uniqueness of left adjoints gives the
ordinary and derived associators. The ordinary units are tensors with one, so the
ordinary comparison sends t tensor (s tensor x) to t*j(s) tensor x. The derived hom
comparison identifies its representative with the composite of the two universal
counits and the localized ordinary comparison. Finally, applying the two ordinary
adjunction hom-equivalences shows that the tensor formula determines the ordinary
comparison uniquely. On good complexes the direct counit is invertible, so equality
of the derived components after that counit implies equality of components. Faithful
precomposition by the good-complex localization then determines the derived map.
This includes repeated fields and all unbounded complexes. -/
private theorem exists_normalized :
    ∃ (o : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
          completedOrdinaryScalarExtension l E G (j.comp ι) X)
      (d : completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F G j X ≅
          completedDerivedScalarExtension l E G (j.comp ι) X),
    (∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
        (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
        (completedScalarTensorSection l F G j X _ U t
          (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E G (j.comp ι) X M U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x) ∧
    (∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      @Eq ((completedDerivedScalarExtension l F G j X).obj
          ((completedDerivedScalarExtension l E F ι X).obj (DerivedCategory.Q.obj P)) ⟶
        DerivedCategory.Q.obj ((completedOrdinaryScalarComplex l E G (j.comp ι) X).obj P))
      ((completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P))
      (d.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E G (j.comp ι) X P)) ∧
    (∀ (o' : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
          completedOrdinaryScalarExtension l E G (j.comp ι) X),
      (∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
          (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
          (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
        (o'.hom.app M).val.app U
          (completedScalarTensorSection l F G j X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
          completedScalarTensorSection l E G (j.comp ι) X M U
            (t * (completedCoefficientMap l F G j X).hom.app U s) x) → o' = o) ∧
    (∀ (d' : completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F G j X ≅
          completedDerivedScalarExtension l E G (j.comp ι) X),
      (∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
        d'.hom.app (DerivedCategory.Q.obj P.obj) ≫
            completedScalarCounit l E G (j.comp ι) X P.obj =
          d.hom.app (DerivedCategory.Q.obj P.obj) ≫
            completedScalarCounit l E G (j.comp ι) X P.obj) → d' = d) := by
  obtain ⟨v⟩ := completedScalarComposition l E X F ι G j
  let o : completedOrdinaryScalarExtension l E F ι X ⋙
      completedOrdinaryScalarExtension l F G j X ≅
        completedOrdinaryScalarExtension l E G (j.comp ι) X := v.ordinary
  let d : completedDerivedScalarExtension l E F ι X ⋙
      completedDerivedScalarExtension l F G j X ≅
        completedDerivedScalarExtension l E G (j.comp ι) X := v.derived
  have ho := v.tensor
  simp only [canonicalPresentation_ordinary, canonicalPresentation_sectionTensor] at ho
  have hd := v.representative
  simp only [canonicalPresentation_ordinary, canonicalPresentation_derived,
    canonicalPresentation_counit] at hd
  have hu := v.unique
  simp only [canonicalPresentation_ordinary, canonicalPresentation_sectionTensor] at hu
  refine ⟨o, d, ho, ?_, hu, ?_⟩
  · intro P
    have h := hd P
    dsimp only [completedOrdinaryScalarComplex, Functor.comp_obj,
      Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as,
      quotient_Qh_obj, scalarSiteDerived, integralTowerHasDerivedCategory, o, d] at h ⊢
    convert h using 0
    rfl
  · intro d' h
    apply Iso.ext
    exact counit_hom_ext l E X F ι G j d'.hom d.hom h

/-- The recorded scalar associator is uniquely fixed by tensor sections and good counits.
Source: Stacks Tags 06YY and 07A6; blueprint Proof (3)
(blueprint: lem-pur-completed-scalar-associator-exists).
Proof: use the normalized comparison for the actual recorded presentations. Restrict
its all-complex representative formula to good complexes. The tensor formula fixes
the ordinary isomorphism, and equality after the direct counit on good complexes
fixes the derived isomorphism by faithful localization and K-flat counit cancellation. -/
theorem exists_unique :
    let lift := fun (o : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
          completedOrdinaryScalarExtension l E G (j.comp ι) X) ↦
      (show completedOrdinaryScalarComplex l E F ι X ⋙
          completedOrdinaryScalarComplex l F G j X ≅
            completedOrdinaryScalarComplex l E G (j.comp ι) X from by
        unfold completedOrdinaryScalarComplex
        exact Functor.mapHomologicalComplexCompIso o (ComplexShape.up ℤ))
    ∃! a : (completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
          completedOrdinaryScalarExtension l E G (j.comp ι) X) ×
      (completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F G j X ≅
          completedDerivedScalarExtension l E G (j.comp ι) X),
      (∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
          (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
          (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
        (a.1.hom.app M).val.app U
          (completedScalarTensorSection l F G j X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
          completedScalarTensorSection l E G (j.comp ι) X M U
            (t * (completedCoefficientMap l F G j X).hom.app U s) x) ∧
      (∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
        (completedDerivedScalarExtension l F G j X).map
            (completedScalarCounit l E F ι X P.obj) ≫
          completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
          DerivedCategory.Q.map ((lift a.1).hom.app P.obj) =
        a.2.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E G (j.comp ι) X P.obj) := by
  obtain ⟨o, d, ho, hd, hu, hv⟩ := exists_normalized l E X F ι G j
  refine ⟨(o, d), ⟨ho, ?_⟩, ?_⟩
  · intro P
    have h := hd P.obj
    convert h using 0
    delta completedOrdinaryScalarComplex
    rfl
  · intro a ha
    have hs : a.1 = o := hu a.1 ha.1
    apply Prod.ext hs
    apply hv a.2
    intro P
    have h := ha.2 P
    rw [hs] at h
    refine h.symm.trans ?_
    have h' := hd P.obj
    convert h' using 0
    delta completedOrdinaryScalarComplex
    rfl

end AssociatorProof
end CompletedScalarAssociator
end WeilConjectures
