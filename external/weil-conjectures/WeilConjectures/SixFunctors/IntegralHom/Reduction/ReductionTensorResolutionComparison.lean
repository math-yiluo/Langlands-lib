/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.Algebra.Homology.SixFunctors.RestrictionExtensionTensorComparisonIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # Scalar reduction computed by a coefficient resolution

Source: Stacks Tags 06YY and 07A4; the coefficient resolution in paragraph 1 of
`lem-coef-integral-hom-reduction.proof.md`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.IntegralHom

open MonoidalCategory
open scoped ZeroObject

section Resolutions

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The closed sheaf tensor is additive in each variable. -/
private theorem tensorPreadditive : MonoidalPreadditive (Modules.{t, u} Y R) := by
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  have (M : Modules.{t, u} Y R) : (tensorLeft M).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have (M : Modules.{t, u} Y R) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

attribute [local instance] tensorPreadditive

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Functorial K-flat replacements from the existing reduced flat resolution.
Source: Stacks Tag 06YS. The flat-resolution colimit theorem gives categorical
K-flatness. Apply it to zero maps into acyclic complexes to obtain the recorded
acyclic-tensor predicate. -/
private theorem functorialResolution :
    ∃ (F : CochainComplex (Modules.{t, u} Y R) ℤ ⥤
        CochainComplex (Modules.{t, u} Y R) ℤ) (π : F ⟶ 𝟭 _),
      (∀ P, QuasiIso (π.app P)) ∧ (∀ P, flat.{t, u} Y R (F.obj P)) := by
  let A := Modules.{t, u} Y R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have : HasExactColimitsOfShape ℤ A := by
    have := AB5OfSize_of_univLE.{0, 0, max u (t + 1), max u (t + 1)}
      AddCommGrpCat.{max u (t + 1)}
    exact HasExactColimitsOfShape.domain_of_functor ℤ
      (SheafOfModules.toSheaf.{max u (t + 1)}
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat RingCat)).obj R))
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Z ↦ β_ X Z) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  refine ⟨Λ.resolutionFunctor, Λ.resolutionNatTrans, fun P ↦ inferInstance, ?_⟩
  intro P Z hZ
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P
  let T := tensorRight (Λ.resolutionFunctor.obj P)
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have ht : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- K-flat tensor preserves quasi-isomorphisms in both orders, by symmetry. -/
private theorem tensorQuasiIso
    (P : CochainComplex (Modules.{t, u} Y R) ℤ) (hP : flat.{t, u} Y R P)
    {X Z : CochainComplex (Modules.{t, u} Y R) ℤ} (f : X ⟶ Z) (hf : QuasiIso f) :
    QuasiIso (((totalTensor.{t, u} Y R).obj P).map f) ∧
      QuasiIso (((totalTensor.{t, u} Y R).flip.obj P).map f) := by
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  have hr : QuasiIso (((totalTensor.{t, u} Y R).flip.obj P).map f) :=
    kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP f hf
  refine ⟨?_, hr⟩
  let e (Z : CochainComplex (Modules.{t, u} Y R) ℤ) :
      ((totalTensor.{t, u} Y R).obj P).obj Z ≅
        ((totalTensor.{t, u} Y R).flip.obj P).obj Z := β_ P Z
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (e X) (e Z) ?_)).2 hr
  exact (BraidedCategory.braiding_naturality_right P f).symm

end Resolutions

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Tensor with a K-flat coefficient resolution computes restricted derived reduction,
without an internal Hom or any tensor presentation as input.

Source: Stacks 06YY, 07A4, 07A6 and 08J7; blueprint
`lem-coef-integral-hom-reduction.proof.md`, paragraph 1.
(blueprint: lem-sf-reduction-tensor-resolution-comparison).

Proof: on a K-flat complex A, tensor the supplied augmentation with A. Its
localization is invertible by K-flatness of A. The ordinary balanced tensor
comparison identifies tensor with the restricted quotient unit with restriction
of scalar extension of A. The left-derived counit and the exact-restriction
factorization identify this with restricted derived reduction of Qloc(A).
For arbitrary C choose a K-flat resolution A -> C. Tensoring its augmentation
with the supplied K-flat Q is a quasi-isomorphism, so the preceding isomorphism
extends to C. Use the existing reduced functorial flat resolution to make this
choice natural in C. Whisker the counit, ordinary comparison, tensor augmentation,
and resolution augmentation, then compose their localized natural isomorphisms.
No boundedness or nonzero hypothesis on Q, C, the ring, or the site is used. -/
theorem reduction_tensor_resolution_comparison
    (n : ℕ) (Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hQ : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q)
    (epsilon : Q ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))))
    (hepsilon : QuasiIso epsilon) :
    Nonempty (DerivedCategory.Q ⋙ integralDerivedReduction l E Y D hl n ⋙
        scalarReductionDerivedRestriction l E Y n ≅
      (totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).flip.obj Q ⋙
        DerivedCategory.Q) := by
  classical
  let R := completedIntegralCommRingSheaf l E Y D hl
  let A := completedIntegralModuleSheaves l E Y D hl
  let B := scalarReductionTarget l E Y n
  let U := scalarReductionRestriction l E Y n
  let E₀ := scalarReductionExtension l E Y n
  let L := integralDerivedReduction l E Y D hl n
  let V := scalarReductionDerivedRestriction l E Y n
  let T := totalTensor.{t, u} Y R
  let S := U.obj (SheafOfModules.unit (integralCoefficientSheaf l E Y n))
  let S₀ := (CochainComplex.singleFunctor A 0).obj S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have := tensorPreadditive Y R
  have : E₀.Additive := scalarReductionExtensionAdditive l E Y n
  have : PreservesFiniteLimits U := scalarReductionRestrictionLimits l E Y n
  have : PreservesFiniteColimits U := scalarReductionRestrictionColimits l E Y n
  let E' := E₀.mapHomologicalComplex (.up ℤ)
  let U' := U.mapHomologicalComplex (.up ℤ)
  obtain ⟨F, π, hπ, hF⟩ := functorialResolution Y R
  let H := DerivedCategory.Q ⋙ L ⋙ V
  let c : DerivedCategory.Q ⋙ L ⟶ E' ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv L ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
        (scalarReductionCounit l E Y n) ≫
      Functor.whiskerRight (E₀.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft E' (DerivedCategory.quotientCompQhIso B).hom
  have hc (P : CochainComplex A ℤ) (hp : flat.{t, u} Y R P) : IsIso (c.app P) := by
    have : IsIso ((scalarReductionCounit l E Y n).app
        ((HomotopyCategory.quotient A (.up ℤ)).obj P)) :=
      (scalarReductionDerivedExistence l E Y n).choose_spec.choose_spec.2.2 P hp
    dsimp only [c, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have hcF : ∀ P, IsIso ((Functor.whiskerLeft F c).app P) := fun P ↦ hc _ (hF P)
  have : IsIso (Functor.whiskerLeft F c) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hcF
  let cF := asIso (Functor.whiskerLeft F c)
  obtain ⟨o⟩ :=
    SheafOfModules.restrictionExtensionTensorComparisonIndependentCoefficients
    (completedIntegralCommRingProjectionUnrestricted l E Y n) E₀
    (scalarReductionExistence l E Y n).choose_spec.choose
    (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose
  let singleIso : U'.obj
      ((CochainComplex.singleFunctor B 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n))) ≅ S₀ :=
    (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app _
  let e : Q ⟶ S₀ := epsilon ≫ singleIso.hom
  have he : QuasiIso e := by
    have : QuasiIso epsilon := hepsilon
    dsimp only [e]
    infer_instance
  let ordinary : T.flip.obj S₀ ≅ E' ⋙ U' :=
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso (ordinaryTensor.{t, u} Y R) S ≪≫
      (NatIso.mapHomologicalComplex o (.up ℤ)).symm
  let a : T.flip.obj Q ⟶ T.flip.obj S₀ := T.flip.map e
  have ha (P : CochainComplex A ℤ) (hp : flat.{t, u} Y R P) :
      QuasiIso (a.app P) :=
    (tensorQuasiIso Y R P hp e he).1
  have haF : ∀ P,
      IsIso ((Functor.whiskerRight (Functor.whiskerLeft F a) DerivedCategory.Q).app P) := by
    intro P
    have : QuasiIso (a.app (F.obj P)) := ha _ (hF P)
    change IsIso (DerivedCategory.Q.map (a.app (F.obj P)))
    infer_instance
  have : IsIso (Functor.whiskerRight (Functor.whiskerLeft F a) DerivedCategory.Q) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ haF
  let aF := asIso (Functor.whiskerRight (Functor.whiskerLeft F a) DerivedCategory.Q)
  have hπH : ∀ P, IsIso ((Functor.whiskerRight π H).app P) := by
    intro P
    have : QuasiIso (π.app P) := hπ P
    change IsIso (V.map (L.map (DerivedCategory.Q.map (π.app P))))
    infer_instance
  have : IsIso (Functor.whiskerRight π H) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hπH
  have hπT : ∀ P,
      IsIso ((Functor.whiskerRight π (T.flip.obj Q ⋙ DerivedCategory.Q)).app P) := by
    intro P
    have : QuasiIso ((T.flip.obj Q).map (π.app P)) :=
      (tensorQuasiIso Y R Q hQ (π.app P) (hπ P)).2
    change IsIso (DerivedCategory.Q.map ((T.flip.obj Q).map (π.app P)))
    infer_instance
  have : IsIso (Functor.whiskerRight π (T.flip.obj Q ⋙ DerivedCategory.Q)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hπT
  refine ⟨(Functor.leftUnitor H).symm ≪≫
    (asIso (Functor.whiskerRight π H)).symm ≪≫
    Functor.isoWhiskerRight cF V ≪≫
    Functor.isoWhiskerLeft (F ⋙ E') U.mapDerivedCategoryFactors ≪≫
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft F ordinary) DerivedCategory.Q).symm ≪≫
    aF.symm ≪≫ asIso (Functor.whiskerRight π (T.flip.obj Q ⋙ DerivedCategory.Q)) ≪≫
    Functor.leftUnitor _⟩

end WeilConjectures.IntegralHom
