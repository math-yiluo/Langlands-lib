/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.Normalized.NormalizedScalarChainComparison
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionScalarPair
import WeilConjectures.Algebra.Homology.Scalar.ScalarHomExtensionKFlat
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement

/-! # Sectionwise normalization data for integral reduction

This isolates the representative normalization field required by
`ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules CategoryTheory.MonoidalCategory CategoryTheory.Functor
open CategoryTheory.ScalarHomTensor

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory
  scalarPairComplexComparison WeilConjectures.CoefficientTensorModels.iso

namespace WeilConjectures.IntegralHom

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  integralReductionExistence integralReductionDerivedExistence
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted constantSheaf

universe c₁ v₁ r w₁ e ve

/-- Restricting bifunctors to K-flat representative pairs is fully faithful. -/
private theorem flatPairsWhiskering
    {C : Type c₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {R : Sheaf J CommRingCat.{r}} [HasDerivedCategory.{w₁} (scalarModules J R)]
    (E : Type e) [Category.{ve} E] :
    let P : ObjectProperty (CochainComplex (scalarModules J R) ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (scalarModules J R) × DerivedCategory (scalarModules J R)) E).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let A := scalarModules J R
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  have hff := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) E
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  obtain ⟨ff⟩ := hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  exact ⟨ff'⟩

/-- Cancelling the two isomorphisms completes a representative square. -/
private theorem inverseSquare {C : Type c₁} [Category.{v₁} C] {X Y Z W V T : C}
    (f : X ⟶ Y) (g : Y ⟶ V) (h : V ⟶ T) (e : X ⟶ Z) (b : Z ≅ W) (r : W ≅ T)
    (he : f ≫ g ≫ h = e ≫ b.hom ≫ r.hom) : f ≫ g ≫ h ≫ r.inv ≫ b.inv = e := by
  calc
    _ = (f ≫ g ≫ h) ≫ r.inv ≫ b.inv := by simp only [Category.assoc]
    _ = _ := by rw [he]; simp only [Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
  [EssentiallySmall.{max u (t + 1)} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

omit [EssentiallySmall.{max u (t + 1)} Y.ProEt] in
/-- The two total tensor section interfaces use the same summand inclusion. -/
private theorem totalPair_eq_generator
    (T : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (P Q : CochainComplex (Modules.{t, u} Y T) ℤ) (i j : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    totalPair.{t, u} Y T P Q i j U x y =
      coefficientTensorGenerator.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) T P Q i j (i + j) rfl U x y := by
  rfl

omit [EssentiallySmall.{max u (t + 1)} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
/-- The actual scalar pair retains the fixed integral reduction counit. -/
private theorem actual_pairCounit (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    reductionCounit l E Y D hl n P =
      scalarPairComplexComparison
        (coefficientActualScalarDerivedPair l E Y n).extension
        (coefficientActualScalarDerivedPair l E Y n).extension_additive
        (coefficientActualScalarDerivedPair l E Y n).derived
        (coefficientActualScalarDerivedPair l E Y n).counit P := by
  unfold reductionCounit scalarPairComplexComparison
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

omit [EssentiallySmall.{max u (t + 1)} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
/-- The actual scalar pair retains the prescribed ordinary adjunction. -/
private theorem actual_ordinaryAdjunction (n : ℕ) :
    (coefficientActualScalarDerivedPair l E Y n).ordinaryAdjunction =
      (scalarReductionExtension_adjunction l E Y n).choose := rfl

-- STATEMENT-DISPUTED: repaired; an arbitrary mu need not satisfy the counit square.
-- Choose the comparison and its normalization together.
-- The concrete representative conversions require a larger elaboration budget.
/-- The sectionwise and counit-square normalization data exists for a fixed
finite target and source presentation.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: on K-flat representatives use the scalar-extension unit
`x ↦ 1 ⊗ x`. Balanced tensor associativity gives an invertible chain map and
its pure-tensor formula. The left-derived universal property transports this
map to the displayed counit square. Choose the derived comparison by descent
of this normalized chain comparison, rather than accepting an arbitrary comparison.
(blueprint: lem-sf-integral-hom-reduction-normalization-data).
-/
theorem reduction_normalization_data_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) :
    letI : HasDerivedCategory (Modules.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (Modules.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) := HasDerivedCategory.standard _
    ∃ mu : a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
      ((integralDerivedReduction l E Y D hl n).prod
        (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor,
    ∀ (P Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
      (hp : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hq : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q),
      ∃ (hp' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P))
        (hq' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q))
        (beta : ((totalTensor.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
        ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q)),
        IsIso beta ∧
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
          (beta.f (i + j)).val.app U
              (totalPair.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
                (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex
                  (.up ℤ)).obj P)
                (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex
                  (.up ℤ)).obj Q)
                i j U ((reductionUnit l E Y D hl n (P.X i)).val.app U x)
                  ((reductionUnit l E Y D hl n (Q.X j)).val.app U y)) =
            (reductionUnit l E Y D hl n
              ((((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q).X
                (i + j))).val.app U
              (totalPair.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P Q i j U x y)) ∧
        (integralDerivedReduction l E Y D hl n).map
            (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
          mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          target.tensor.map (Prod.mkHom (reductionCounit l E Y D hl n P)
            (reductionCounit l E Y D hl n Q)) ≫
          target.representative.inv.app (⟨_, hp'⟩, ⟨_, hq'⟩) ≫ DerivedCategory.Q.map beta =
        reductionCounit l E Y D hl n
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q) := by
  classical
  dsimp only
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let R := completedIntegralCommRingSheaf l E Y D hl
  let S := integralCoefficientCommRingSheaf l E Y n
  let c := completedIntegralCommRingProjectionUnrestricted l E Y n
  let s := integralReductionScalarPair l E Y D hl n
  let := s.extension_additive
  let A := scalarModules J R
  let B := scalarModules J S
  let : HasDerivedCategory A := HasDerivedCategory.standard _
  let : HasDerivedCategory B := HasDerivedCategory.standard _
  let F := (integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)
  let tR := coefficientTotalTensor.{u, t + 1, t} J R
  let tS := coefficientTotalTensor.{u, t + 1, t} J S
  obtain ⟨b, hg⟩ := normalizedScalarChainComparison.{t + 1, t, u, max (t + 2) (u + 1)} c s
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
  have hF : ∀ P, PR P → PS (F.obj P) :=
    fun P hp ↦ scalarExtension_preservesKFlat c s P hp
  let eps : DerivedCategory.Q ⋙ s.derived ⟶ F ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv s.derived ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) s.counit ≫
      Functor.whiskerRight (s.extension.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso B).hom
  have heps (P : CochainComplex A ℤ) : eps.app P =
      scalarPairComplexComparison s.extension s.extension_additive s.derived s.counit P := by
    change s.derived.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
      s.counit.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ (DerivedCategory.quotientCompQhIso B).hom.app
        (F.obj P) = _
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    unfold scalarPairComplexComparison
    rfl
  obtain ⟨ff'⟩ := flatPairsWhiskering (J := J) (R := R) (DerivedCategory B)
  obtain ⟨alpha, ha, _⟩ := tensorComparisonDescent
    (K := CochainComplex A ℤ) (H := CochainComplex B ℤ)
    (D := DerivedCategory A) (E := DerivedCategory B)
    DerivedCategory.Q DerivedCategory.Q F s.derived eps PR PS hF ff' tR tS
    a.tensor target.tensor a.representative target.representative b
    (fun P hp ↦ by rw [heps]; exact s.computes P hp)
    (fun P Q hp hq ↦ by
      rw [heps]
      exact s.computes _ (coefficientTotalTensor_isKFlat.{u, t + 1, t} J R P Q hp hq))
  refine ⟨alpha, ?_⟩
  intro P Q hp hq
  refine ⟨hF P hp, hF Q hq, (b.app (P, Q)).inv, Iso.isIso_inv _, ?_, ?_⟩
  · intro i j U x y
    have h := hg P Q i j (i + j) rfl U x y
    dsimp only [c, s, integralReductionScalarPair] at h
    erw [totalPair_eq_generator.{t, u} Y (integralCoefficientCommRingSheaf l E Y n),
      totalPair_eq_generator.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)]
    simp only [pairUnit, actual_ordinaryAdjunction,
      reductionUnit] at h ⊢
    dsimp only [coefficientTotalTensor, totalTensor, ordinaryTensor, scalarReductionExtension,
      scalarReductionExistence] at h ⊢
    exact h
  · have hh := ha P Q hp hq
    have hc (X : CochainComplex A ℤ) : reductionCounit l E Y D hl n X = eps.app X :=
      (actual_pairCounit l E Y D hl n X).trans (heps X).symm
    have h := inverseSquare _ _ _ _ (DerivedCategory.Q.mapIso (b.app (P, Q)))
      (target.representative.app (⟨F.obj P, hF P hp⟩, ⟨F.obj Q, hF Q hq⟩)) hh
    have hm : target.tensor.map (Prod.mkHom (eps.app P) (eps.app Q)) =
        target.tensor.map (Prod.mkHom (reductionCounit l E Y D hl n P)
          (reductionCounit l E Y D hl n Q)) :=
      congrArg (fun f ↦ target.tensor.map f)
        (congrArg₂ Prod.mkHom (hc P).symm (hc Q).symm)
    erw [hm] at h
    dsimp only [tR, coefficientTotalTensor, totalTensor, ordinaryTensor] at h ⊢
    simp only [← hc] at h
    dsimp only [s, integralReductionScalarPair, F, Iso.app, Functor.mapIso, uncurry_obj_obj] at h
    exact h

end WeilConjectures.IntegralHom
