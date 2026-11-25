/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralNormalization
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso

/-! # Finite tensor comparison with condensed coefficients

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
attribute [local irreducible] nativeCondensedDerived nativeCondensedModules

private theorem representative_of_stage_normalization
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] {B : Type*} [Category B]
    (S : StageSystem C) (H : S.PairCategory ⥤ B) (F : ∀ i, C i ⥤ B)
    (e : ∀ i, S.ι i ⋙ H ≅ F i)
    (p : ∀ {i j} (h : i ≤ j), F i ≅ S.T h ⋙ F j)
    (he : ∀ (A : S.PairCategory) (j : I) (h : A.stage ≤ j),
      H.map (S.isoToStage A h).hom ≫ (e j).hom.app (A.toStage h) =
        (e A.stage).hom.app A.obj ≫ (p h).hom.app A.obj)
    {A A' : S.PairCategory} (j : I) (hA : A.stage ≤ j) (hA' : A'.stage ≤ j)
    (f : A.toStage hA ⟶ A'.toStage hA') :
    H.map (StageSystem.PairCategory.mkHom j hA hA' f) =
      (e A.stage).hom.app A.obj ≫ (p hA).hom.app A.obj ≫
        (F j).map f ≫ (p hA').inv.app A'.obj ≫ (e A'.stage).inv.app A'.obj := by
  let c (A : S.PairCategory) : H.obj A ≅ (F A.stage).obj A.obj :=
    (e A.stage).app A.obj
  have hc (A : S.PairCategory) (j : I) (h : A.stage ≤ j) :
      H.map (S.isoToStage A h).hom ≫ (e j).hom.app (A.toStage h) =
        (c A).hom ≫ (p h).hom.app A.obj := he A j h
  change H.map (StageSystem.PairCategory.mkHom j hA hA' f) =
    (c A).hom ≫ (p hA).hom.app A.obj ≫ (F j).map f ≫
      (p hA').inv.app A'.obj ≫ (c A').inv
  have hi : H.map (S.isoToStage A' hA').inv ≫ (c A').hom =
      (e j).hom.app (A'.toStage hA') ≫ (p hA').inv.app A'.obj := by
    apply (cancel_epi (H.map (S.isoToStage A' hA').hom)).mp
    rw [← H.map_comp_assoc, Iso.hom_inv_id, H.map_id, Category.id_comp]
    rw [← Category.assoc, hc A' j hA']
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (cancel_mono (c A').hom).mp
  rw [StageSystem.mkHom_eq_isoToStage hA hA' f]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hi]
  have hn := (e j).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Category.assoc, hc A j hA]
  simp only [Category.assoc]

/-- Finite coefficient realization agrees with the normalized native tensor formula.

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), Proposition 6.8.14(2),
and Remark 6.8.15; the finite-stage identification in the parent Hom-descent proof
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison).

Proof in words: first apply the integral identity equivalence between strict-tower and
completed integral presentations, and rationalize it. Compose with the continuous rational
realization at the finite field. The section-ring comparison for that finite condensed
coefficient identifies continuous modules with internal modules. Constructible rational
Hom comparison makes this finite realization full and faithful; preservation of local
finite freeness puts its image in the bounded constructible condensed category. Neither
essential surjectivity of this finite functor nor a closure Hom quotient is required.
For E ≤ L, inverse-completion
scalar coherence, the continuous realization scalar comparison, and balanced tensor
transitivity give the displayed scalar isomorphism. The finite coefficient inclusion
followed by condensedNativeMap is the specified rational inclusion of D: both maps evaluate
a function by the fixed embedding. Integral residue normalization identifies their integral
maps. Hence D.integral identifies the integral restrictions of both realizations. The
universal property of localization extends this identification to the raw rational stage,
giving objectIso. On an integral arrow its naturality is exactly that of D.integral;
inverse uniformizer powers are preserved by functoriality. The equation D.common_field
identifies the transition isomorphisms with the same completion and tensor comparisons.
Write a representative as isoToStage, then a stage arrow, then the inverse isoToStage.
Mapping this expression proves the representative equation. Identity extensions use the
unit comparison; repeated fields and zero objects use the same formulas. For the empty
scheme the categories and formulas are the zero ones. This lemma asserts finite tensor
normalization only, with no Hom-surjectivity, eventual equality, or essential-image claim
at the algebraic closure.
-/
theorem condensedStageComparison_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    Nonempty (CondensedStageComparison l X D)  := by
  classical
  obtain ⟨A⟩ := AdicFiniteRealization.finiteData_exists l X
  obtain ⟨e, he⟩ := finiteCondensedIntegralNormalization l X D A
  let H := D.J ⋙ nativeCondensedDerived l X
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X
  let F := AdicFiniteRealization.finiteCondensedClosureFunctor l X A
  have hd (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
      ∃! d : GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ H ≅ F E,
        ∀ K : sfIntegralConstructibleCategory l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X,
          d.hom.app ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K) =
              (e E).hom.app K := by
    letI : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) n).Additive :=
      fun n ↦ inferInstance
    letI : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) n).Linear
          (Padic.coefficientExtensionIntegers l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)) :=
      fun n ↦ sfIntegralConstructibleShift_linear l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X n
    exact ScalarLocalization.naturalIso_of_integral
      (Padic.coefficientExtensionIntegers l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E))
      (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
      (Padic.coefficientExtensionUniformizer l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E))
      (GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ H) (F E) (e E)
  let d E := (hd E).exists.choose
  have de (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E) :
      (d E).hom.app K = (e E).hom.app K.obj :=
    (hd E).exists.choose_spec K.obj
  have ht (B : S.PairCategory) (L : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : B.stage ≤ L) :
      H.map (S.isoToStage B h).hom ≫ (d L).hom.app (B.toStage h) =
        (d B.stage).hom.app B.obj ≫
          (AdicFiniteRealization.finiteCondensedClosureTransition l X A h).hom.app B.obj := by
    rw [de, de]
    exact he B.stage L h B.obj.obj
  let objectComparison (B : S.PairCategory) :
      (nativeCondensedDerived l X).obj (D.J.obj B) ≅ (F B.stage).obj B.obj :=
    (d B.stage).app B.obj
  refine ⟨{
    finite := AdicFiniteRealization.finiteCondensedFunctor l X A
    full := fun E ↦ inferInstance
    faithful := fun E ↦ inferInstance
    scalar := AdicFiniteRealization.finiteCondensedScalarComparison l X A
    objectIso := objectComparison
    representative := ?_
  }⟩
  intro B C L hB hC f
  have hf := representative_of_stage_normalization S H F d
    (fun {_ _} h ↦ AdicFiniteRealization.finiteCondensedClosureTransition l X A h)
    ht L hB hC f
  change H.map (StageSystem.PairCategory.mkHom L hB hC f) =
    (objectComparison B).hom ≫
      (AdicFiniteRealization.finiteCondensedClosureTransition l X A hB).hom.app B.obj ≫
      (F L).map f ≫
      (AdicFiniteRealization.finiteCondensedClosureTransition l X A hC).inv.app C.obj ≫
      (objectComparison C).inv at hf
  simpa only [H, F, AdicFiniteRealization.finiteCondensedClosureFunctor,
    AdicFiniteRealization.finiteCondensedClosureTransition,
    Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Iso.symm_inv, Functor.comp_map,
    Functor.map_comp, Functor.comp_obj, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using hf

end WeilConjectures.LocallyFiniteAdicRealization
