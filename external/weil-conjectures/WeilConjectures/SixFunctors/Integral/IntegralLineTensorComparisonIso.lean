/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonDefinitions
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonRepresentative
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Integral line tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings MonoidalCategory
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- The completion comparison is invertible on a derived-complete object.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-sf-integral-line-tensor-comparison-iso).

Proof: take a flat-term K-flat representative P of C. The identity-extension
specialization of finiteFreeCompletedScalarComparison makes the prescribed quotient
completion augmentation of P invertible. Tensor by T is an exact equivalence, with
inverse tensor by its dual: after a cover trivializing T both composites are the
identity, so the local identifications glue. This equivalence preserves countable
products and mapping cones. The balancing isomorphisms identify the tower of the
tensor complex with tensor by T of the original restricted quotient tower. These
isomorphisms preserve every quotient transition and the augmentation x ↦ 1 tensor x.
Consequently the augmentation of P tensor T is tensor by T of the invertible
augmentation of P. It is invertible after localization. The representative
normalization defining completionUnit identifies this augmentation with exactly
integralLineComparison, including its zero shifted component. Conjugation by the
representative isomorphisms proves the displayed assertion. No boundedness or
constructibility assumption is used. -/
theorem integralLineTensorComparison_iso
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : D l E X none) (hC : IsComplete l E X none C)
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1] :
    IsIso ((integralLineComparison l E X).app (C, T)) := by
  classical
  let R := ring l E X none
  let q := qGood l E X none
  let : q.IsLocalization ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (Good l E X none).ι) := goodLocalization l E X none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (Good l E X none).ι)
  let P := q.objPreimage C
  let e : DerivedCategory.Q.obj P.obj ≅ C := q.objObjPreimageIso C
  obtain ⟨hT, hS, hfinite⟩ := integralLineTensorComparison_representative l E X T P
  clear hfinite
  let er := integralLineRepresentativeIso l E X P T hT C e
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  let F := MonoidalCategory.tensorRight T
  have hcover : ∀ U : X.ProEt, ∃ s : Sieve U,
      s ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
      ∀ (V : X.ProEt) (f : V ⟶ U), s f →
        Nonempty (T.over V ≅ SheafOfModules.unit ((rings l E X none).over V)) := by
    obtain ⟨I, V, hV, h⟩ :=
      (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := T) (r := 1)).mp inferInstance
    intro U
    refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
    rintro Z f ⟨i, ⟨g⟩⟩
    let ei := (h i).some ≪≫ SheafOfModules.freeUniqueIso (ULift (Fin 1))
    exact ⟨((SheafOfModules.overFunctorMap (rings l E X none) g).app T).symm ≪≫
      (SheafOfModules.overMap (rings l E X none) g).mapIso ei ≪≫
      SheafOfModules.overMapUnitIso g⟩
  obtain ⟨_, _, _, hfl, hfc, _, _, _, _, _, _, ev, _, _, a, b, _, _, ht, _⟩ :=
    SheafOfModules.LineEvaluation.evaluation_inverse_pair R T hcover
  let := hfl
  let := hfc
  let eqv : Mod l E X none ≌ Mod l E X none :=
    ⟨F, MonoidalCategory.tensorRight (SheafOfModules.LineEvaluation.dual R T),
      a.symm, b, ht⟩
  let : F.IsEquivalence := eqv.isEquivalence_functor
  let G := F.mapHomologicalComplex (.up ℤ)
  let ec : integralLineComplex l E X P.obj T ≅ G.obj P.obj :=
    CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor (Mod l E X none)) T P.obj
  have hGP : Good l E X none (G.obj P.obj) := by
    constructor
    · intro A hA i
      let H := (Functor.map₂HomologicalComplex
        (MonoidalCategory.curriedTensor (Mod l E X none)) (.up ℤ) (.up ℤ) (.up ℤ)).obj A
      exact HomologicalComplex.ExactAt.of_iso (hS.1 A hA i) (H.mapIso ec)
    · intro i
      let ei := (HomologicalComplex.eval _ _ i).mapIso ec
      let et := SheafOfModules.siteSheafTensorRightIso R _ ≪≫
        (MonoidalCategory.curriedTensor (Mod l E X none)).flip.mapIso ei ≪≫
        (SheafOfModules.siteSheafTensorRightIso R _).symm
      exact (exactFunctor _ _).prop_of_iso et (hS.2 i)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨d, hdideal, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  -- Use the equivalent principal-cone unit, whose exact-equivalence API preserves its
  -- actual augmentation. This avoids a separate quotient-tower balancing argument.
  have hc := ((roosIntrinsicCompletenessEquivalence p l (by omega) E X d hdideal
    C P e).out 1 3).mp hC
  have hi : IsIso (DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E X P.obj))) := by
    change IsIso (e.inv ≫ DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E X P.obj))) at hc
    let := hc
    exact IsIso.of_isIso_comp_left e.inv _
  have hμ : End.of (G.map (integralKoszulScalar l E X P.obj).asHom) =
      integralKoszulScalar l E X (G.obj P.obj) := by
    apply End.ext
    apply HomologicalComplex.Hom.ext
    funext i
    apply SheafOfModules.LineEvaluation.pure_hom_ext R (P.obj.X i) T
    intro U x y
    have hm := SheafOfModules.LineEvaluation.pure_map R
      ((integralKoszulScalar l E X P.obj).asHom.f i) (𝟙 T) U x y
    rw [MonoidalCategory.tensorHom_id] at hm
    change (((integralKoszulScalar l E X P.obj).asHom.f i) ▷ T).val.app U _ = _
    calc
      _ = SheafOfModules.LineEvaluation.pureTensor R (P.obj.X i) T U
          (((integralKoszulScalar l E X P.obj).asHom.f i).val.app U x) y := hm
      _ = integralCompletionScalarValue l E X U •
          SheafOfModules.LineEvaluation.pureTensor R (P.obj.X i) T U x y := by
        have hx : ((integralKoszulScalar l E X P.obj).asHom.f i).val.app U x =
            integralCompletionScalarValue l E X U • x :=
          (integralKoszulScalar_existsUnique l E X P.obj).exists.choose_spec i U x
        exact (congrArg (fun z ↦
          SheafOfModules.LineEvaluation.pureTensor R (P.obj.X i) T U z y) hx).trans
            (SheafOfModules.LineEvaluation.pure_smul_left R _ _ U _ x y)
      _ = _ := ((integralKoszulScalar_existsUnique l E X (G.obj P.obj)).exists.choose_spec
        i U _).symm
  let : HasCountableProducts (Mod l E X none) :=
    { out := fun D ↦ SheafOfModules.hasLimitsOfShape.{max u (t + 1)}
        (D := Discrete D) («R» := rings l E X none) }
  obtain ⟨c, hc⟩ := CochainComplex.principalCompletionMap F
    (integralKoszulScalar l E X P.obj)
  have hqi : QuasiIso
      (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E X P.obj)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hi
  let := hqi
  have hm : IsIso (DerivedCategory.Q.map
      (G.map (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E X P.obj)))) := by
    infer_instance
  have hs : IsIso (DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E X (G.obj P.obj)))) := by
    have hu : IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
        (End.of (G.map (integralKoszulScalar l E X P.obj).asHom)))) := by
      rw [← hc, Functor.map_comp]
      infer_instance
    exact (congrArg (fun μ : End (G.obj P.obj) ↦ IsIso (DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit μ))) hμ).mp hu
  let PG : (Good l E X none).FullSubcategory := ⟨G.obj P.obj, hGP⟩
  have hcG : IsComplete l E X none (DerivedCategory.Q.obj PG.obj) := by
    apply ((roosIntrinsicCompletenessEquivalence p l (by omega) E X d hdideal
      (DerivedCategory.Q.obj PG.obj) PG (Iso.refl _)).out 1 3).mpr
    change IsIso (𝟙 _ ≫ DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E X (G.obj P.obj))))
    simpa only [Category.id_comp] using hs
  have huG := ((roosIntrinsicCompletenessEquivalence p l (by omega) E X d hdideal
    (DerivedCategory.Q.obj PG.obj) PG (Iso.refl _)).out 1 5).mp hcG
  let ed : DerivedCategory.Q.obj PG.obj ≅ (integralLineOrdinary l E X).obj (C, T) :=
    (DerivedCategory.Q.mapIso ec).symm ≪≫ er
  exact (NatTrans.isIso_app_iff_of_iso (completionUnit l E X none) ed).mp huG

end WeilConjectures
