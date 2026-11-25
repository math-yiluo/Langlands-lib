/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineNormalizedEvaluations
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonIso
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineSupportPreservation
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLinePowerComparisons
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineDerivedComparisons
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Restriction of signed integral line tensor

(blueprint: lem-pur-integral-line-restrictions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem restrict_pair {C : Type*} [Category C] (P : ObjectProperty C)
    (T S U V : C ⥤ C)
    (hT : ∀ K : P.FullSubcategory, P (T.obj K.obj))
    (hS : ∀ K : P.FullSubcategory, P (S.obj K.obj))
    (hU : ∀ K : P.FullSubcategory, P (U.obj K.obj))
    (hV : ∀ K : P.FullSubcategory, P (V.obj K.obj))
    (cT : P.ι ⋙ T ≅ P.ι ⋙ U) (cS : P.ι ⋙ S ≅ P.ι ⋙ V)
    (v : T ⋙ S ≅ 𝟭 C) (w : S ⋙ T ≅ 𝟭 C)
    (hv : ∀ K : C, T.map (v.inv.app K) ≫ w.hom.app (T.obj K) = 𝟙 _) :
    ∃ (F : P.FullSubcategory ≌ P.FullSubcategory)
      (a : F.functor ⋙ P.ι ≅ P.ι ⋙ T) (b : F.inverse ⋙ P.ι ≅ P.ι ⋙ S),
      (∀ K, P.ι.map (F.unitIso.inv.app K) =
        b.hom.app (F.functor.obj K) ≫ S.map (a.hom.app K) ≫ v.hom.app K.obj) ∧
      (∀ K, P.ι.map (F.counitIso.hom.app K) =
        a.hom.app (F.inverse.obj K) ≫ T.map (b.hom.app K) ≫ w.hom.app K.obj) ∧
      ∃ (a' : F.functor ⋙ P.ι ≅ P.ι ⋙ U) (b' : F.inverse ⋙ P.ι ≅ P.ι ⋙ V),
        (∀ K, P.ι.map (F.unitIso.inv.app K) =
          b'.hom.app (F.functor.obj K) ≫ V.map (a'.hom.app K) ≫
            cS.inv.app ⟨U.obj K.obj, hU K⟩ ≫ S.map (cT.inv.app K) ≫ v.hom.app K.obj) ∧
        ∀ K, P.ι.map (F.counitIso.hom.app K) =
          a'.hom.app (F.inverse.obj K) ≫ U.map (b'.hom.app K) ≫
            cT.inv.app ⟨V.obj K.obj, hV K⟩ ≫ T.map (cS.inv.app K) ≫ w.hom.app K.obj := by
  let TF := P.lift (P.ι ⋙ T) hT
  let SF := P.lift (P.ι ⋙ S) hS
  let ev : TF ⋙ SF ≅ 𝟭 _ := NatIso.ofComponents
    (fun K ↦ P.isoMk (v.app K.obj)) (by
      intro K N f
      apply P.ι.map_injective
      exact v.hom.naturality f.hom)
  let coev : SF ⋙ TF ≅ 𝟭 _ := NatIso.ofComponents
    (fun K ↦ P.isoMk (w.app K.obj)) (by
      intro K N f
      apply P.ι.map_injective
      exact w.hom.naturality f.hom)
  let F : P.FullSubcategory ≌ P.FullSubcategory :=
    { functor := TF
      inverse := SF
      unitIso := ev.symm
      counitIso := coev
      functor_unitIso_comp K := by
        apply P.ι.map_injective
        exact hv K.obj }
  refine ⟨F, Iso.refl _, Iso.refl _, ?_, ?_, cT, cS, ?_, ?_⟩
  · intro K
    change v.hom.app K.obj = 𝟙 _ ≫ S.map (𝟙 _) ≫ v.hom.app K.obj
    rw [S.map_id, Category.id_comp, Category.id_comp]
  · intro K
    change w.hom.app K.obj = 𝟙 _ ≫ T.map (𝟙 _) ≫ w.hom.app K.obj
    rw [T.map_id, Category.id_comp, Category.id_comp]
  · intro K
    have hn := cS.inv.naturality
      (ObjectProperty.homMk (cT.hom.app K) : TF.obj K ⟶ ⟨U.obj K.obj, hU K⟩)
    change V.map (cT.hom.app K) ≫ cS.inv.app ⟨U.obj K.obj, hU K⟩ =
      cS.inv.app (TF.obj K) ≫ S.map (cT.hom.app K) at hn
    rw [← Category.assoc (V.map _) _ _, hn]
    change v.hom.app K.obj = cS.hom.app (TF.obj K) ≫
      (cS.inv.app (TF.obj K) ≫ S.map (cT.hom.app K)) ≫
        S.map (cT.inv.app K) ≫ v.hom.app K.obj
    rw [Category.assoc, cS.hom_inv_id_app_assoc, ← S.map_comp_assoc,
      cT.hom_inv_id_app]
    rw [S.map_id ((P.ι ⋙ T).obj K)]
    exact (Category.id_comp (v.hom.app K.obj)).symm
  · intro K
    have hn := cT.inv.naturality
      (ObjectProperty.homMk (cS.hom.app K) : SF.obj K ⟶ ⟨V.obj K.obj, hV K⟩)
    change U.map (cS.hom.app K) ≫ cT.inv.app ⟨V.obj K.obj, hV K⟩ =
      cT.inv.app (SF.obj K) ≫ T.map (cS.hom.app K) at hn
    rw [← Category.assoc (U.map _) _ _, hn]
    change w.hom.app K.obj = cT.hom.app (SF.obj K) ≫
      (cT.inv.app (SF.obj K) ≫ T.map (cS.hom.app K)) ≫
        T.map (cS.inv.app K) ≫ w.hom.app K.obj
    rw [Category.assoc, cT.hom_inv_id_app_assoc, ← T.map_comp_assoc,
      cS.hom_inv_id_app]
    rw [T.map_id ((P.ι ⋙ S).obj K)]
    exact (Category.id_comp (w.hom.app K.obj)).symm

private theorem complete_iff_unit (K : D.{u, u} l E X none) :
    IsComplete l E X none K ↔ IsIso ((completionUnit l E X none).app K) := by
  classical
  let q := qGood l E X none
  let : q.IsLocalization ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (Good l E X none).ι) := goodLocalization l E X none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (Good l E X none).ι)
  let P := q.objPreimage K
  let e : DerivedCategory.Q.obj P.obj ≅ K := q.objObjPreimageIso K
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  exact (roosIntrinsicCompletenessEquivalence p l (by omega) E X d hd K P e).out 1 5

private theorem comparison_isIso
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : D.{u, u} l E X none) (hK : IsComplete l E X none K) :
    IsIso ((comparison l E X L m).app K) := by
  have : (power l E X L m).IsFiniteLocallyFreeOfRank 1 := by
    rw [power_eq_coefficient]
    exact (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L m).1
  apply integralLineTensorComparison_iso l E X ?_ K hK (power l E X L m)
  intro x
  let := hl x
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
  simpa using (isUnit_of_invertible (l : X.residueField x)).ne_zero

private theorem ordinary_complete
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : D.{u, u} l E X none) (hK : IsComplete l E X none K) :
    IsComplete l E X none ((ordinary l E X L m).obj K) := by
  apply (complete_iff_unit l E X _).mpr
  exact comparison_isIso l E X hl L m K hK

local instance : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

local instance : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

open SheafOfModules.FlatSingleDerivedNormalization in
private theorem finite_ordinary_constructible
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (n : ℕ) (m : ℤ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible.{u} l E (n + 1) (by omega) X K) :
    intrinsicFiniteTorsionConstructible.{u} l E (n + 1) (by omega) X
      ((finiteOrdinary.{u} l E X L n m).obj K) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := integralCoefficientCommRingSheaf.{u, u} l E X n
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let M := finitePower l E X L n m
  have : M.IsFiniteLocallyFreeOfRank 1 := finite_power_rank l E X L n m
  have hM := (SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u, u + 2}
    X R M).1
  obtain ⟨hSingle, _, hLim, hCol, _⟩ :=
    flat_single_derived_normalization.{u + 1, u, u + 1, u + 2} R M hM
  let := hLim
  let := hCol
  let T := MonoidalCategory.tensorRight M
  let : PreservesFiniteLimits T := hLim
  let : PreservesFiniteColimits T := hCol
  let : T.PreservesHomology := Functor.preservesHomologyOfExact T
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := R) G
  let := hf
  let e : (DerivedCategory.Q.obj P : DerivedCategory (scalarReductionTarget.{u, u} l E X n)) ≅
      K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let collapse := SheafOfModules.FlatSingleDerivedNormalization.collapse.{u + 1, u, u + 1} R M
  let a : DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (finiteOrdinary.{u} l E X L n m).obj K :=
    (DerivedCategory.Q.mapIso (collapse.app P)).symm ≪≫
      (finiteModel l E X n).models.iso.{u, u + 1, u, u + 2} (ProEt.topology X) R
        (finiteModel l E X n).closed P ((CochainComplex.singleFunctor _ 0).obj M)
        hP hSingle ≪≫
      (finiteModel l E X n).closed.tensor.mapIso (Iso.prod e (Iso.refl _))
  constructor
  · exact hK.1.subset (finite_ordinary_support_subset l E X L n m K)
  · intro i
    let H := DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X n) i
    let c : H.obj ((finiteOrdinary.{u} l E X L n m).obj K) ≅ T.obj (H.obj K) :=
      H.mapIso a.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
        (P.sc i).mapHomologyIso T ≪≫
        T.mapIso ((DerivedCategory.homologyFunctorFactors _ i).app P).symm ≪≫
        T.mapIso (H.mapIso e)
    let F := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) M
    let : F.Additive := Functor.additive_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M).symm
    let : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso
      (SheafOfModules.siteSheafTensorRightIso R M).symm
    let : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso
      (SheafOfModules.siteSheafTensorRightIso R M).symm
    have hc := (finiteLineTensor_conditions X A M).2.1 (H.obj K) (hK.2 i)
    let d : F.obj (H.obj K) ≅ H.obj ((finiteOrdinary.{u} l E X L n m).obj K) :=
      (SheafOfModules.siteSheafTensorRightIso R M).app _ ≪≫ c.symm
    apply (proEtaleModuleRestriction_constructible_iff X A _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X A).mapIso d)
      ((proEtaleModuleRestriction_constructible_iff X A _).mp hc)

private theorem intrinsic_complete (K : sfIntegralConstructibleCategory l E X) :
    IsComplete l E X none K.obj := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl K.obj).mp K.property.1⟩

private theorem preserves_integral
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1] :
    PreservesIntegral l E X L := by
  let := sfIntegralConstructible_isClosedUnderIsomorphisms l E X
  obtain ⟨b, _, hb, _⟩ := integral_line_power_comparisons l E X L
  obtain ⟨d, _, hs⟩ := integral_line_derived_comparisons l E X L b hb
  intro m K
  have hK : IsComplete l E X none K.obj := intrinsic_complete l E X K
  have hc := ordinary_complete l E X hl L m K.obj hK
  have hO : sfIntegralConstructible l E X ((ordinary l E X L m).obj K.obj) := by
    obtain ⟨D, hD, hc⟩ := hc
    obtain ⟨_, a, z, haz, hred⟩ := K.property
    refine ⟨(sfDerivedComplete_iff_legacy l E X D hD _).mpr hc, a, z, haz, ?_⟩
    intro n
    let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    have hi : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible.{u} l E (n + 1) (by omega) X) :=
      (proEtale_bounded_constructible_isTriangulated X
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨?_, hs m K.obj a z (fun r ↦ (hred r).2) n⟩
    exact ObjectProperty.prop_of_iso _ ((d m n).app K.obj).symm
      (finite_ordinary_constructible l E X L n m _ (hred n).1)
  let := comparison_isIso l E X hl L m K.obj hK
  exact ⟨hO, ObjectProperty.prop_of_iso _ (asIso ((comparison l E X L m).app K.obj)) hO⟩

/-- Ordinary signed-line tensor preserves completeness, and its evaluations restrict
and transport to the integral category through the actual completion comparisons.
Source: Bhatt--Scholze 3.4.12, 3.5.1 and 3.5.2; blueprint proof (3).
(blueprint: lem-pur-integral-line-restrictions).

Proof: the opposite-line pairing makes exact tensor a triangulated equivalence,
which preserves products. Balance tensor past each reduction, with its quotient
transitions and reduction units. Transport the canonical augmented Roos triangle:
the first map is still exactly the reduction units and the second is 1 minus the
quotient shift. Thus ordinary tensor preserves completeness. For each finite
reduction its cohomology is the old cohomology tensored with the finite signed
line. Refine a finite constructible partition by a line-trivializing cover; its
finite model is M tensor A, isomorphic to M. Hence constructibility and the same
uniform support interval are preserved. The actual completion comparison is an
isomorphism on these complete objects, giving the completed membership statement
and the natural comparison c. Localize the ordinary evaluations on good models;
association and evaluation give the stated chain evaluation formula. The two
triangle identities hold on pure tensors and descend by localization. Fullness
restricts this equivalence and both evaluations to the integral subcategory.
Conjugate by c to obtain the completed functors and evaluations. Naturality cancels
successive inverse comparisons in both triangle identities. These are precisely
the two displayed evaluation equations in CompletedRestriction. -/
theorem integral_line_restrictions
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (hfinite : FiniteReductions l E X L)
    (e : Evaluations l E X L) (he : EvaluationFormula l E X L e) :
    (∀ (m : ℤ) (K : D.{u, u} l E X none), IsComplete l E X none K →
      IsComplete l E X none ((ordinary l E X L m).obj K)) ∧
      Restrictions l E X L e := by
  classical
  have _hfinite := hfinite
  refine ⟨ordinary_complete l E X hl L, ?_⟩
  let h := preserves_integral l E X hl L
  let c : ∀ m : ℤ, (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m ≅
      (sfIntegralConstructible l E X).ι ⋙ completed l E X L m := fun m ↦ by
    let α := Functor.whiskerLeft (sfIntegralConstructible l E X).ι (comparison l E X L m)
    letI : ∀ K, IsIso (α.app K) := fun K ↦
      comparison_isIso l E X hl L m K.obj (intrinsic_complete l E X K)
    letI : IsIso α := NatIso.isIso_of_isIso_app α
    exact asIso α
  refine ⟨h, c, fun _ ↦ rfl, ?_⟩
  intro m
  obtain ⟨v, w, hv, hw, ht⟩ := integral_line_normalized_evaluations l E X L e he m
  obtain ⟨F, a, b, ha, hb, a', b', ha', hb'⟩ := restrict_pair
    (sfIntegralConstructible l E X)
    (ordinary l E X L m) (ordinary l E X L (-m))
    (completed l E X L m) (completed l E X L (-m))
    (fun K ↦ (h m K).1) (fun K ↦ (h (-m) K).1)
    (fun K ↦ (h m K).2) (fun K ↦ (h (-m) K).2) (c m) (c (-m)) v w ht
  exact ⟨v, w, hv, hw, ⟨F, a, b, ha, hb⟩, ⟨F, a', b', ha', hb'⟩⟩

end WeilConjectures.IntegralLineReduction
