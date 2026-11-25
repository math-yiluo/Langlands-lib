/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomExactUniverses
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
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
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Completeness of bounded finite-projective completed-coefficient sheaf complexes

Source: Bhatt--Scholze, Lemma 6.5.5, finite-projective devissage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

private theorem complete_local_iff (K : IntegralOnSlice.D l E T none) :
    IsDerivedCompleteUnrestricted l E T K ↔
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K := by
  classical
  obtain ⟨P₀, q, hP₀, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) (DerivedCategory.Q.objPreimage K)
  let : QuasiIso q := hq
  let P : (IntegralOnSlice.Good l E T none).FullSubcategory :=
    ⟨P₀, hP₀, fun i ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (IntegralOnSlice.ring l E T none) _).symm
        (hflat i)⟩
  let e : DerivedCategory.Q.obj P.obj ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  exact (roosIntrinsicCompletenessEquivalence p l (by omega) E T d hd K P e).out 1 2

/-- A bounded complex of retracts of finite free completed-coefficient sheaves is
complete, with no hypothesis on the scheme or its residue characteristics.

Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Tags 099I and 0941.
(blueprint: lem-sf-bounded-projective-complex-complete-unrestricted).

Proof: use the intrinsic local-Hom criterion for the canonical quotient tower.
For each localized section, restriction followed by internal Hom is triangulated.
The free-cell theorem makes its value on every finite free cell zero. A splitting
into and out of a free module makes the value on a projective term a retract of
zero, hence zero. Its kernel is a triangulated subcategory. Bounded brutal-truncation
induction now makes its value on the entire complex zero. Apply the local-Hom
criterion in reverse. The argument allows rank zero, inverted bounds, arbitrary
sheaf-linear differentials, the empty scheme and the zero complex. -/
theorem boundedProjectiveComplex_complete
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hb : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k))
    (hP : ∀ k : ℤ, ∃ r : ℕ,
      ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E T)),
      ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E T))) ⟶ P.X k,
      i ≫ p = 𝟙 _) :
    IntegralOnSlice.IsComplete l E T none (DerivedCategory.Q.obj P) := by
  apply (complete_local_iff l E T _).mpr
  intro U s hs
  let : HasSheafify (IntegralOnSlice.topology T (some U)) CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  let R := IntegralOnSlice.rings l E T none
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over U))
  let F := SheafOfModules.overFunctor.{max u (t + 1)} R U
  let : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).1
  let : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  let A := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)
  let H := (Functor.curry.obj (IntegralOnSlice.hom l E T (some U))).obj (op A)
  obtain ⟨hshift, htri⟩ :=
    (CategoryTheory.RingedHomUniverses.ringedInternalHom_exact
      (IntegralOnSlice.topology T (some U)) (IntegralOnSlice.ring l E T (some U))).2 A
  let : H.CommShift ℤ := hshift
  let : H.IsTriangulated := htri
  let G := F.mapDerivedCategory ⋙ H
  have e (K : IntegralOnSlice.D l E T none) :
      IntegralPrincipalCone.localTest l E T K U s ≅ G.obj K :=
    (IntegralOnSlice.hom l E T (some U)).mapIso
      ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso R U K))
  have hfree (r : ℕ) : IsZero (G.obj (DerivedCategory.Q.obj
      (CompletedCoefficientFree.freeCell l E T r 0))) := by
    have hc := (CompletedCoefficientFree.completed_coefficient_free_resolution l E T).2.1 r 0
    exact (e _).isZero_iff.mp ((complete_local_iff l E T _).mp hc U s hs)
  have : G.kernel.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    exact ((G.commShiftIso n).app K).isZero_iff.mpr ((shiftFunctor _ n).map_isZero hK)
  have : G.kernel.IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun Δ hΔ h₁ h₃ ↦
      Triangle.isZero₂_of_isZero₁₃ _ (G.map_distinguished Δ hΔ) h₁ h₃)
  have : G.kernel.IsTriangulated := {}
  obtain ⟨a, b, hb⟩ := hb
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).mpr (fun k hk ↦ hb k (.inl hk))
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).mpr (fun k hk ↦ hb k (.inr hk))
  have hbounded := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (G.kernel.inverseImage DerivedCategory.Qh) P a b (fun k _ _ ↦ ?_)
  · exact ((G.mapIso ((DerivedCategory.quotientCompQhIso _).app P)).isZero_iff.mp
      hbounded).of_iso (e _)
  obtain ⟨r, i, p, hip⟩ := hP k
  let S := DerivedCategory.singleFunctor (scalarReductionSource l E T) 0
  have hz : IsZero (G.obj (S.obj (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)))) := hfree r
  let eSingle :
      DerivedCategory.Qh.obj
        ((HomotopyCategory.singleFunctor (scalarReductionSource l E T) 0).obj (P.X k)) ≅
        S.obj (P.X k) :=
    DerivedCategory.Qh.mapIso
      ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (scalarReductionSource l E T) 0).app (P.X k)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app
        ((CochainComplex.singleFunctor _ 0).obj (P.X k))
  apply (G.mapIso eSingle).isZero_iff.mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  have h : G.map (S.map i) ≫ G.map (S.map p) = 𝟙 (G.obj (S.obj (P.X k))) := by
    rw [← G.map_comp, ← S.map_comp, hip, S.map_id, G.map_id]
  rw [← h, hz.eq_of_tgt (G.map (S.map i)) 0, zero_comp]

end WeilConjectures.GeneratorReduction
