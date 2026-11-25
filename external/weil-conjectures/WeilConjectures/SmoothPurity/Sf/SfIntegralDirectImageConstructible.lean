/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero
import WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.SmoothPurity.NilpotentCoefficientDirectImageBound
import WeilConjectures.AlgebraicGeometry.Sf.SfEtaleOriginPushforwardAmplitude
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteProEtalePushforwardConstructible
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-!
# Integral direct image preserves bounded constructibility

Source: Bhatt--Scholze, Lemma 6.7.2, with Lemmas 6.5.9 and 6.5.11;
Stacks Tags 0F10 and 099N
(blueprint: lem-sf-integral-direct-image-constructible).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem intrinsic_iso
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    {C D : proEtaleDerivedCategory T B} (e : C ≅ D)
    (h : (Set.Finite (proEtaleCohomologicalSupport C)) ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
        ((DerivedCategory.homologyFunctor _ i).obj C)) :
    Set.Finite (proEtaleCohomologicalSupport D) ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
        ((DerivedCategory.homologyFunctor _ i).obj D) := by
  constructor
  · apply h.1.subset
    intro i hi
    exact fun hz ↦ hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    have hc := h.2 i
    rw [proEtaleModuleRestriction_constructible_iff] at hc ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T B).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hc

private theorem support_iso
    (T : Scheme.{u}) (B : Type u) [CommRing B]
    {C D : proEtaleDerivedCategory T B} (e : C ≅ D) :
    proEtaleCohomologicalSupport C = proEtaleCohomologicalSupport D := by
  ext i
  exact not_congr ((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff

private theorem coefficient_killed (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ((l ^ n : ℕ) : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) = 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  apply ULift.down_injective
  change ((l ^ n : ℕ) :
    Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
    Ideal.Quotient.eq_zero_iff_mem]
  simpa only [Nat.cast_pow] using hpow

private theorem residue_bound_all_levels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (N : ℤ)
    (hN : ∀ (q : ℕ), N < (q : ℤ) →
      ∀ M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))),
      IsZero (((Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)))
        f).rightDerived q).obj M)) (n : ℕ) :
    ∀ M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))),
      ∀ q : ℤ, 0 ≤ q → N < q →
        IsZero (Etale.higherDirectImage
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) f q M) := by
  let A := Padic.coefficientExtensionIntegers l E
  let J : Ideal A := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  let R := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let S := ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)
  have hle : J ^ (n + 1) ≤ J ^ 1 := Ideal.pow_le_pow_right (by omega)
  let p₀ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l E 1 := Ideal.Quotient.factor hle
  let eR : R ≃+* Padic.coefficientExtensionRing l E (n + 1) := ULift.ringEquiv
  let eS : S ≃+* Padic.coefficientExtensionRing l E 1 := ULift.ringEquiv
  let p : R →+* S := eS.symm.toRingHom.comp (p₀.comp eR.toRingHom)
  have hp : Function.Surjective p :=
    eS.symm.surjective.comp ((Ideal.Quotient.factor_surjective hle).comp eR.surjective)
  have hker₀ : RingHom.ker p₀ = (J ^ 1).map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    change RingHom.ker (Ideal.Quotient.lift _ (Ideal.Quotient.mk _) _) = _
    rw [Ideal.ker_quotient_lift, Ideal.mk_ker]
    rfl
  have hnil₀ : (RingHom.ker p₀) ^ (n + 1) = ⊥ := by
    rw [hker₀, ← Ideal.map_pow, pow_one, Ideal.map_mk_eq_bot_of_le le_rfl]
  have hker : RingHom.ker p = (RingHom.ker p₀).comap eR.toRingHom := by
    dsimp only [p]
    rw [RingHom.ker_equiv_comp, RingHom.comap_ker]
  have hnil : (RingHom.ker p) ^ (n + 1) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [hker]
    apply (Ideal.le_comap_pow eR.toRingHom (n + 1)).trans
    rw [hnil₀]
    exact le_of_eq ((RingHom.injective_iff_ker_eq_bot eR.toRingHom).mp eR.injective)
  let e : R ⧸ RingHom.ker p ≃+* S := RingHom.quotientKerEquivOfSurjective hp
  apply Etale.isZero_higherDirectImage_of_nilpotent_quotient_bound
    f R (RingHom.ker p) (n + 1) (by omega) hnil N
  intro Q q hq hNq
  let Q' := (Sheaf.restrictScalars X.smallEtaleTopology e.symm.toRingHom).obj Q
  have hz : IsZero (Etale.higherDirectImage S f q Q') := by
    lift q to ℕ using hq
    exact (hN q hNq Q').of_iso
      ((Etale.lowerStar (ModuleCat.{u + 1} S)
        f).homologyRightDerivedFunctorPlusObjSingleFunctorIso Q' q)
  exact (Etale.isZero_higherDirectImage_restrictScalars_iff e.symm.toRingHom f q Q).mp hz

private theorem finite_image_constructible
    (k : Type u) [Field k] (B : Type u) [CommRing B] [Finite B]
    (m : ℕ) (hm : 0 < m) (hB : (m : ULift.{u + 1} B) = 0)
    (hk : IsUnit (m : k))
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (C : proEtaleDerivedCategory X B)
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X B
      ((DerivedCategory.homologyFunctor _ i).obj C))
    (a b : ℤ) (hab : a ≤ b)
    (hv : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj C)) :
    Set.Finite (proEtaleCohomologicalSupport
      ((proEtaleConstantDerivedDirectImage f B).obj C)) ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
        ((DerivedCategory.homologyFunctor _ i).obj
          ((proEtaleConstantDerivedDirectImage f B).obj C)) := by
  classical
  let R := fun T : Scheme.{u} ↦ ProEtale.finiteCoefficientIntrinsicRealization T B
  have hR (T : Scheme.{u}) : (R T).IsEquivalence :=
    (ProEtale.finiteCoefficientIntrinsicRealization_exact T B).1
  let := hR X
  let := hR Y
  let J := (R X).mapDerivedCategory.objPreimage C
  let eJ : (R X).mapDerivedCategory.obj J ≅ C :=
    (R X).mapDerivedCategory.objObjPreimageIso C
  have hJ (i : ℤ) : (R X).obj ((DerivedCategory.homologyFunctor _ i).obj J) ≅
      (DerivedCategory.homologyFunctor _ i).obj C :=
    ((R X).mapDerivedCategoryHomologyFunctorIso i).app J ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso eJ
  have hcJ (i : ℤ) : IsConstructibleProEtaleFixedModuleSheaf X (ULift.{u + 1} B)
      ((DerivedCategory.homologyFunctor _ i).obj J) := by
    apply (ProEtale.fixed_constructible_iff _ _ _).mpr
    apply (intrinsicRealization_constructible_iff X B _).mp
    exact intrinsicConstructible_of_iso X B (hJ i).symm (hc i)
  have hvJ (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj J) := by
    have hz := (hv i hi).of_iso (hJ i)
    rw [IsZero.iff_id_eq_zero] at hz ⊢
    exact (R X).map_injective (by simpa using hz)
  obtain ⟨L, hL, α, hα, hcF, c, d, hcd, hvF⟩ :=
    ProEtale.finite_proetale_pushforward_constructible k (ULift.{u + 1} B)
      m hm hB hk aX aY f hf J hcJ ⟨a, b, hab, hvJ⟩
  let F := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).rightDerivedFunctor
  let e : (R Y).mapDerivedCategory.obj (F.obj J) ≅
      (proEtaleConstantDerivedDirectImage f B).obj C :=
    (sfIntrinsicDerivedDirectImageComparison f B).symm.app J ≪≫
      (proEtaleConstantDerivedDirectImage f B).mapIso eJ
  have he (i : ℤ) : (R Y).obj ((DerivedCategory.homologyFunctor _ i).obj (F.obj J)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        ((proEtaleConstantDerivedDirectImage f B).obj C) :=
    ((R Y).mapDerivedCategoryHomologyFunctorIso i).app (F.obj J) ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e
  constructor
  · apply (Set.finite_Icc c d).subset
    intro i hi
    by_contra hout
    have ho : i < c ∨ d < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hout
    exact hi (((R Y).map_isZero (hvF i ho)).of_iso (he i).symm)
  · intro i
    apply intrinsicConstructible_of_iso Y B (he i)
    apply (intrinsicRealization_constructible_iff Y B _).mpr
    exact (ProEtale.fixed_constructible_iff _ _ _).mp (hcF i)

private theorem finite_image_support
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (B : Type u) [CommRing B] [Finite B] (N : ℤ)
    (hN : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))
      (q : ℤ), 0 ≤ q → N < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          f).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (C : proEtaleDerivedCategory X B)
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X B
      ((DerivedCategory.homologyFunctor _ i).obj C))
    (hbounded : ∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, i < c ∨ d < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj C))
    (a b : ℤ) (hs : proEtaleCohomologicalSupport C ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport ((proEtaleConstantDerivedDirectImage f B).obj C) ⊆
      Set.Icc a (b + N) := by
  obtain ⟨L, ⟨e⟩⟩ := ((finiteRing_constructibleDerived_origin X B).2.2.1 C).mpr
    ⟨hc, hbounded⟩
  have hL := L.property.2
  have he := (proEtaleConstantDerivedDirectImage f B).mapIso e
  have hamp (c d : ℤ) (hcd : c ≤ d)
      (hv : ∀ i : ℤ, i < c ∨ d < i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj C))
      (i : ℤ) (hi : i < c ∨ d + N < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((proEtaleConstantDerivedDirectImage f B).obj C)) := by
    have hC (r : ℤ) (hr : r < c ∨ d < r) :=
      (hv r hr).of_iso ((DerivedCategory.homologyFunctor _ r).mapIso e)
    have hz := (ProEtale.etaleOrigin_pushforward_amplitude f B N hN c d hcd
      L.obj hL hC).2.1 i hi
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso he).symm
  intro i hi
  by_contra hout
  have ho : i < a ∨ b + N < i := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hout
  by_cases hab : a ≤ b
  · exact hi (hamp a b hab (fun r hr ↦ by
      by_contra hz
      obtain ⟨h₁, h₂⟩ := hs hz
      rcases hr with hr | hr <;> exact (by omega)) i ho)
  · exact hi (hamp (i + 1) (i + 1) le_rfl (fun r _ ↦ by
      by_contra hz
      obtain ⟨h₁, h₂⟩ := hs hz
      exact (by omega)) i (Or.inl (by omega)))

set_option linter.unusedVariables false in
/-- Preservation of constructibility, every canonical reduction comparison, and uniform
cohomological bounds, including the dimension and empty-source cases.
Source: Bhatt--Scholze, Lemma 6.7.2; Stacks Tag 0F10
(blueprint: lem-sf-integral-direct-image-constructible).
Proof: the derived category has countable products, so completing the prescribed
one-minus-transition map to a distinguished triangle gives an integral direct image.
The geometry-independent complete direct-image and reduction theorem gives completeness
and identifies the canonical finite reductions of every such triangle.

For finite constructibility, use the exact equivalence between fixed-coefficient and
intrinsic finite-ring module sheaves. It commutes with homology and intertwines the two
actual derived direct images. The finite-coefficient constructibility theorem therefore
gives finite intrinsic cohomological support and constructible cohomology at every level.
The quotient O_E/varpi^(n+1) is killed by l^(n+1), since l lies in the maximal ideal;
this annihilator is invertible in the base field.

The proved torsion-module dimension theorem and the uniform dimension bound after field
extension give a nonnegative residue-coefficient bound N. For any qualifying integer N,
the surjection O_E/varpi^(n+1) -> O_E/varpi has nilpotent kernel. Nilpotent coefficient
devissage, followed by coefficient change along the resulting quotient-ring isomorphism,
gives this same N at every level. The finite-ring origin equivalence and the etale-origin
amplitude theorem now give support [a,b+N] from [a,b]. If a>b, the input is zero in every
degree; apply that amplitude theorem with an interval above the degree being tested.
This argument also retains negative qualifying bounds. Transport constructibility and
support through the canonical reduction isomorphisms and use the definition of integral
constructibility. Over an algebraically closed field, the explicit torsion-module bound
is 2 dim X. For empty X its discrete topology has Krull dimension at most zero, giving
the stated bound zero without assigning the empty scheme a natural-number dimension.
-/
theorem sfIntegralDirectImage_constructible
    (K₀ : Type u) [Field K₀] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : K₀))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K) :
    (∃ hprod : HasProduct (sfDirectImageTerm l E f K),
      @Nonempty (@SfIntegralDirectImage l _ E _ _ _ X Y f K hprod)) ∧
    (∀ [hprod : HasProduct (sfDirectImageTerm l E f K)]
      (L : SfIntegralDirectImage l E f K),
      sfIntegralConstructible l E Y L.obj ∧ IsSfDerivedComplete l E Y L.obj ∧
        (∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n)) ∧
        (∀ n : ℕ, intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y (sfFiniteDerivedDirectImage l E f K n))) ∧
    (∃ N : ℤ, ∀ (q : ℕ), N < (q : ℤ) →
      ∀ M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))),
        IsZero (((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)))
            f).rightDerived q).obj M)) ∧
    (∀ N : ℤ,
      (∀ (q : ℕ), N < (q : ℤ) →
        ∀ M : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))),
          IsZero (((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)))
            f).rightDerived q).obj M)) →
      ∀ a b : ℤ,
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ⊆ Set.Icc a b) →
        ∀ n : ℕ, proEtaleCohomologicalSupport (sfFiniteDerivedDirectImage l E f K n) ⊆
          Set.Icc a (b + N)) ∧
    (IsAlgClosed K₀ → ∀ d : ℕ, Nonempty X →
      topologicalKrullDim X = (d : WithBot ℕ∞) →
      ∀ (q : ℕ), 2 * d < q →
        ∀ M : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))),
          IsZero (((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)))
            f).rightDerived q).obj M)) ∧
    (IsAlgClosed K₀ → IsEmpty X → ∀ (q : ℕ), 0 < q →
      ∀ M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))),
        IsZero (((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)))
            f).rightDerived q).obj M)) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K₀))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K₀))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of K₀))
  have : QuasiCompact f := inferInstance
  have : QuasiSeparated f := inferInstance
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of K₀))) := by
    rw [comp_over f _]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of K₀))
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)
  have : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 le_rfl
  have : Finite B := inferInstance
  have hbound : ∃ N : ℤ, 0 ≤ N ∧ ∀ q : ℕ, N < (q : ℤ) →
      ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B),
        IsZero (((Etale.lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M) := by
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_isPullback
      (X ↘ Spec (.of K₀))
    refine ⟨2 * d, by positivity, fun q hq M ↦ ?_⟩
    have hz := Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le B
      isAddTorsion_of_finite (X ↘ Spec (.of K₀)) (Y ↘ Spec (.of K₀)) f
      (comp_over f _) d hd M q hq
    exact hz.of_iso
      ((Etale.lowerStar (ModuleCat.{u + 1} B)
        f).homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm
  have hAmplitude : ∀ N : ℤ,
      (∀ (q : ℕ), N < (q : ℤ) →
        ∀ M : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))),
          IsZero (((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)))
            f).rightDerived q).obj M)) →
      ∀ a b : ℤ,
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) ⊆ Set.Icc a b) →
        ∀ n : ℕ, proEtaleCohomologicalSupport (sfFiniteDerivedDirectImage l E f K n) ⊆
          Set.Icc a (b + N) := by
    intro N hN a b hs n
    let Bn := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite Bn := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    obtain ⟨c, d, hcd, hKcd⟩ := _hK.2
    apply finite_image_support f Bn N _ ((scalarReductionDerivedExtension l E X n).obj K)
      (hKcd n).1.2 ⟨c, d, hcd, ?_⟩ a b (hs n)
    · intro M q hq hNq
      have hz := residue_bound_all_levels l E f N hN n M q hq hNq
      lift q to ℕ using hq
      have hz' := hz.of_iso
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} Bn))
          f).homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm
      exact hz'.of_iso
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} Bn))
          f).homologyRightDerivedFunctorObjSingleFunctorIso M q)
    · intro i hi
      by_contra hz
      obtain ⟨h₁, h₂⟩ := (hKcd n).2 hz
      rcases hi with hi | hi <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let A := scalarReductionSource l E Y
    let : HasCountableProducts A := (ProEt.countableProducts_exact.{u, u, 0} Y
      (completedIntegralCommRingSheafUnrestricted l E Y)).1
    let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
    have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
      { preserves := by
          intro F G g hg
          have h := (ProEt.countableProducts_exact.{u, u, 0} Y
            (completedIntegralCommRingSheafUnrestricted l E Y)).2.2
            ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
            (fun n ↦ g.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map g = (Limits.Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ g.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
    have := CountableAB4Star.of_hasExactLimitsOfShape_nat A
    let : HasCountableProducts (DerivedCategory A) :=
      (derivedCategory_countableProducts_core.{0} A).choose
    let : HasProduct (sfDirectImageTerm l E f K) := inferInstance
    obtain ⟨L, p, δ, h⟩ := Pretriangulated.distinguished_cocone_triangle₁
      (towerTransitionEndomorphism (sfDirectImageTransition l E f K))
    exact ⟨inferInstance, ⟨⟨L, p, δ, h⟩⟩⟩
  · intro hp L
    obtain ⟨hcomplete, hred⟩ := sfCompleteDirectImage_reduction l E f K _hK.1 L
    obtain ⟨a, b, hab, hKn⟩ := _hK.2
    obtain ⟨N, hNnonneg, hN⟩ := hbound
    have hfinite (n : ℕ) : intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y (sfFiniteDerivedDirectImage l E f K n) := by
      let Bn := Padic.coefficientExtensionRing l E (n + 1)
      let : Finite Bn := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
      apply finite_image_constructible K₀ Bn (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (coefficient_killed l E _)
        (by simpa only [Nat.cast_pow] using _hl.pow (n + 1))
        (X ↘ Spec (.of K₀)) (Y ↘ Spec (.of K₀)) f (comp_over f _) _
        (hKn n).1.2 a b hab
      intro i hi
      by_contra hz
      obtain ⟨h₁, h₂⟩ := (hKn n).2 hz
      rcases hi with hi | hi <;> omega
    refine ⟨⟨hcomplete, a, b + N, by omega, fun n ↦ ?_⟩, hcomplete, hred, hfinite⟩
    let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    have := hred n
    let e := asIso (sfDirectImageReductionComparison l E f L n)
    exact ⟨intrinsic_iso Y _ e.symm (hfinite n), fun i hi ↦
      hAmplitude N hN a b (fun n ↦ (hKn n).2) n
        (by rwa [support_iso Y _ e] at hi)⟩
  · obtain ⟨N, _, hN⟩ := hbound
    exact ⟨N, hN⟩
  · exact hAmplitude
  · intro hclosed d _ hd q hq M
    let : IsAlgClosed K₀ := hclosed
    have hz := Etale.isZero_higherDirectImage_of_two_mul_lt (Λ := B)
      isAddTorsion_of_finite f (X ↘ Spec (.of K₀)) (Y ↘ Spec (.of K₀))
      (comp_over f _) d hd.le M q (by exact_mod_cast hq)
    exact hz.of_iso
      ((Etale.lowerStar (ModuleCat.{u + 1} B)
        f).homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm
  · intro hclosed hempty q hq M
    let : IsAlgClosed K₀ := hclosed
    let : IsEmpty X := hempty
    have hdim : topologicalKrullDim X ≤ (0 : WithBot ℕ∞) := by
      exact topologicalKrullDim_zero_of_discreteTopology X
    have hz := Etale.isZero_higherDirectImage_of_two_mul_lt (Λ := B)
      isAddTorsion_of_finite f (X ↘ Spec (.of K₀)) (Y ↘ Spec (.of K₀))
      (comp_over f _) 0 hdim M q (by exact_mod_cast hq)
    exact hz.of_iso
      ((Etale.lowerStar (ModuleCat.{u + 1} B)
        f).homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm

end WeilConjectures
