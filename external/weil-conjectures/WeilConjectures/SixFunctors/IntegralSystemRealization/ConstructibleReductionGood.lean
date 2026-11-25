/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.ZetaSeries

/-! # Single-operation bounds for completed compact support

Source: Stacks 0941, 0F10 and 0F7J; the common-bound argument in
lem-sf-completed-shriek-composition-laws, steps 7 and 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem support_of_iso {W : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : proEtaleDerivedCategory W A} (e : K ≅ L) :
    proEtaleCohomologicalSupport K = proEtaleCohomologicalSupport L := by
  ext i
  exact not_congr ((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff

private theorem tor_of_iso {W : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : proEtaleDerivedCategory W A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude W A L a b) : HasProEtaleTorAmplitude W A K a b := by
  refine ⟨h.1, ?_⟩
  intro P Q hP f hf hQ M i hi
  obtain ⟨eP⟩ := hP
  exact h.2 P Q ⟨eP ≪≫ e⟩ f hf hQ M i hi

private theorem constructible_of_iso (W : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L)
    (h : intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) W L) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) W K := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let P := intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) W
  have : P.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated W
      (Padic.coefficientExtensionRing l E (n + 1))).1
  exact P.prop_of_iso e.symm h

private theorem conjugate_cancel {C : Type*} [Category C] {A B D F G : C}
    (f : A ⟶ B) (g : B ⟶ D) (e : F ≅ D) (i : F ≅ G) :
    (f ≫ g ≫ e.inv ≫ i.hom) ≫ i.inv ≫ e.hom = f ≫ g := by
  simp

private theorem origins_of_bounds (W : Scheme.{u}) (M : System l E W)
    (hM : LevelBounds l E W M) : Nonempty (Origins l E W M) := by
  classical
  obtain ⟨a, b, c, d, hab, hcd, hlevels⟩ := hM
  have finite (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let := finite
  let R (n : ℕ) := sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))
  let C (n : ℕ) := ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))) W
  have origins (n : ℕ) : ∃ L : Etale.BoundedConstructibleDerivedCategory
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) W,
      Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison W
        (Padic.coefficientExtensionRing l E (n + 1))).obj L.obj ≅
          (coefficientSequenceDerivedEvaluation l E W n).obj M) := by
    apply (finiteRing_constructibleDerived_origin W
      (Padic.coefficientExtensionRing l E (n + 1))).2.2.1 _ |>.2
    refine ⟨(hlevels n).1.2, a, b, hab, ?_⟩
    intro i hi
    by_contra hz
    have hb : a ≤ i ∧ i ≤ b := (hlevels n).2.1 hz
    omega
  choose L e using origins
  let α (n : ℕ) : (C n).mapDerivedCategory.obj (L n).obj ≅
      (R n).inverse.mapDerivedCategory.obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj M) :=
    (R n).mapDerivedCategory.unitIso.app ((C n).mapDerivedCategory.obj (L n).obj) ≪≫
      (R n).inverse.mapDerivedCategory.mapIso
        ((Functor.mapDerivedCategoryCompIso (C n) (R n).functor).app (L n).obj ≪≫
          Classical.choice (e n))
  have hL (n : ℕ) : DerivedCategory.TStructure.t.plus (L n).obj := by
    obtain ⟨r, s, hrs, hv⟩ := (L n).property.2
    exact ⟨r, (DerivedCategory.isGE_iff _ r).2 fun i hi ↦ hv i (Or.inl hi)⟩
  let level (n : ℕ) : DerivedCategory.Plus
      (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
    (C n).mapDerivedCategoryPlus.obj ⟨(L n).obj, hL n⟩
  let origin (n : ℕ) : Nonempty (FixedEtaleOriginWitness W
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (level n)) :=
    ⟨⟨⟨(L n).obj, hL n⟩, Iso.refl _⟩⟩
  let evaluation (n : ℕ) : (R n).functor.mapDerivedCategory.obj (level n).obj ≅
      (coefficientSequenceDerivedEvaluation l E W n).obj M :=
    (R n).functor.mapDerivedCategory.mapIso (α n) ≪≫
      (R n).mapDerivedCategory.counitIso.app _
  let limits (n : ℕ) := normalizedDVRModuleRes_limits l E W (Nat.le_succ n)
  let colimits (n : ℕ) := normalizedDVRModuleRes_colimits l E W (Nat.le_succ n)
  let δ (n : ℕ) :=
    (Functor.mapDerivedCategorySquareIso (sfRealizationRestriction W
      (Padic.coefficientExtensionTransition l E (n + 1)))).symm.app (level n).obj ≪≫
    (Functor.mapDerivedCategoryNatIso (eqToIso (originRestrictionEquality l E W n))).app
      ((R n).functor.mapDerivedCategory.obj (level n).obj)
  let t (n : ℕ) := (evaluation (n + 1)).hom ≫
    (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app M ≫
      (normalizedDVRRes l E W (Nat.le_succ n)).map (evaluation n).inv
  let fixed (n : ℕ) := (R (n + 1)).functor.mapDerivedCategory.preimage
    (t n ≫ (δ n).inv)
  have fixed_eq (n : ℕ) : (R (n + 1)).functor.mapDerivedCategory.map (fixed n) ≫
      (δ n).hom = t n := by
    simp only [fixed, Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have lift (n : ℕ) : ∃ f :
      (Classical.choice (origin (n + 1))).complex.obj ⟶
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology
          (Padic.coefficientExtensionTransition l E (n + 1)).ulift).obj
            (Classical.choice (origin n)).complex.obj,
      (C (n + 1)).mapDerivedCategory.map f ≫
        (ProEtale.pbcDerivedComparisonRestrict W
          (Padic.coefficientExtensionTransition l E (n + 1)).ulift).inv.app
            (Classical.choice (origin n)).complex.obj ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology W)
          (Padic.coefficientExtensionTransition l E (n + 1)).ulift).map
            (Classical.choice (origin n)).iso.hom =
        (Classical.choice (origin (n + 1))).iso.hom ≫ fixed n := by
    let A := Classical.choice (origin (n + 1))
    let B := Classical.choice (origin n)
    let φ : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 2)) →+*
        ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) :=
      (Padic.coefficientExtensionTransition l E (n + 1)).ulift
    let S := Sheaf.restrictScalars.{u + 1} W.smallEtaleTopology φ
    have hplus : DerivedCategory.TStructure.t.plus (S.mapDerivedCategory.obj B.complex.obj) :=
      (S.mapDerivedCategoryPlus.obj B.complex).property
    let q := A.iso.hom ≫ fixed n ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology W) φ).map B.iso.inv ≫
        (ProEtale.pbcDerivedComparisonRestrict W φ).hom.app B.complex.obj
    obtain ⟨f, hf⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      A.complex.obj (S.mapDerivedCategory.obj B.complex.obj) hplus).2 q
    refine ⟨f, ?_⟩
    change (C (n + 1)).mapDerivedCategory.map f = q at hf
    change (C (n + 1)).mapDerivedCategory.map f ≫
        (ProEtale.pbcDerivedComparisonRestrict W φ).inv.app B.complex.obj ≫
          (Sheaf.derivedRestrictScalars (ProEt.topology W) φ).map B.iso.hom =
        A.iso.hom ≫ fixed n
    exact (congrArg (fun g ↦ g ≫
      (ProEtale.pbcDerivedComparisonRestrict W φ).inv.app B.complex.obj ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology W) φ).map B.iso.hom) hf).trans (by
      exact conjugate_cancel A.iso.hom (fixed n)
        ((Sheaf.derivedRestrictScalars (ProEt.topology W) φ).mapIso B.iso)
        ((ProEtale.pbcDerivedComparisonRestrict W φ).app B.complex.obj))
  choose etale hEtale using lift
  exact ⟨{
    level := level
    origin := origin
    evaluation := evaluation
    etaleTransition := etale
    fixedTransition := fixed
    originSquare := hEtale
    transitionSquare := fixed_eq }⟩

/-- Reduction of an integral constructible object has the common bounds and compatible
origins required at an input leaf. No finite-type hypothesis on the unused inputs is needed.
Source: Stacks 0941; Bhatt--Scholze 6.5.11 and 6.7.2; parent proof step 7
(blueprint: lem-sf-constructible-reduction-good).

Proof: the K-flat quotient model of the recorded reduction functor gives normalization.
Use its evaluation comparison to identify the nth level with derived tensor by A_(n+1).
Integral constructibility gives constructible cohomology and one common cohomology
interval. The residue-Tor theorem applied to its residue interval gives one common Tor
interval for all levels. Transport both intervals across the evaluation comparison.
Each finite constructible bounded reduction has an etale-origin witness by finite-ring
constructible derived origin. The normalized-origin comparison theorem lifts the actual
quotient-transition adjuncts between these bounded witnesses. Compose those lifted
adjuncts with the scalar-extension units to obtain their restriction-of-scalars maps.
Its compatibility equation identifies their images with the actual system transitions;
use these maps and the evaluated quotient model to fill originSquare and transitionSquare.
This constructs Origins for the one specified system, with its actual transitions.
Zero reductions use the zero witness and interval [0,0]; identity quotients use the
scalar unit. No equality of derived system morphisms is inferred from evaluation. -/
theorem constructibleReduction_good (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Over (Spec (CommRingCat.of D.k))) (K : Integral l E X.left)
    (hK : sfIntegralConstructible l E X.left K) :
    Good l E X.left ((calculus l E X.left).reduction.obj K) := by
  classical
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let (x : X.left) : Invertible (l : X.left.residueField x) :=
    (show IsUnit (l : X.left.residueField x) from by
      simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map
        (X.hom.residueFieldAlgebraMap x)).invertible
  have normalized : IsNormalizedCoefficientSequence l E X.left
      ((calculus l E X.left).reduction.obj K) :=
    (calculus l E X.left).reduction_normalized K
  obtain ⟨a, b, hab, hlevels⟩ := hK.2
  have tor := (integral_residue_tor D l hl E X.left).1 K hK a b hab
    (fun i hi ↦ (hlevels 0).2 hi)
  have bounds : LevelBounds l E X.left ((calculus l E X.left).reduction.obj K) := by
    refine ⟨a, b, a, b, hab, hab, fun n ↦ ?_⟩
    let e := ((calculus l E X.left).reductionEvaluation n).app K
    refine ⟨constructible_of_iso l E X.left n e (hlevels n).1, ?_, tor_of_iso e (tor n)⟩
    exact fun i hi ↦ (hlevels n).2 ((congrArg (fun S : Set ℤ ↦ i ∈ S)
      (support_of_iso e)).mp hi)
  exact ⟨normalized, bounds, origins_of_bounds l E X.left _ bounds⟩

end WeilConjectures.IntegralSystemRealization
