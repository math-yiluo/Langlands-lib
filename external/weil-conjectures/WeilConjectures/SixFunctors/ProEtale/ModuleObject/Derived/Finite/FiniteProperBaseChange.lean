/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import WeilConjectures.AlgebraicGeometry.Proper.Geometric.ProperGeometricFibreTorsionBound
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientExchangeEncoding
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientProjectionEncoding
import WeilConjectures.AlgebraicGeometry.SmoothPurity.KunnethDerivedTensorTEst
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
/-!
# Proper direct image with finite coefficients

Source: blueprint main-20261015, chap-Construction-of-f,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-finite.md
(blueprint: proposition-proper-direct-image-constructible-complexes).

All three clauses use the recorded internal-module Dctf and ordinary uncompleted
unbounded derived operations. The exchange is the mate of the composition comparison;
the projection is the right-adjoint projection map of the canonical derived tensor comparison.

## Main definitions

* `finiteProperCoefficientRing`: the sheafified constant coefficient ring.
* `finiteProperAmbientExchange`: the canonical ambient exchange mate.

## Main statements

* `finiteProperBaseChange`: preservation of Dctf, base change, and the projection formula.
-/

@[expose] public section

set_option autoImplicit false

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor CategoryTheory.MonoidalClosed

local instance finiteProperCache1 : CategoryTheory.EssentiallySmall.{u + 1} Profinite.{u} :=
  CategoryTheory.essentiallySmallSelf.{0} _

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

local instance finiteProperCache2 : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasEnrichedHom Ab.{u + 1} F G :=
  (presheaf_enrichedHoms_exist (C := Profinite.{u}) (A := Ab.{u + 1})).1
local instance finiteProperCache3 : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom Ab.{u + 1} F G :=
  (presheaf_enrichedHoms_exist (C := Profinite.{u}) (A := Ab.{u + 1})).2
local instance finiteProperCache4 :
    ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal

local instance finiteProperCache5 (T : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

local instance finiteProperCache6 (T : AlgebraicGeometry.Scheme.{u}) :
    ∀ (F G : T.ProEtᵒᵖ ⥤ Ab.{u + 1}),
      Enriched.FunctorCategory.HasEnrichedHom Ab.{u + 1} F G :=
  (presheaf_enrichedHoms_exist (C := T.ProEt) (A := Ab.{u + 1})).1
local instance finiteProperCache7 (T : AlgebraicGeometry.Scheme.{u}) :
    ∀ (F G : T.ProEtᵒᵖ ⥤ Ab.{u + 1}),
      Enriched.FunctorCategory.HasFunctorEnrichedHom Ab.{u + 1} F G :=
  (presheaf_enrichedHoms_exist (C := T.ProEt) (A := Ab.{u + 1})).2
local instance finiteProperCache8 (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal

noncomputable local instance finiteProperCache9 (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory _ _
noncomputable local instance finiteProperCache10 (T : AlgebraicGeometry.Scheme.{u}) :
    SymmetricCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.symmetricCategory _ _
noncomputable local instance finiteProperCache11 :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.monoidalCategory _ _
noncomputable local instance finiteProperCache12 :
    SymmetricCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.symmetricCategory _ _

noncomputable local instance cachedModuleMonoidal (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    MonoidalCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  Mod.monoidalCategory

noncomputable local instance cachedModuleBraided (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    BraidedCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  Mod.braidedCategory

noncomputable local instance cachedModuleSymmetric (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    SymmetricCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  Mod.symmetricCategory

noncomputable local instance cachedDerivedMonoidal (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    MonoidalCategory (DerivedCategory
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)) :=
  inferInstance

noncomputable local instance cachedModuleClosed (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    MonoidalClosed (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  Mod.monoidalClosed

local instance cachedModuleFlatResolution (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  Mod.hasFunctorialFlatResolution

local instance cachedDerivedTensorStructure (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (DerivedCategory.Qh (C := Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)).HasDerivedMonoidalCategory
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The sheafified constant commutative coefficient ring on the profinite point.
This bundles the existing `Sheaf.sheafifyRingPresheaf` construction, so the finite ring
may have the same arbitrary universe as the schemes, with no topology parameters.
Source: blueprint sk-thm-sfb-proper-base-change-finite, finite discrete coefficients,
and Bhatt--Scholze Section 5.3 (blueprint:
proposition-proper-direct-image-constructible-complexes). -/
noncomputable def finiteProperCoefficientRing (A : Type u) [CommRing A] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  letI : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  let P : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} :=
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A))
  letI := P.isCommMonObj_compForget₂
    (fun _ a b ↦ @mul_comm (ULift.{u + 1, u} A) _ a b)
  exact
    { X := Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
        (coherentTopology Profinite.{u}) P }

noncomputable local instance finiteProperCoefficientMon (A : Type u) [CommRing A] :
    MonObj (finiteProperCoefficientRing A).X := (finiteProperCoefficientRing A).mon
local instance finiteProperCoefficientComm (A : Type u) [CommRing A] :
    IsCommMonObj (finiteProperCoefficientRing A).X := (finiteProperCoefficientRing A).comm

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Elaborating the two composed derived pullbacks unfolds their module scalar transports.
/-- The canonical ambient exchange for internal condensed-coefficient modules.
Source: blueprint sk-thm-sfb-proper-base-change-finite, clause (2), and the
unit/square/counit construction in sk-def-sfb-base-change-morphism
(blueprint: proposition-proper-direct-image-constructible-complexes). -/
noncomputable abbrev finiteProperAmbientExchange := @finiteProperExchange.{u}

attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem finiteProperCoefficientRing_iso
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (finiteProperCoefficientRing A).X ≅
      Mon.mk (FiniteDiscreteOrdinary.coefficient A)) := by
  let J := coherentTopology Profinite.{u}
  let φ := FiniteDiscreteOrdinary.pointConstants A
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff _).mp hφ
  let e := asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso J (Profinite.continuousCoefficientRingSheaf A)
  have he : IsMonHom e.hom := by
    change IsMonHom ((presheafToSheaf J Ab.{u + 1}).map
      (Functor.whiskerRight (FiniteDiscreteOrdinary.pointRingConstants A)
        (forget₂ RingCat Ab)) ≫
      (Sheaf.sheafifyRingPresheafIso J (Profinite.continuousCoefficientRingSheaf A)).hom)
    infer_instance
  exact ⟨Mon.mkIso' e⟩

-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem continuous_finiteProper_preserves
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left]
    (K : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) X.left) :
    (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y.left ⊓
      DerivedCategory.finiteTorAmplitude _)
        ((lowerStar (FiniteDiscreteOrdinary.coefficient A) p.left).rightDerivedFunctor.obj
          K.obj) := by
  classical
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists A T).some
  obtain ⟨hreal, hpush⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization
    ℓ (ringChar k) k ((Fact.out : (ringChar k).Prime).pos) Fact.out A E
  obtain ⟨a, b, hK⟩ := K.property.2
  let a' := min a b
  have hab : a' ≤ b := min_le_right _ _
  have hK' : DerivedCategory.torAmplitudeIn _ a' b K.obj :=
    hK.mono (min_le_left _ _) le_rfl
  obtain ⟨eX, ⟨heX⟩⟩ := hreal X a' b hab
  let C := eX.inverse.obj ⟨K.obj, K.property.1, hK'⟩
  let eC : (FiniteDiscreteOrdinary.internalEtaleRealization A X.left (E X.left)).obj
      C.obj ≅ K.obj :=
    (heX.app C).symm ≪≫ (ObjectProperty.ι _).mapIso
      (eX.counitIso.app ⟨K.obj, K.property.1, hK'⟩)
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have hxsep : IsSeparated (X.left ↘ Spec (.of k)) :=
    show IsSeparated X.hom from inferInstance
  have hysep : IsSeparated (Y.left ↘ Spec (.of k)) :=
    show IsSeparated Y.hom from inferInstance
  have hxlft : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    show LocallyOfFiniteType X.hom from inferInstance
  have hylft : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    show LocallyOfFiniteType Y.hom from inferInstance
  have hxqc : QuasiCompact (X.left ↘ Spec (.of k)) :=
    show QuasiCompact X.hom from inferInstance
  have hyqc : QuasiCompact (Y.left ↘ Spec (.of k)) :=
    show QuasiCompact Y.hom from inferInstance
  have : p.left.IsOver (Spec (.of k)) := ⟨p.w⟩
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  obtain ⟨d, hd⟩ := exists_proper_geometricFibre_torsion_cohomology_bound p.left
  have hd' : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y.left)
      (F : Sheaf (pullback p.left y).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (U : (pullback p.left y).Etale) (s : F.obj.obj (Opposite.op U)),
        ∃ n : ℕ, (ℓ ^ n) • s = 0) →
      ∀ i : ℤ, (d : ℤ) < i →
        IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback p.left y) i).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    intro Ω _ _ y F hF i hi
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    apply hd Ω y F _ i hi
    intro U s
    obtain ⟨n, hn⟩ := hF U.unop s
    exact ⟨(ℓ ^ n : ℕ), by exact_mod_cast pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero,
      by simpa only [natCast_zsmul] using hn⟩
  have hA' : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : ULift.{u + 1} A) = 0 := by
    obtain ⟨r, hr⟩ := hA
    refine ⟨r + 1, by omega, ?_⟩
    apply ULift.ext
    change (ℓ ^ (r + 1) : ℕ) • (1 : A) = 0
    have hr' : (ℓ : A) ^ r = 0 := by
      simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hr
    simp only [nsmul_eq_mul, mul_one, Nat.cast_pow, pow_succ, Nat.cast_mul, hr', zero_mul]
  obtain ⟨hD, hDt⟩ :=
    Etale.isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper
      ℓ (ringChar k) Fact.out (Fact.out : (ringChar k).Prime).pos Fact.out k p.left
      (ULift.{u + 1} A)
      hA' d hd' a' b hab C.obj C.property.1 C.property.2
  obtain ⟨eY, ⟨heY⟩⟩ := hreal Y a' (b + (d : ℤ)) (by omega)
  let D := eY.functor.obj ⟨_, hD, hDt⟩
  have hplus : ∃ n : ℤ, C.obj.IsGE n := by
    obtain ⟨a, b, hc⟩ := C.property.1.2
    exact ⟨a, (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hc.2 i (Or.inl hi)⟩
  obtain ⟨hp⟩ := hpush X Y p
  let ep := (heY.app ⟨_, hD, hDt⟩) ≪≫ hp.app ⟨C.obj, hplus⟩ ≪≫
    ((lowerStar (FiniteDiscreteOrdinary.coefficient A) p.left).rightDerivedFunctor).mapIso eC
  have : (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A)
      Y.left).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined
      (FiniteDiscreteOrdinary.coefficient A) Y.left).2.1
  exact ⟨ObjectProperty.prop_of_iso _ ep D.property.1,
    ObjectProperty.prop_of_iso _ ep ⟨a', b + (d : ℤ), D.property.2⟩⟩

-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem preserves_coefficientIso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ∀ K : ConstantModelConstructibleFiniteTor S X,
      (constantModelBoundedConstructible S Y ⊓ DerivedCategory.finiteTorAmplitude _)
        ((lowerStar S p).rightDerivedFunctor.obj K.obj))
    (K : ConstantModelConstructibleFiniteTor R X) :
    (constantModelBoundedConstructible R Y ⊓ DerivedCategory.finiteTorAmplitude _)
      ((lowerStar R p).rightDerivedFunctor.obj K.obj) := by
  have : IsIso e.inv.hom := by
    change IsIso ((Mon.forget _).map e.inv)
    infer_instance
  let T (Z : Scheme.{u}) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap e.inv.hom Z)).mapDerivedCategory
  let U (Z : Scheme.{u}) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap e.hom.hom Z)).mapDerivedCategory
  have hflat (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom Z)) := by
    have : IsIso (coefficientMap e.inv.hom Z) := by dsimp [coefficientMap]; infer_instance
    exact preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoComapInv (coefficientMap e.inv.hom Z)).symm
  let ep := (derivedComapLowerStarIso e.inv.hom p).app K.obj
  have hD := h ⟨(T X).obj K.obj, constantModelCtf_coefficientIso e X K⟩
  have : (constantModelBoundedConstructible S Y).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined S Y).2.1
  have hT : (constantModelBoundedConstructible S Y ⊓ DerivedCategory.finiteTorAmplitude _)
      ((T Y).obj ((lowerStar R p).rightDerivedFunctor.obj K.obj)) :=
    ObjectProperty.prop_of_iso _ ep.symm hD
  have hU := constantModelCtf_coefficientIso e.symm Y ⟨_, hT⟩
  let ec : T Y ⋙ U Y ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso _ _) ≪≫
      Functor.mapDerivedCategoryNatIso
        ((Mod.comapComp _ _).symm ≪≫ Mod.comapCongr (by
          change (upperStarFromPoint Y).map e.hom.hom ≫
            (upperStarFromPoint Y).map e.inv.hom = 𝟙 _
          rw [← Functor.map_comp]
          change (upperStarFromPoint Y).map ((Mon.forget _).map (e.hom ≫ e.inv)) = _
          simp only [Iso.hom_inv_id]
          exact (upperStarFromPoint Y).map_id R) ≪≫ Mod.comapId _) ≪≫
      Functor.mapDerivedCategoryIdIso _
  have : (constantModelBoundedConstructible R Y).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined R Y).2.1
  exact ObjectProperty.prop_of_iso _ (ec.app _) hU
-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem isIso_app_app_of_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {F G : C ⥤ D ⥤ H} (τ : F ⟶ G)
    {K K' : C} (eK : K ≅ K') {M M' : D} (eM : M ≅ M')
    [IsIso ((τ.app K).app M)] : IsIso ((τ.app K').app M') := by
  let t := Functor.whiskerRight τ ((evaluation D H).obj M)
  have ht : IsIso ((τ.app K').app M) :=
    (NatTrans.isIso_app_iff_of_iso t eK).1
      (show IsIso ((τ.app K).app M) from inferInstance)
  exact (NatTrans.isIso_app_iff_of_iso (τ.app K') eM).1 ht

-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem ordinary_projection_of_etale_tor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (C : Etale.DerivedCategoryModule A X) (D : Etale.DerivedCategoryModule A Y)
    (hC : Etale.DerivedCategory.isBoundedConstructible A X C)
    (hD : Etale.DerivedCategory.isBoundedConstructible A Y D)
    (a b : ℤ) (hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b C) :
    ordinaryFiniteCoefficientProjectionIsIso A p
      (((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj C)
      (((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj D) := by
  refine (ordinaryFiniteCoefficientProjectionIsIso_iff A p _ _).2 ?_
  obtain ⟨c, d, hc⟩ := hC.2
  have hCplus : ∃ n : ℤ, C.IsGE n :=
    ⟨c, (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hc.2 i (Or.inl hi)⟩
  obtain ⟨e, f, hd⟩ := hD.2
  have : D.IsGE e :=
    (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hd.2 i (Or.inl hi)
  have hDMap : ((Etale.upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj D).IsGE e :=
    Functor.isGE_mapDerivedCategory_obj _ D e
  have hPull : ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj D).IsGE e :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctorIsoMapDerivedCategory).app
        D).symm e
  have hTensor : ∃ n : ℤ,
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj C).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj D)).IsGE n := by
    refine ⟨a + e, (DerivedCategory.isGE_iff _ _).2 ?_⟩
    exact Etale.derivedTensor_isZero_homology_of_torAmplitudeGE A X C _ a e
      (fun M i hi ↦ hTor M i (Or.inl hi))
      ((DerivedCategory.isGE_iff _ _).1 hPull)
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) p).app C).app D) :=
    Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
      A isAddTorsion_of_finite p C D
  have := ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived
    (ModuleCat.{u + 1} A) p C D hCplus hTensor
  exact isIso_app_app_of_iso
    (ProEtale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p)
    (((comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory).app
      C)
    (((comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory).app
      D)

-- Specialize naturality before substituting the coefficient-encoding categories.
private theorem ordinary_projection_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (C : Etale.DerivedCategoryModule A X) (D : Etale.DerivedCategoryModule A Y)
    (hC : Etale.DerivedCategory.isBoundedConstructible A X C)
    (hD : Etale.DerivedCategory.isBoundedConstructible A Y D)
    (a b : ℤ) (hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b C)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (eK : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj C ≅ K)
    (eM : (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj D ≅ M) :
    ordinaryFiniteCoefficientProjectionIsIso A p K M := by
  exact ordinaryFiniteCoefficientProjectionIsIso_of_iso A p eK eM
    (ordinary_projection_of_etale_tor A p C D hC hD a b hTor)

private abbrev EncodedEtaleOrigin
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [IsTopologicalRing A]
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R]
    (e : Mon.mk R ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (T : Scheme.{u})
    (K : ConstantModelConstructibleFiniteTor R T) :=
  Σ (C : Etale.DerivedCategoryModule (ULift.{u + 1} A) T), Σ a b : ℤ,
    { _eC : ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
        T).mapDerivedCategory).obj C ≅
          (FiniteDiscreteOrdinary.coefficientEncoding A e T (E T)).obj K.obj //
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T C ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b C }

-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem coefficientEncoding_etaleOrigin
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R]
    (e : Mon.mk R ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (K : ConstantModelConstructibleFiniteTor R T.left) :
    Nonempty (EncodedEtaleOrigin A e E T.left K) := by
  let L : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) T.left :=
    ⟨_, constantModelCtf_coefficientIso e T.left K⟩
  obtain ⟨a, b, hL⟩ := L.property.2
  let a' := min a b
  have hL' : DerivedCategory.torAmplitudeIn _ a' b L.obj :=
    hL.mono (min_le_left _ _) le_rfl
  obtain ⟨hreal, _⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization
    ℓ (ringChar k) k ((Fact.out : (ringChar k).Prime).pos) Fact.out A E
  obtain ⟨eT, ⟨heT⟩⟩ := hreal T a' b (min_le_right _ _)
  let C := eT.inverse.obj ⟨L.obj, L.property.1, hL'⟩
  let ec : (FiniteDiscreteOrdinary.internalEtaleRealization A T.left (E T.left)).obj
      C.obj ≅ L.obj :=
    (heT.app C).symm ≪≫ (ObjectProperty.ι _).mapIso
      (eT.counitIso.app ⟨L.obj, L.property.1, hL'⟩)
  refine ⟨⟨C.obj, a', b, ?_, C.property.1, C.property.2⟩⟩
  exact ((E T.left).fixedDerived.counitIso.app _).symm ≪≫
    (E T.left).fixedDerived.functor.mapIso ec

-- Compare the fixed derived functors without unfolding their resolving constructions.
private theorem ordinary_exchange_of_etale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} [IsProper p]
    (sq : ChosenCartesianSquare g' p' p g)
    (C : Etale.DerivedCategoryModule A X)
    (hC : Etale.DerivedCategory.isBoundedConstructible A X C) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj C)) := by
  obtain ⟨c, d, hc⟩ := hC.2
  have hplus : ∃ n : ℤ, C.IsGE n :=
    ⟨c, (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hc.2 i (Or.inl hi)⟩
  have hp : IsPullback g' p' p g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  exact ProEtale.isIso_derivedBaseChangeMap_app_of_isProper A hp _
    ⟨C, hplus, ⟨Iso.refl _⟩⟩

attribute [local irreducible] FiniteDiscreteOrdinary.coefficientEncoding
  FiniteDiscreteOrdinary.Encoding.fixedDerived ProEtale.derivedBaseChangeMap
  ProEtale.rightDerivedLowerStarProjectionMap finiteCoefficientProjectionIsIso
  ordinaryFiniteCoefficientProjectionIsIso

-- Transport only between the named ordinary and internal projection arrows.
private theorem projection_of_encoded_origins
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (K : ConstantModelConstructibleFiniteTor Λ X)
    (M : ConstantModelConstructibleFiniteTor Λ Y)
    (origin : EncodedEtaleOrigin A e E X K)
    (originD : EncodedEtaleOrigin A e E Y M) :
    finiteCoefficientProjectionIsIso Λ p K.obj M.obj := by
  apply (FiniteDiscreteOrdinary.finiteCoefficientProjectionEncoding A e E
    p K.obj M.obj).2
  exact ordinary_projection_transport (ULift.{u + 1} A) p
    origin.1 originD.1 origin.2.2.2.property.1 originD.2.2.2.property.1
    origin.2.1 origin.2.2.1 origin.2.2.2.property.2 _ _ origin.2.2.2.val originD.2.2.2.val

set_option maxHeartbeats 40000 in
-- The canonical-arrow comparisons retain large derived-module instance terms.
private theorem finiteProperBaseChange_of_coefficientIso
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar Λ p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
      IsIso ((finiteProperExchange Λ
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
      (M : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso (moduleObjectProjectionMap Λ p.left K.obj M.obj)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact preserves_coefficientIso e p.left
      (continuous_finiteProper_preserves A ℓ _hA k X Y p)
  · intro X' Y' g p' g' sq K
    let origin := (coefficientEncoding_etaleOrigin (R := Λ) A ℓ k e E X K).some
    let α := ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A)) sq.toCommSq
    have hα : IsIso (α.app
        ((FiniteDiscreteOrdinary.coefficientEncoding A e X.left (E X.left)).obj K.obj)) :=
      (NatTrans.isIso_app_iff_of_iso α origin.2.2.2.val).1
        (ordinary_exchange_of_etale (ULift.{u + 1} A) sq origin.1 origin.2.2.2.property.1)
    exact (FiniteDiscreteOrdinary.finiteCoefficientExchangeEncoding_isIso A e E sq K.obj).2 hα
  · intro K M
    unfold moduleObjectProjectionMap moduleObjectProjectionData derivedTensor
    let origin := (coefficientEncoding_etaleOrigin (R := Λ) A ℓ k e E X K).some
    let originD := (coefficientEncoding_etaleOrigin (R := Λ) A ℓ k e E Y M).some
    exact (finiteCoefficientProjectionIsIso_iff Λ p.left K.obj M.obj).1
      (projection_of_encoded_origins Λ A e E p.left K M origin originD)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 20000 in
-- Use the canonical comparison API without unfolding its arrow data.
/-- Proper direct image preserves Dctf, and its canonical exchange and projection arrows
are invertible, in the ordinary unbounded derived category of internal modules.
Source: blueprint main-20261015, proposition-proper-direct-image-constructible-complexes, clauses
(1)--(3) (blueprint: proposition-proper-direct-image-constructible-complexes).

Proof:
1. The sheafified constant coefficient ring is isomorphic, as a ring object, to the
continuous finite coefficient ring: the constant-functions map is locally bijective, so
sheafification inverts it, and it is multiplicative
(proposition-proper-direct-image-constructible-complexes). Scalar restriction along the inverse
isomorphism is an exact equivalence, and it transports finite constant models and finite Tor
amplitude (proposition-proper-direct-image-constructible-complexes). Fix normalized encodings of the
continuous coefficients on every scheme.
2. Enlarge an internal Tor interval to [min a b, b]. The finite internal/etale realization
(proposition-proper-direct-image-constructible-complexes) gives a bounded constructible etale
antecedent C with this interval, its comparison isomorphism, and the comparison of the
total proper direct images on bounded-below inputs.
3. Clause (1). The proper geometric-fibre torsion bound gives d for sectionwise
ell-power-torsion sheaves on every geometric fibre. Replace the exponent killing 1 by r+1,
positive also for the zero ring. proposition-proper-direct-image-finite-coefficients--1 gives
bounded constructibility and Tor interval [a, b+d] for the etale direct image of C. The realization
over Y, the direct-image comparison and repleteness
(proposition-proper-direct-image-constructible-complexes) transport both properties to the
continuous coefficients, then along the ring isomorphism of step 1.
4. Clause (2). The encoded K has the etale origin C of step 2, bounded below. The
fixed-scalar proper exchange theorem (proposition-proper-direct-image-constructible-complexes)
makes the ordinary exchange at its comparison image invertible, for arbitrary g; naturality
moves it to the encoded K. The exchange encoding
(proposition-proper-direct-image-constructible-complexes) and reflection of isomorphisms by the
encoding equivalence give invertibility of the internal exchange
(proposition-proper-direct-image-constructible-complexes).
5. Clause (3). Take etale antecedents C, D of K, M. Exact etale pullback keeps a lower bound e
of D; Tor connectivity (proposition-proper-direct-image-constructible-complexes) bounds C tensor^L
p*D below by a+e. Finite A is additively torsion, so the etale projection map is invertible
(proposition-proper-direct-image-constructible-complexes--9). The fixed-scalar projection transport
(proposition-proper-direct-image-constructible-complexes) carries this to the ordinary pro-etale
projection map; naturality transports it along both antecedent isomorphisms. The projection encoding
(proposition-proper-direct-image-constructible-complexes) gives invertibility of the internal
right-adjoint projection map.
-/
theorem finiteProperBaseChange
    (A : Type u) [CommRing A] [Finite A]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X X.left,
      (constantModelBoundedConstructible (finiteProperCoefficientRing A).X Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar (finiteProperCoefficientRing A).X p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X X.left),
      IsIso ((finiteProperAmbientExchange (finiteProperCoefficientRing A).X
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X X.left)
      (M : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X Y.left),
      IsIso ((((derivedUpperStarLowerStarAdjunction (finiteProperCoefficientRing A).X
        p.left).rightAdjointProjectionMap
          (leftDerivedUpperStarTensor (finiteProperCoefficientRing A).X p.left)).app K.obj).app
            M.obj)) := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let e := Classical.choice (finiteProperCoefficientRing_iso A)
  let E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T :=
    fun T ↦ (FiniteDiscreteOrdinary.encoding_exists A T).some
  have h := finiteProperBaseChange_of_coefficientIso (finiteProperCoefficientRing A).X
    A e E ℓ _hA k X Y p
  unfold moduleObjectProjectionMap moduleObjectProjectionData derivedTensor at h
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
