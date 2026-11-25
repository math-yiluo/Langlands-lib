/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.PurReductionLimitShiftData
public import WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts
public import Mathlib.CategoryTheory.Shift.Adjunction
import all WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteTensorMonoidal
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Finite models of the adjoint coefficient shift

Source: Stacks 06YY, 07A6 and 0941; current blueprint
`sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientFiniteReductionModel coefficientLocalizedCounitModel

-- Recover the evaluation from its normalized mate under two shift-compatible adjunctions.
private theorem evaluation_shift
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (L : A ⥤ B) (R : B ⥤ A) (F : A ⥤ C) (G : C ⥤ A) (V : B ⥤ C)
    [L.CommShift ℤ] [R.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    [V.CommShift ℤ] (a : L ⊣ R) (b : F ⊣ G) [a.CommShift ℤ] [b.CommShift ℤ]
    (e : L ⋙ V ≅ F) (π : R ⟶ V ⋙ G) [NatTrans.CommShift π ℤ]
    (h : ∀ N, b.homEquiv _ _ (e.inv.app (R.obj N) ≫ V.map (a.counit.app N)) =
      π.app N) : NatTrans.CommShift e.hom ℤ := by
  let β : TwoSquare R V (𝟭 A) G :=
    .mk _ _ _ _ (R.rightUnitor.hom ≫ π)
  let α := ((mateEquiv a b).symm β)
  have hα : NatTrans.CommShift α ℤ := by
    dsimp only [α, mateEquiv, Equiv.coe_fn_symm_mk, β]
    infer_instance
  let τ : TwoSquare (𝟭 A) L F V :=
    .mk _ _ _ _ (F.leftUnitor.hom ≫ e.inv)
  have hm : mateEquiv a b τ = β := by
    ext N
    simpa [mateEquiv, τ, β, Adjunction.homEquiv_unit, Functor.map_comp,
      Category.assoc] using h N
  have heq : (mateEquiv a b).symm β = τ := by
    rw [← hm]
    exact (mateEquiv a b).symm_apply_apply τ
  have : NatTrans.CommShift τ ℤ := by
    rw [← heq]
    exact hα
  have he : e.inv = F.leftUnitor.inv ≫ τ := by simp [τ]
  have : NatTrans.CommShift e.inv ℤ := by rw [he]; infer_instance
  have : NatTrans.CommShift e.symm.hom ℤ := ‹NatTrans.CommShift e.inv ℤ›
  exact NatTrans.CommShift.of_iso_inv e.symm ℤ

-- Naturality extends a unit normalization from resolving representatives to all complexes.
private theorem normalized_shift_of_resolutions
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (L : DerivedCategory A ⥤ DerivedCategory B) [L.CommShift ℤ]
    (α : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsRightKanExtension α] [NatTrans.CommShift α ℤ]
    (adj : L ⊣ G.mapDerivedCategory) (P : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ, ∃ (Q : CochainComplex A ℤ) (s : Q ⟶ K),
      P Q ∧ QuasiIso s)
    (norm : ∀ Q : CochainComplex A ℤ, P Q →
      adj.unit.app (DerivedCategory.Q.obj Q) ≫ G.mapDerivedCategory.map (α.app Q) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
          G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj Q)) :
    adj.CommShift ℤ := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let β := G.mapDerivedCategoryFactors.inv
  let δ := Functor.whiskerLeft DerivedCategory.Q adj.unit ≫
    (Functor.associator DerivedCategory.Q L G.mapDerivedCategory).inv ≫
      Functor.whiskerRight α G.mapDerivedCategory
  let ζ := (Functor.rightUnitor DerivedCategory.Q).hom ≫
    (Functor.leftUnitor DerivedCategory.Q).inv ≫
    Functor.whiskerRight (a.mapHomologicalComplex (.up ℤ)).unit DerivedCategory.Q ≫
    (Functor.associator Fc Gc DerivedCategory.Q).hom ≫
    Functor.whiskerLeft Fc β ≫ (Functor.associator Fc DerivedCategory.Q G.mapDerivedCategory).inv
  have he : δ = ζ := by
    apply NatTrans.ext
    funext K
    obtain ⟨Q, s, hQ, hs⟩ := res K
    have : QuasiIso s := hs
    have : IsIso (DerivedCategory.Q.map s) := inferInstance
    apply (cancel_epi (DerivedCategory.Q.map s)).mp
    change DerivedCategory.Q.map s ≫ δ.app K = DerivedCategory.Q.map s ≫ ζ.app K
    have hd := δ.naturality s
    have hz := ζ.naturality s
    dsimp only [Functor.comp_map, Functor.id_map] at hd hz
    rw [hd, hz]
    have hq : δ.app Q = ζ.app Q := by
      simpa [δ, ζ, Fc, Gc, β] using norm Q hQ
    rw [hq]
  have hn (Q : CochainComplex A ℤ) :
      adj.unit.app (DerivedCategory.Q.obj Q) ≫ G.mapDerivedCategory.map (α.app Q) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
          β.app (Fc.obj Q) := by
    simpa [δ, ζ, Fc, Gc] using NatTrans.congr_app he Q
  exact Adjunction.CommShift.mk' adj ℤ
    (CategoryTheory.normalized_unit_commShift DerivedCategory.Q DerivedCategory.Q Fc Gc
      L G.mapDerivedCategory (a.mapHomologicalComplex (.up ℤ)) adj α β hn)

-- The homotopy and cochain localization factors have the same components.
private theorem factorsh_app
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (I : CochainComplex A ℤ) :
    G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) =
      G.mapDerivedCategoryFactors.hom.app I := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change G.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  simp only [G.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.id_comp,
    Category.comp_id]

-- The K-injective normalization forces the projection to respect the canonical derived shifts.
private theorem projection_shift
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G)
    (π : F.rightDerivedFunctor ⟶ G.mapDerivedCategory)
    (norm : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      π.app (DerivedCategory.Q.obj I) ≫ G.mapDerivedCategoryFactors.hom.app I =
        (F.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I)) :
    NatTrans.CommShift π ℤ := by
  let β := Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ))
    DerivedCategory.Qh ≫ G.mapDerivedCategoryFactorsh.inv
  let δ := F.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh π
  have hI (I : CochainComplex A ℤ) [I.IsKInjective] :
      δ.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) =
        β.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) := by
    have hu : F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
        (F.rightDerivedFunctorObjQIso I).hom = 𝟙 _ := by
      dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, asIso_inv, Iso.app]
      change _ ≫ (F.rightDerivedFunctor.map (𝟙 _) ≫ inv _ ≫ 𝟙 _) = _
      rw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id,
        IsIso.hom_inv_id]
    apply (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I))).mp
    dsimp only [δ, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_app, Category.comp_id, factorsh_app G I]
    erw [norm I, ← Category.assoc, hu, Category.id_comp]
    have ht := DerivedCategory.quotientCompQhIso_hom_naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I)
    have hq (K : CochainComplex B ℤ) :
        (DerivedCategory.quotientCompQhIso B).hom.app K = 𝟙 _ := rfl
    erw [hq, hq, Category.comp_id, Category.id_comp] at ht
    exact ht
  have he : δ = β := by
    apply NatTrans.ext
    funext X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨I, hI', s, _, hs⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective K
    let : I.IsKInjective := hI'
    let : QuasiIso s := hs
    let f := (HomotopyCategory.quotient A (.up ℤ)).map s
    have : IsIso (DerivedCategory.Qh.map f) := by
      exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ)) f
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs)
    have : IsIso ((DerivedCategory.Qh ⋙ G.mapDerivedCategory).map f) := by
      dsimp only [Functor.comp_map]; infer_instance
    apply (cancel_mono ((DerivedCategory.Qh ⋙ G.mapDerivedCategory).map f)).mp
    rw [← δ.naturality, ← β.naturality, hI I]
  have : NatTrans.CommShift δ ℤ := by rw [he]; dsimp only [β]; infer_instance
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal)
        F.rightDerivedFunctorUnit) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ ?_)
    obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp
    infer_instance
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh F.rightDerivedFunctorUnit π

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
  comp_preservesFiniteLimits comp_preservesFiniteColimits

@[instance_reducible] private def finiteRestrictionCommShift (n : ℕ) :
    (coefficientFiniteDerivedRestriction l E W n).CommShift ℤ := by
  unfold coefficientFiniteDerivedRestriction scalarReductionDerivedRestriction
  infer_instance

private theorem finiteCochainModelAdditive (n : ℕ) :
    (finiteCochainModel l E W n).E.Additive := (finiteCochainModel l E W n).additive

attribute [local instance] finiteRestrictionCommShift finiteCochainModelAdditive

-- Normalize the independently presented coefficient categories in the recorded unit equation.
private theorem finite_adj_shift (n : ℕ)
    (s : (coefficientFiniteDerivedExtension l E W n).CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift (finiteCochainModel l E W n).ε ℤ) :
    letI := s
    (coefficientFiniteAdjunction l E W n).CommShift ℤ := by
  let := s
  have : NatTrans.CommShift (finiteCochainModel l E W n).ε ℤ := hs
  have : (coefficientFiniteDerivedExtension l E W n).IsRightKanExtension
      (finiteCochainModel l E W n).ε :=
    (finiteCochainModel l E W n).universal.isRightKanExtension
  let : (scalarReductionExtension l E W n).Additive :=
    coefficientFiniteExtensionAdditive l E W n
  let R := scalarReductionRestriction l E W n
  have : PreservesFiniteLimits R := (scalarReductionRestriction_exact l E W n).1
  have : PreservesFiniteColimits R := (scalarReductionRestriction_exact l E W n).2
  let : EssentiallySmall.{max u (t+1)} W.ProEt := scalarReductionSiteSmall.{t, u} W
  let : HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t+1)} :=
    integralCoefficientAbSheafify W
  let : (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{max u (t+1)} :=
    integralCoefficientAbLocallyBijective W
  refine normalized_shift_of_resolutions (scalarReductionExtension l E W n) R
    (scalarReductionExtension_adjunction l E W n).choose
    (coefficientFiniteDerivedExtension l E W n) (finiteCochainModel l E W n).ε
    (coefficientFiniteAdjunction l E W n)
    (fun Q ↦ CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) Q) ?_ ?_
  · intro K
    obtain ⟨Q, f, hQ, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E W) K
    exact ⟨Q, f, hQ, hf⟩
  · intro Q hQ
    apply (Iso.eq_comp_inv (R.mapDerivedCategoryFactors.app _)).2
    have hu := CompletionUnit.finiteModel_unit l E W Q hQ n
    -- Normalize the named model instead of searching inside the expanded cochain counit.
    simp only [← finiteCochainModel_counit l E W n Q hQ] at hu
    with_unfolding_all exact (Category.assoc _ _ _).trans hu

-- Assemble the actual sequence projection from exact restriction and the derived limit.
private theorem sequence_projection_shift (n : ℕ) :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    NatTrans.CommShift (coefficientSequenceProjection l E W n) ℤ := by
  let := SequenceKInjectiveComparison.totalLimitCommShift l E W
  let R := scalarReductionRestriction l E W n
  have : PreservesFiniteLimits R := (scalarReductionRestriction_exact l E W n).1
  have : PreservesFiniteColimits R := (scalarReductionRestriction_exact l E W n).2
  let : (coefficientFiniteDerivedRestriction l E W n).CommShift ℤ :=
    inferInstanceAs (R.mapDerivedCategory.CommShift ℤ)
  let : (coefficientConstantTowerLimit l E W).CommShift ℤ :=
    inferInstanceAs ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctor.CommShift ℤ)
  let : (coefficientConstantTowerEvaluation l E W n).CommShift ℤ :=
    inferInstanceAs
      (((((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategory).CommShift
        ℤ))
  have : NatTrans.CommShift (coefficientConstantTowerProjection l E W n) ℤ :=
    projection_shift
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)) (lim.π (op n))
      (coefficientConstantTowerProjection l E W n)
      (coefficientConstantTowerProjection_exists l E W n).choose_spec.1
  have : NatTrans.CommShift (coefficientRestrictedEvaluationIso l E W n).hom ℤ := by
    dsimp only [coefficientRestrictedEvaluationIso]
    simp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  dsimp only [coefficientSequenceProjection]
  infer_instance

-- Unfold coefficient-category aliases when identifying the two forms of the finite shift square.
/-- The shift of reduction adjoint to the canonical total-limit shift agrees with
all finite K-flat scalar-extension models and the supplied evaluation isomorphisms.
Source: Stacks 06YY (derived tensor), 07A6 (derived adjunction), and 0941;
current blueprint coefficient-comparison sentence
(blueprint: lem-pur-reduction-finite-shift-normalization).

Proof: transport coherent shifts through the universal finite cochain counit.
On K-flat complexes it is exactly coefficientFiniteReductionModel, so its shift
square is the displayed model equation. The recorded finite scalar unit equation
holds on K-flat complexes; K-flat resolutions and naturality extend it to every
complex. The normalized-unit right Kan argument then makes the actual finite
scalar adjunction commute with these shifts.

For a derived projection from a right-derived functor to an exact evaluation,
its K-injective normalization identifies its composite with the derived unit
with the localized ordinary projection. K-injective resolutions extend this
identity to all homotopy objects. The canonical derived unit commutes with shifts
and is invertible on K-injectives, so the projection commutes with shifts.
Apply this to tower limit and evaluation, then compose with exact sequence
restriction and its canonical evaluation comparison. The result is the shift
square for the actual coefficientSequenceProjection and totalLimitCommShift.

The equation S.counit_projection identifies that projection with the mate of the
inverse reductionEvaluation under the total and finite scalar adjunctions. Both
adjunctions commute with shifts, so inverse mates and hence reductionEvaluation
commute with shifts. No faithfulness of derived evaluation is used. Coherent
integer shifts include zero, negative and repeated shifts, zero complexes and
the empty scheme. No finite-field, finite-type, completeness or exact-product
hypothesis is required. -/
theorem purReductionFiniteShiftNormalization
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S) :
    letI := SequenceKInjectiveComparison.totalLimitCommShift l E W
    letI := S.adjunction.leftAdjointCommShift ℤ
    ∃ finite_reduction_shift :
        ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ,
      (∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (hQr : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q⟦r⟧)),
      letI := finite_reduction_shift n
      (coefficientFiniteDerivedExtension l E W n).map
          ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
        ((coefficientFiniteDerivedExtension l E W n).commShiftIso r).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
      (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
        DerivedCategory.Q.map
          ((((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso r).hom.app Q) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)) ∧
      (∀ n : ℕ,
      letI := finite_reduction_shift n
      NatTrans.CommShift (S.reductionEvaluation n).hom ℤ) := by
  classical
  have _coherence := hS
  let := SequenceKInjectiveComparison.totalLimitCommShift l E W
  let := S.adjunction.leftAdjointCommShift ℤ
  have hf (n : ℕ) : ∃ s : (coefficientFiniteDerivedExtension l E W n).CommShift ℤ,
      let := s
      NatTrans.CommShift (finiteCochainModel l E W n).ε ℤ := by
    let m := finiteCochainModel l E W n
    exact Functor.rightKanExtension_coherentShift
      (m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
      m.T m.ε m.universal.isRightKanExtension
  choose sf hsf using hf
  refine ⟨sf, ?_, ?_⟩
  · intro n Q r hQ hQr
    let := sf n
    have := hsf n
    have h := NatTrans.shift_app_comm (finiteCochainModel l E W n).ε r Q
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
    -- Use the cochain counits on both sides, with the same composition normal form as h.
    simp only [← finiteCochainModel_counit l E W n Q hQ,
      ← finiteCochainModel_counit l E W n (Q⟦r⟧) hQr, Category.assoc]
    with_unfolding_all exact h
  · intro n
    let := sf n
    let R := scalarReductionRestriction l E W n
    have : PreservesFiniteLimits R := (scalarReductionRestriction_exact l E W n).1
    have : PreservesFiniteColimits R := (scalarReductionRestriction_exact l E W n).2
    let : (coefficientFiniteDerivedRestriction l E W n).CommShift ℤ :=
      inferInstanceAs (R.mapDerivedCategory.CommShift ℤ)
    have : (coefficientFiniteAdjunction l E W n).CommShift ℤ :=
      finite_adj_shift l E W n (sf n) (hsf n)
    have : S.adjunction.CommShift ℤ := S.adjunction.commShift_of_rightAdjoint ℤ
    have : NatTrans.CommShift (coefficientSequenceProjection l E W n) ℤ :=
      sequence_projection_shift l E W n
    exact evaluation_shift S.reduction (coefficientSequenceLimit l E W)
      (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteDerivedRestriction l E W n)
      (coefficientSequenceDerivedEvaluation l E W n) S.adjunction
      (coefficientFiniteAdjunction l E W n) (S.reductionEvaluation n)
      (coefficientSequenceProjection l E W n) (fun N ↦ S.counit_projection N n)

end WeilConjectures
