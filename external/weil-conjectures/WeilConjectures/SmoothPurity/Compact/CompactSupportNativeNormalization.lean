/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycle
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars

/-! # Normalization of the native compact-support system

The native output preserves normalized coefficient systems by the finite scalar
comparison and quotient cocycle.
(blueprint: lem-weil-compact-support-native-system-normalized).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true

set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct Opposite
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientSequenceTransition constantSheaf
  sfIntegralCompactSupportValue
  Padic.coefficientExtensionIdeal compactSupportOrdinaryCoefficientTransition

namespace CompactSupportNativeNormalization

private theorem derivedTransition_congr
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : A ⥤ C) (R R' : C ⥤ B)
    [F.Additive] [G.Additive] [R.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (h : R = R') (τ : F ⟶ G ⋙ R) (τ' : F ⟶ G ⋙ R')
    (hτ : τ ≫ Functor.whiskerLeft G (eqToHom h) = τ') :
    CategoryTheory.derivedTransition F G R τ ≫
      Functor.whiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (eqToIso h)).hom =
      CategoryTheory.derivedTransition F G R' τ' := by
  subst R'
  simp only [eqToHom_refl, Functor.whiskerLeft_id', Category.comp_id] at hτ
  subst τ'
  change _ ≫ Functor.whiskerLeft G.mapDerivedCategory
    (Functor.mapDerivedCategoryNatIso (Iso.refl R)).hom = _
  rw [Functor.mapDerivedCategoryNatIso_refl, Functor.whiskerLeft_id', Category.comp_id]

section TowerHelpers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance directQuotient_limits (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _

private instance directQuotient_colimits (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _

private def finiteRestrictionIso (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory :=
  by
    let : PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)) :=
      proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _
    let : PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)) :=
      proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _
    exact Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W h))

private theorem ordinaryTransition_app_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E W) :
    (coefficientSequenceTransition.{u, u} l E W h).app M ≫
      eqToHom (congrArg
        (fun F : normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m ↦
          F.obj ((coefficientSequenceEvaluation.{u, u} l E W n).obj M))
        (compactSupportModuleRes_eq l E W h)) =
      (compactSupportOrdinaryCoefficientTransition l E W h).app M := by
  simpa only [eqToHom_refl, Category.id_comp] using
    moduleHom_eq_of_heq rfl
      (congrArg (fun F : normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m ↦
        F.obj ((coefficientSequenceEvaluation.{u, u} l E W n).obj M))
          (compactSupportModuleRes_eq l E W h))
      ((coefficientSequenceTransition.{u, u} l E W h).app M)
      ((compactSupportOrdinaryCoefficientTransition l E W h).app M)
      (fun V ↦ (transition_heq l E W M h V).trans
        (compactSupportOrdinaryCoefficientTransition_sections l E W h M V).symm)

private theorem derivedTransition_direct (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedTransition.{u, u} l E W h ≫
      Functor.whiskerLeft (coefficientSequenceDerivedEvaluation.{u, u} l E W n)
        (finiteRestrictionIso l E W h).hom =
      compactSupportCoefficientTransition l E W h := by
  let : PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
    proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _
  let : PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
    proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _
  have H := derivedTransition_congr
    (coefficientSequenceEvaluation.{u, u} l E W m) (coefficientSequenceEvaluation.{u, u} l E W n)
    (normalizedDVRModuleRes l E W h)
    (proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h))
    (compactSupportModuleRes_eq l E W h)
    (coefficientSequenceTransition.{u, u} l E W h)
    (compactSupportOrdinaryCoefficientTransition l E W h) (by
      apply NatTrans.ext
      funext M
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] using
        ordinaryTransition_app_eq l E W h M)
  unfold CategoryTheory.derivedTransition at H
  exact H

private theorem adjacentRestrictionComp (W : Scheme.{u}) (j : ℕ) :
    compactSupportRestrictionComp l E W (j + 1) j j.le_succ =
      sfCompactSupportDerivedRestrictionComp l E W j := by
  rfl

private theorem adjacentReductionMap (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) (j : ℕ) :
    compactSupportReductionMap l E W (j + 1) j j.le_succ K =
      sfCompactSupportReductionTransition l E W K j := by
  rfl

private theorem adjacentQuotient (j : ℕ) :
    compactSupportLevelQuotient l E (j + 1) j j.le_succ =
      Padic.coefficientExtensionTransition l E (j + 1) := by
  rfl

private theorem finiteConstructible_iso (W : Scheme.{u}) (n : ℕ)
    {A B : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : A ≅ B)
    (h : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W A) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W B := by
  constructor
  · apply h.1.subset
    intro i hi
    exact fun hz ↦ hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    have hc := h.2 i
    rw [proEtaleModuleRestriction_constructible_iff] at hc ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction W (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hc

private theorem constantTowerTransition_eq (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRTowerTransition l E W D hl h =
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h := by
  rfl

end TowerHelpers
end CompactSupportNativeNormalization

open CompactSupportNativeNormalization

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Native open extension followed by proper direct image preserves normalization
for the reduction of an integral constructible complex.
Source: blueprint lem-fix-operation-reduction.proof.md, compact-support paragraph.
(blueprint: lem-weil-compact-support-native-system-normalized).
Proof: use the quotient cocycle to identify the input transition adjunct with an
isomorphism. Finite constructibility transports across that isomorphism. The finite
compact-support scalar comparison identifies the output transition adjunct with
the composite of two isomorphisms. Evaluation naturality transports this result
back to the system transition. Finally the direct quotient restriction and the
sequence-site restriction have identical horizontal section maps; their derived
transition isomorphism transfers the resulting representable bijection. -/
theorem compactSupportNativeSystem_normalized
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (K : sfIntegralConstructibleCategory l E X)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    IsNormalizedCoefficientSequence.{u, u} l E Y
      ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K.obj)) := by
  classical
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K.obj)
  let F (n : ℕ) := sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E (n + 1))
  let L (n : ℕ) := (scalarReductionDerivedExtension l E X n).obj K.obj
  let e (n : ℕ) : (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ≅
      (F n).obj (L n) :=
    (compactSupportSystemEvaluation l E c n).app (S.reduction.obj K.obj) ≪≫
      (F n).mapIso ((S.reductionEvaluation n).app K.obj)
  obtain ⟨a, b, hab, hK⟩ := K.property.2
  intro m n h P
  let Rx := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n h)
  let Ry := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h)
  let ax := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)
  let ay := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E Y m n h)
  let β := (ax.homEquiv _ _).symm (compactSupportReductionMap l E X m n h K.obj)
  have hβ : IsIso β := (compactSupport_quotient_cocycle l E K₀ hl c K.obj).1 m n h |>.1
  let := hβ
  have hred : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)) :=
    finiteConstructible_iso l E X n (asIso β).symm (hK n).1
  let τ := (F m).map (compactSupportReductionMap l E X m n h K.obj) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n)
  let q := (ay.homEquiv _ _).symm τ
  let z := (ay.homEquiv _ _).symm ((F m).map (ax.unit.app (L m)) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)))
  have hz : IsIso z := finiteCompactSupportScalarComparison l E K₀ hl
    (m + 1) (Nat.succ_pos m) (n + 1) (Nat.succ_pos n) (Nat.add_le_add_right h 1)
    f c (L m) (hK m).1 hred
  let := hz
  have hτ : τ = ((F m).map (ax.unit.app (L m)) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m))) ≫
      Ry.map ((F n).map β) := by
    have hn := (sfCompactSupportRestriction c
      (compactSupportLevelQuotient l E m n h)).hom.naturality β
    change (F m).map (Rx.map β) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n) =
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)) ≫
        Ry.map ((F n).map β) at hn
    change (F m).map (compactSupportReductionMap l E X m n h K.obj) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        (L n) = _
    rw [Category.assoc, ← hn, ← Category.assoc, ← (F m).map_comp]
    exact congrArg (fun d ↦ (F m).map d ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n))
      ((compactSupport_quotient_cocycle l E K₀ hl c K.obj).1 m n h).2
  have hqeq : q = z ≫ (F n).map β :=
    (congrArg ((ay.homEquiv _ _).symm) hτ).trans
      (ay.homEquiv_naturality_right_symm _ _)
  have hq : IsIso q := by rw [hqeq]; infer_instance
  let := hq
  have ht : (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map (e n).hom =
      (e m).hom ≫ τ := by
    have hg := compactSupportNativeSystemTransition l E c h (S.reduction.obj K.obj)
    have hd := compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction
      h K.obj
    have H := compactSupportFiniteSquare (F m) (F n) Rx Ry
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom
      _ _ _ _ _ _ _ hg hd
    simpa only [N, τ, L, coefficientFiniteDerivedExtension, e, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using H
  let qN := (ay.homEquiv _ _).symm ((compactSupportCoefficientTransition l E Y h).app N)
  have hqN : qN ≫ (e n).hom =
      (pbcDerivedExtend (compactSupportLevelSheafQuotient l E Y m n h)).map (e m).hom ≫ q := by
    calc
      qN ≫ (e n).hom = (ay.homEquiv _ _).symm
          ((compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map (e n).hom) :=
        (ay.homEquiv_naturality_right_symm _ _).symm
      _ = (ay.homEquiv _ _).symm ((e m).hom ≫ τ) := congrArg _ ht
      _ = (pbcDerivedExtend (compactSupportLevelSheafQuotient l E Y m n h)).map
          (e m).hom ≫ q := ay.homEquiv_naturality_left_symm _ _
  have : IsIso (qN ≫ (e n).hom) := by rw [hqN]; infer_instance
  have : IsIso qN := IsIso.of_isIso_comp_right qN (e n).hom
  have hb : Function.Bijective (fun g :
      (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ⟶ P ↦
      (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map g) := by
    have hb := ((ay.homEquiv _ P).bijective).comp
      ((isIso_iff_coyoneda_map_bijective qN).mp inferInstance P)
    simpa only [Function.comp_def, qN, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply] using hb
  let ε := finiteRestrictionIso l E Y h
  have he : (fun g : (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ⟶ P ↦
      (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map g) =
      (fun z ↦ z ≫ ε.hom.app P) ∘
        (fun g ↦ (coefficientSequenceDerivedTransition.{u, u} l E Y h).app N ≫
          (normalizedDVRRes l E Y h).map g) := by
    funext g
    have hn := ε.hom.naturality g
    dsimp only [Function.comp_apply]
    rw [Category.assoc, hn, ← Category.assoc]
    exact congrArg (fun d ↦ d ≫ Ry.map g) (NatTrans.congr_app
      (derivedTransition_direct l E Y h) N).symm
  rw [he] at hb
  exact Function.Bijective.of_comp_left (f := fun z ↦ z ≫ ε.hom.app P) hb
    (fun a b hab ↦ (cancel_mono (ε.hom.app P)).mp hab)

end FiniteAction
end WeilConjectures
