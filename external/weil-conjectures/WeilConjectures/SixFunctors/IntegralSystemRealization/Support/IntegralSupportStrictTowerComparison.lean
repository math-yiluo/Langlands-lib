/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportNativeTowerComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOpenComparison

/-! # Strict compact-support tower comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local irreducible] HasDerivedCategory.standard Scheme.residueField
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  pullbackTensorCalculus
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverse_evaluation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (a : X ≅ Y) {Z : D}
    {p : F.obj X ⟶ Z} {q : F.obj Y ⟶ Z} (h : F.map a.hom ≫ q = p) :
    F.map a.inv ≫ p = q := by
  rw [← h, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

private theorem tower_evaluation {C D H I : Type*}
    [Category C] [Category D] [Category H] [Category I]
    (F : C ⥤ D) (G : D ⥤ I) (V : C ⥤ H) (R : H ⥤ I)
    (q : F ⋙ G ≅ V ⋙ R) {A B : C} {T : D} (b : A ≅ B) (a : T ≅ F.obj B)
    {Z U : H} (e₀ : V.obj A ⟶ Z) (e₁ : V.obj B ⟶ Z) (t : Z ⟶ U)
    (p : G.obj T ⟶ R.obj U)
    (ha : G.map a.hom ≫ q.hom.app B ≫ R.map (e₁ ≫ t) = p)
    (hb : V.map b.hom ≫ e₁ = e₀) :
    G.map (F.map b.hom ≫ a.inv) ≫ p = q.hom.app A ≫ R.map (e₀ ≫ t) := by
  have hc := inverse_evaluation G a ha
  rw [G.map_comp, Category.assoc, hc]
  have hn := q.hom.naturality b.hom
  dsimp only [Functor.comp_map] at hn
  have hb' : V.map b.hom ≫ (e₁ ≫ t) = e₀ ≫ t := by rw [← Category.assoc, hb]
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, hb']

private def nativeSupportIso (o : Operations l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g :=
  Functor.isoWhiskerRight (integralNativeOpenIso l E c.i (o.extension c.i)) _ ≪≫
    Functor.isoWhiskerLeft _ (integralNativeDirectIso l E c.g (o.direct c.g))

private theorem nativeSupportIso_evaluation (o : Operations l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : System l E X) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Y n).map
        ((nativeSupportIso l E o c).hom.app M) ≫
      (compactSupportSystemEvaluation l E c n).hom.app M =
        (supportEvaluation l E o c n).hom.app M := by
  let aJ := integralNativeOpenIso l E c.i (o.extension c.i)
  let aP := integralNativeDirectIso l E c.g (o.direct c.g)
  have haJ := integralNativeOpenComparison l E c.i (o.extension c.i) (o.openEvaluation c.i)
  have haP := integralNativeDirectComparison l E c.g (o.direct c.g) (o.evaluation c.g)
  let J := ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i
  let P := ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.g
  let b : Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ≅ J ⋙ P :=
    Functor.isoWhiskerRight aJ _ ≪≫ Functor.isoWhiskerLeft J aP
  let := proEtaleConstantModuleDirectImage_additive c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  let := sfIntrinsicExtensionByZero_additive c.i
    (Padic.coefficientExtensionRing l E (n + 1))
  let := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  let := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let R := proEtaleConstantDerivedDirectImage c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  let eJ := ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel c.i (Padic.coefficientExtensionRing l E (n + 1))))
  let eP := ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.g n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel c.g (Padic.coefficientExtensionRing l E (n + 1))))
  have hh : (coefficientSequenceDerivedEvaluation l E Y n).map
      ((Operations.push l E o c.g).map (aJ.hom.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map (aP.hom.app (J.obj M)) ≫
      eP.hom.app (J.obj M) ≫ R.map (eJ.hom.app M) =
    ((o.evaluation c.g).evaluation n).hom.app
      ((Operations.shriek l E o c.i).obj M) ≫
      R.map (((o.openEvaluation c.i).evaluation n).hom.app M) := by
    rw [← Category.assoc _ (eP.hom.app _) _, haP]
    have hn := ((o.evaluation c.g).evaluation n).hom.naturality (aJ.hom.app M)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, haJ]
  simpa only [nativeSupportIso, b, compactSupportSystemEvaluation, supportEvaluation,
    eP, eJ, R, J,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc] using hh

/-- The simultaneous open/proper system comparison identifies the prescribed strict
compact-support tower, retaining its specified finite evaluation maps.
Source: Stacks 0941 and 0D6E; fix-prop-coherence.proof.md, coefficient comparisons,
and primitive support realization Step 1
(blueprint: lem-sf-integral-support-strict-tower-comparison).

Proof: present the ordinary sequence-site direct images as the native varying-ring
ones by the identity on sections. Their left adjoints are identified by the units;
localizing the exact inverse images and taking right-adjoint conjugates identifies
both the open and proper derived operations with the native operations. Compare the
fixed reduction with the reduction used for the chosen support tower by uniqueness
of left adjoints to the common total limit. Its unit-projection identity identifies
finite evaluations with reductionEvaluation. Compose reduction, open, proper and
strict scalar restriction comparisons before localizing the whole diagram. The
result is the required tower isomorphism. Evaluating this composite, the ordinary
unit identities and the defining transpose identity of o.openEvaluation identify
its open component with that evaluation; the direct-image unit and counit identities
identify its proper component with o.evaluation. Hence the evaluated composite is
supportEvaluation followed by reductionEvaluation, with the displayed restricted
coordinate change. The chosen evaluations e are retained throughout, rather than
replaced by independently chosen levelwise comparisons. The restriction cocycle
keeps all quotient transitions. No faithfulness of finite derived evaluations is
used. Zero inputs and the empty open give the same zero comparison. -/
theorem integralSupportStrictTowerComparison (K₀ : Type u) [Field K₀]
    (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : IsUnit (l : K₀)) (c : Compactification f)
    (T : Integral l E X ⥤ coefficientSequenceRestrictedDerived l E Y)
    (e : ∀ n : ℕ,
      T ⋙ coefficientConstantTowerEvaluation l E Y n ≅ compactSupportRestrictedLevel l E c n)
    (hT : T = Classical.choose (Classical.choose_spec (Classical.choose_spec
      (exists_compactSupportReductionTower l E K₀ X Y f hl c))).2.2)
    (he : HEq e (Classical.choose (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E K₀ X Y f hl c))).2.2).2).2)) :
    ∃ tower : (calculus l E X).reduction ⋙
        Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
          coefficientSequenceDerivedRestriction l E Y ≅ T,
      ∀ (K : Integral l E X) (n : ℕ),
        (coefficientConstantTowerEvaluation l E Y n).map (tower.hom.app K) ≫
            (e n).hom.app K =
          (coefficientRestrictedEvaluationIso l E Y n).hom.app
              ((Operations.push l E o c.g).obj
                ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K))) ≫
            (scalarReductionDerivedRestriction l E Y n).map
              ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K) ≫
                (sfAmbientCompactSupportCandidate
                  (Padic.coefficientExtensionRing l E (n + 1)) c).map
                  (((calculus l E X).reductionEvaluation n).hom.app K)) := by
  classical
  subst T
  cases he
  let b := nativeSupportIso l E o c
  have hb := nativeSupportIso_evaluation l E o c
  obtain ⟨a, ha⟩ := qcqsCompactSupport_nativeTowerComparison l E K₀ hl
    (X := X) (Y := Y) (f := f) c (calculus l E X)
  let B := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (calculus l E X).reduction b)
    (coefficientSequenceDerivedRestriction l E Y)
  refine ⟨B ≪≫ a.symm, ?_⟩
  intro K n
  exact tower_evaluation
    (coefficientSequenceDerivedRestriction l E Y)
    (coefficientConstantTowerEvaluation l E Y n)
    (coefficientSequenceDerivedEvaluation l E Y n)
    (scalarReductionDerivedRestriction l E Y n)
    (coefficientRestrictedEvaluationIso l E Y n)
    (b.app ((calculus l E X).reduction.obj K)) (a.app K)
    ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K))
    ((compactSupportSystemEvaluation l E c n).hom.app ((calculus l E X).reduction.obj K))
    ((sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (((calculus l E X).reductionEvaluation n).hom.app K))
    _ (ha K n) (hb _ n)

end WeilConjectures.IntegralSystemRealization
