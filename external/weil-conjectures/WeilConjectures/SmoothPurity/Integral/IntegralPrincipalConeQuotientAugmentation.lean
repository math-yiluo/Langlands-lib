/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAugmentation
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # The levelwise principal-cone augmentation to integral quotients

Source: Stacks Tags 0A0E, 093M and 0941.
(blueprint: lem-pur-integral-principal-cone-quotient-augmentation) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

private theorem ordinaryExtension_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ)
    [HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients (IntegralOnSlice.topology T none)
        (IntegralOnSlice.finite l E T none n)))]
    (d : SheafOfModules.DerivedChangeOfRingsCochainModel
      (C := IntegralOnSlice.Site T none) (J := IntegralOnSlice.topology T none)
      (IntegralOnSlice.projection l E T none n)) :
    d.E = IntegralOnSlice.reduction l E T none n := by
  apply CategoryTheory.Functor.ext (F := d.E)
    (G := IntegralOnSlice.reduction l E T none n) (fun M ↦ (d.obj_eq M).trans
    (IntegralOnSlice.reduction_obj l E T none n M).symm) ?_
  intro M N f
  rw [d.map_eq, IntegralOnSlice.unrestrictedReduction_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

private def uniformizerValue
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (U : T.ProEtᵒᵖ) : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U :=
  (PrincipalKoszulStrictReplacement.uniformizer l E T).val U

private def uniformizerPower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) :
    (SheafOfModules.unit (IntegralOnSlice.rings l E T none)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ uniformizerValue l E T U ^ (n + 1))
    (by
      intro U V f
      change (completedIntegralCoefficientSheafUnrestricted l E T).obj.map f
          (uniformizerValue l E T U ^ (n + 1)) = _
      rw [map_pow]
      congr 1
      exact (PrincipalKoszulStrictReplacement.uniformizer l E T).property f)

private theorem regularScalar_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) :
    (SheafOfModules.RegularQuotientCone.scalar (IntegralOnSlice.ring l E T none)
      (uniformizerPower l E T n)).app (SheafOfModules.unit (IntegralOnSlice.rings l E T none)) =
      PrincipalKoszulStrictReplacement.multiplication l E T n := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U at x
  change (uniformizerValue l E T U ^ (n + 1)) * x = _
  have h := PrincipalKoszulStrictReplacement.multiplication_apply l E T n
    (show T.ProEtᵒᵖ from U) x
  change _ = x * uniformizerValue l E T U ^ (n + 1) at h
  exact (completedIntegralCoefficient_mul_commUnrestricted l E T
    (show T.ProEtᵒᵖ from U) _ x).trans h.symm

private theorem regularProjection_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) :
    SheafOfModules.RegularQuotientCone.ringMap (IntegralOnSlice.projection l E T none n) =
      PrincipalKoszulStrictReplacement.projection l E T n := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem regularExact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) :
    ∃ ht : (SheafOfModules.RegularQuotientCone.scalar (IntegralOnSlice.ring l E T none)
        (uniformizerPower l E T n)).app
        (SheafOfModules.unit (IntegralOnSlice.rings l E T none)) ≫
          SheafOfModules.RegularQuotientCone.ringMap
            (IntegralOnSlice.projection l E T none n) = 0,
      (ShortComplex.mk _ _ ht).ShortExact := by
  simp only [regularScalar_eq, regularProjection_eq]
  exact ⟨PrincipalKoszulStrictReplacement.multiplication_projection l E T n,
    (PrincipalKoszulStrictReplacement.completed_exact l E T n).1⟩

private theorem scalarPower_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (P : IntegralOnSlice.Cx l E T none) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x = uniformizerValue l E T U • x) (n : ℕ) :
    μ ^ (n + 1) = End.of ((SheafOfModules.RegularQuotientCone.complexScalar
      (IntegralOnSlice.ring l E T none) (uniformizerPower l E T n)).app P) := by
  have hp (k : ℕ) (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U) :
      ((μ ^ k).asHom.f q).val.app U x = uniformizerValue l E T U ^ k • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, End.mul_asHom]
      change ((μ ^ k).asHom.f q).val.app U ((μ.asHom.f q).val.app U x) = _
      rw [hμ]
      have hlin := (((μ ^ k).asHom.f q).val.app U).hom.map_smul
        (uniformizerValue l E T U) x
      rw [hlin, ih, smul_smul, pow_succ']
  apply End.ext
  apply HomologicalComplex.hom_ext
  intro q
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hp (n + 1) q U x

private theorem complexExtensionCast_f {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (F G : A ⥤ B)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (h : F = G)
    (P : CochainComplex A ℤ) (q : ℤ) :
    ((NatIso.mapHomologicalComplex (eqToIso h) (.up ℤ)).hom.app P).f q =
      eqToHom (congrArg (fun H : A ⥤ B ↦ H.obj (P.X q)) h) := by
  subst G
  rfl

private theorem transportConeAugmentation {A : Type*} [Category* A] [Abelian A]
    {P X Y : CochainComplex A ℤ} {f g : End P} (h : f = g)
    (b : CochainComplex.mappingCone g.asHom ⟶ X) [QuasiIso b]
    (ρ : P ⟶ X) (e : X ≅ Y)
    (hb : ∀ q : ℤ, b.f q =
      (CochainComplex.mappingCone.snd g.asHom).v q q (add_zero q) ≫ ρ.f q) :
    ∃ a : CochainComplex.mappingCone f.asHom ⟶ Y, QuasiIso a ∧
      ∀ q : ℤ, a.f q =
        (CochainComplex.mappingCone.snd f.asHom).v q q (add_zero q) ≫ (ρ ≫ e.hom).f q := by
  subst g
  refine ⟨b ≫ e.hom, inferInstance, ?_⟩
  intro q
  simp only [HomologicalComplex.comp_f, hb, Category.assoc]

private theorem coneAugmentations {A : Type*} [Category* A] [Abelian A]
    {P : CochainComplex A ℤ} (μ : End P) (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ C)
    (a : ∀ n : ℕ, CochainComplex.PrincipalCone.level μ n ⟶ C.obj (op n))
    (ha : ∀ (n : ℕ) (q : ℤ), (a n).f q =
      (CochainComplex.mappingCone.snd (μ ^ (n + 1)).asHom).v q q (add_zero q) ≫
        (γ.app (op n)).f q) :
    (∀ n, CochainComplex.PrincipalCone.step μ n ≫ a n =
      a (n + 1) ≫ integralOperationsTowerStep C n) ∧
    (∀ n, CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ a n = γ.app (op n)) := by
  constructor
  · intro n
    apply HomologicalComplex.hom_ext
    intro q
    apply CochainComplex.mappingCone.ext_from (μ ^ (n + 1 + 1)).asHom (q + 1) q rfl
    · simp [HomologicalComplex.comp_f, ha, CochainComplex.PrincipalCone.step,
        CochainComplex.mappingCone.map]
    · have h := congrArg (fun k ↦ k.f q) (γ.naturality (homOfLE n.le_succ).op)
      simpa [HomologicalComplex.comp_f, ha, CochainComplex.PrincipalCone.step,
        CochainComplex.mappingCone.map, Category.assoc, integralOperationsTowerStep] using h
  · intro n
    apply HomologicalComplex.hom_ext
    intro q
    simp only [HomologicalComplex.comp_f, ha,
      CochainComplex.mappingCone.inr_f_snd_v_assoc]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  IntegralOnSlice.reductionWitness
  unrestrictedIntegralReductionExistence

private theorem levelAugmentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (P : IntegralOnSlice.Cx l E T none)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) P)
    (μ : End P)
    (hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x = uniformizerValue l E T U • x) (n : ℕ) :
    ∃ a : CochainComplex.PrincipalCone.level μ n ⟶
        ((IntegralOnSlice.tower l E T none).obj P).obj (op n),
      QuasiIso a ∧ ∀ q : ℤ, a.f q =
        (CochainComplex.mappingCone.snd (μ ^ (n + 1)).asHom).v q q (add_zero q) ≫
          ((((IntegralOnSlice.augmentation l E T none).app P).app (op n)).f q) := by
  let : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T none) :=
    essentiallySmallSelf _
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients (IntegralOnSlice.topology T none)
      (IntegralOnSlice.finite l E T none n)))
  obtain ⟨d⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (IntegralOnSlice.projection l E T none n)
  obtain ⟨ht, hexact⟩ := regularExact l E T n
  obtain ⟨b⟩ := SheafOfModules.RegularQuotientCone.nonempty_augmentation
    (IntegralOnSlice.projection l E T none n) (uniformizerPower l E T n) ht hexact d
  let ed := NatIso.mapHomologicalComplex (eqToIso (ordinaryExtension_eq l E T n d)) (.up ℤ)
  let V := (SheafOfModules.RegularQuotientCone.restriction
    (IntegralOnSlice.projection l E T none n)).mapHomologicalComplex (.up ℤ)
  have hρ : b.ρ.app P ≫ V.map (ed.hom.app P) =
      ((IntegralOnSlice.augmentation l E T none).app P).app (op n) := by
    apply HomologicalComplex.hom_ext
    intro q
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := b.ρ_sections P q U x
    have hγ := (IntegralOnSlice.augmentation_existsUnique l E T none).exists.choose_spec
      P n q U x
    change ((V.map (ed.hom.app P)).f q).val.app U
        (((b.ρ.app P).f q).val.app U x) = _
    change (((((IntegralOnSlice.augmentation_existsUnique l E T none).exists.choose.app P).app
      (op n)).f q).val.app U x) = _ at hγ
    have hγ' : (((((IntegralOnSlice.augmentation l E T none).app P).app (op n)).f q).val.app U x) =
        IntegralOnSlice.generator l E T none n (P.X q) U 1 x := hγ
    erw [hγ']
    let F := SheafOfModules.evaluation
      (SheafOfModules.derivedChangeRingIndependentCoefficients (IntegralOnSlice.topology T none)
        (IntegralOnSlice.finite l E T none n)) U
    have hiso : IsIso (F.map (eqToHom
      (IntegralOnSlice.reduction_obj l E T none n (P.X q)))) := inferInstance
    apply (ConcreteCategory.bijective_of_isIso (F.map (eqToHom
      (IntegralOnSlice.reduction_obj l E T none n (P.X q))))).1
    have ht : (ed.hom.app P).f q ≫
        eqToHom (IntegralOnSlice.reduction_obj l E T none n (P.X q)) =
        eqToHom (d.obj_eq (P.X q)) := by
      dsimp only [ed]
      rw [complexExtensionCast_f]
      simp only [eqToHom_trans]
    have ht' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.val.app U) ht)
      (((b.ρ.app P).f q).val.app U x)
    change (eqToHom (IntegralOnSlice.reduction_obj l E T none n (P.X q))).val.app U
      (((ed.hom.app P).f q).val.app U
        (((b.ρ.app P).f q).val.app U x)) = _
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      CategoryTheory.comp_apply] at ht'
    refine ht'.trans (h.trans ?_)
    change _ = (eqToHom (IntegralOnSlice.reduction_obj l E T none n (P.X q))).val.app U
      (IntegralOnSlice.generator l E T none n (P.X q) U 1 x)
    have hi := (F.mapIso (eqToIso
      (IntegralOnSlice.reduction_obj l E T none n (P.X q)))).inv_hom_id
    dsimp only [IntegralOnSlice.generator]
    change _ = (F.map (eqToHom
      (IntegralOnSlice.reduction_obj l E T none n (P.X q))))
      ((F.map (eqToHom (IntegralOnSlice.reduction_obj l E T none n (P.X q)).symm)) _)
    exact (ConcreteCategory.congr_hom hi _).symm
  have : QuasiIso (b.a.app P) := b.quasiIso P hP
  obtain ⟨a, ha, hc⟩ := transportConeAugmentation (scalarPower_eq l E T P μ hμ n)
    (b.a.app P) (b.ρ.app P) (V.mapIso (ed.app P)) (b.a_components P)
  refine ⟨a, ha, ?_⟩
  intro q
  have h := hc q
  change a.f q = (CochainComplex.mappingCone.snd (μ ^ (n + 1)).asHom).v q q (add_zero q) ≫
    (b.ρ.app P ≫ V.map (ed.hom.app P)).f q at h
  rw [hρ] at h
  exact h

/-- K-flat tensoring of the regular principal-quotient resolution gives a strict,
levelwise quasi-isomorphic comparison of augmented towers. The quotient augmentation
is the actual x mapped to 1 tensor x map, not a freely chosen comparison.

Source: Stacks Tags 0A0E, 093M and 06YP.
(blueprint: lem-pur-integral-principal-cone-quotient-augmentation).

Proof: completed_exact gives the short exact sequence whose maps are multiplication
by the actual uniformizer power and the actual completed projection. Apply the
normalized regular-quotient cone augmentation with its section formula. K-flatness
makes its component on P a quasi-isomorphism. The section formula for μ identifies
its positive powers with the scalar endomorphisms used there. The fixed object and map
identifications of ordinary scalar extension identify the target with IntegralOnSlice
level n. On each cone summand the adjacent square commutes: on the shifted summand
both augmentations are zero, and on the unshifted summand quotient transition sends
1 tensor x to 1 tensor x. Sheafification and equality of maps in every degree prove
the strict transition equation. The same unshifted formula identifies the composite
of the cone inclusion with the specified quotient augmentation. This works for zero
P and for n=0, which denotes the first positive power. -/
theorem integralPrincipalConeQuotientAugmentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (P : IntegralOnSlice.Cx l E T none)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) P)
    (μ : End P)
    (_hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x =
        (integralConstantToCompletionOfUniverses l E T).hom.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
                (ULift.up (Padic.coefficientExtensionUniformizer l E))) • x) :
    ∃ a : ∀ n : ℕ, CochainComplex.PrincipalCone.level μ n ⟶
        ((IntegralOnSlice.tower l E T none).obj P).obj (op n),
      (∀ n, QuasiIso (a n)) ∧
      (∀ n, CochainComplex.PrincipalCone.step μ n ≫ a n =
        a (n + 1) ≫ integralOperationsTowerStep
          ((IntegralOnSlice.tower l E T none).obj P) n) ∧
      (∀ n, CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ a n =
        ((IntegralOnSlice.augmentation l E T none).app P).app (op n)) := by
  classical
  choose a ha hc using fun n ↦ levelAugmentation l E T P _hP μ _hμ n
  obtain ⟨hs, hu⟩ := coneAugmentations μ ((IntegralOnSlice.tower l E T none).obj P)
    ((IntegralOnSlice.augmentation l E T none).app P) a hc
  exact ⟨a, ha, hs, hu⟩

end WeilConjectures
