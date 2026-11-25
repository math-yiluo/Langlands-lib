/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.Algebra.Homology.OrdinaryCommonQuotientTower.OrdinaryCommonQuotientTowerSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Ordinary pullback of one finite quotient module

Source: Stacks Project, Modules on Sites, lemma-tensor-product-pullback (03EL),
and Cohomology on Sites, Tags 06YY and 07A4. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.IntegralOnSlice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- One ordinary quotient, with the completed coefficient action restored.
Source: Stacks 03EL and 06YY
(blueprint: lem-fix-ordinary-quotient-module-comparison). -/
abbrev ordinaryQuotientModule (W : Scheme.{t}) (n : ℕ) :
    Mod l E W none ⥤ Mod l E W none :=
  reduction l E W none n ⋙ SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (projection l E W none n))

private abbrev quotientUnit (W : Scheme.{t}) (n : ℕ) :
    𝟭 (Mod l E W none) ⟶ ordinaryQuotientModule l E W n :=
  moduleUnit l E W none n

private theorem projection_surjective (W : Scheme.{t}) (n : ℕ)
    (V : W.ProEtᵒᵖ) : Function.Surjective ((projection l E W none n).hom.app V) := by
  intro a
  obtain ⟨b, hb⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E W n V a
  refine ⟨(integralConstantToCompletionOfUniverses l E W).hom.app V b, ?_⟩
  exact (congrArg (fun h ↦ h.hom.app V b)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))).trans hb

private theorem quotientUnit_epi (W : Scheme.{t}) (n : ℕ) (M : Mod l E W none) :
    Epi ((quotientUnit l E W n).app M) := by
  let q := projection l E W none n
  have hq : Presheaf.IsLocallySurjective (ProEt.topology W) q.hom :=
    Presheaf.isLocallySurjective_of_surjective (ProEt.topology W) q.hom
      (projection_surjective l E W n)
  let e := (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map q)).mapIso
      (eqToIso (reduction_obj l E W none n M)).symm
  have h := SheafOfModules.quotientUnit_epi q hq M
    (SheafOfModules.commonQuotientUnit q M)
    (SheafOfModules.commonQuotientUnit_sections q M)
  have he : (quotientUnit l E W n).app M =
      SheafOfModules.commonQuotientUnit q M ≫ e.hom := by
    ext V x
    rfl
  rw [he]
  exact epi_comp _ _

private def uniformizerSection (W : Scheme.{t}) (V : W.ProEtᵒᵖ) :
    (ring l E W none).obj.obj V :=
  (integralConstantToCompletionOfUniverses l E W).hom.app V
    ((toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app V
          (ULift.up (Padic.coefficientExtensionUniformizer l E)))

private theorem uniformizerSection_natural (W : Scheme.{t})
    {V Z : W.ProEtᵒᵖ} (i : V ⟶ Z) :
    (ring l E W none).obj.map i (uniformizerSection l E W V) =
      uniformizerSection l E W Z := by
  change (completedIntegralCoefficientSheafUnrestricted l E W).obj.map i _ = _
  unfold uniformizerSection
  have hc := ConcreteCategory.congr_hom
    ((integralConstantToCompletionOfUniverses l E W).hom.naturality i)
      ((toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app V
            (ULift.up (Padic.coefficientExtensionUniformizer l E)))
  refine hc.symm.trans ?_
  apply congrArg ((integralConstantToCompletionOfUniverses l E W).hom.app Z)
  exact (ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).naturality i)
          (ULift.up (Padic.coefficientExtensionUniformizer l E))).symm

private def uniformizerPower (W : Scheme.{t}) (n : ℕ) (M : Mod l E W none) : M ⟶ M where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        { toFun := fun x ↦ uniformizerSection l E W V ^ (n + 1) • x
          map_add' := smul_add _
          map_smul' := fun r x ↦ by simp only [RingHom.id_apply, smul_smul, mul_comm] }
      naturality := by
        intro V Z i
        ext x
        change uniformizerSection l E W Z ^ (n + 1) •
            (show M.val.obj Z from M.val.map i x) =
          M.val.map i (uniformizerSection l E W V ^ (n + 1) • x)
        rw [PresheafOfModules.map_smul, map_pow]
        change uniformizerSection l E W Z ^ (n + 1) •
            (show M.val.obj Z from M.val.map i x) =
          (ring l E W none).obj.map i (uniformizerSection l E W V) ^ (n + 1) •
            (show M.val.obj Z from M.val.map i x)
        rw [uniformizerSection_natural] }

private theorem projection_uniformizer_zero (W : Scheme.{t}) (n : ℕ)
    (V : W.ProEtᵒᵖ) :
    (projection l E W none n).hom.app V (uniformizerSection l E W V ^ (n + 1)) = 0 := by
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  let B := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let a : A := ULift.up (Padic.coefficientExtensionUniformizer l E)
  let q : A ⟶ B := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        ULift.ringEquiv.toRingHom))
  have hq : q (a ^ (n + 1)) = 0 := by
    apply ULift.ext
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (n + 1)
  have hp := congrArg (fun h ↦ h.hom.app V)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))
  have ht := toSheafify_naturality (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).map q)
  calc
    _ = (integralConstantQuotientOfUniverses l E W n).hom.app V
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app V
          (a ^ (n + 1))) := by
      let c := integralConstantToCompletionOfUniverses l E W
      let η := toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)
      have hpow : c.hom.app V (η.app V (a ^ (n + 1))) =
          (c.hom.app V (η.app V a)) ^ (n + 1) :=
        (congrArg (c.hom.app V) ((η.app V).hom.map_pow a (n + 1))).trans
          ((c.hom.app V).hom.map_pow (η.app V a) (n + 1))
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V
        ((c.hom.app V (η.app V a)) ^ (n + 1)) = _
      rw [← hpow]
      exact congrArg (fun h ↦ h (η.app V (a ^ (n + 1)))) hp
    _ = (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj B)).app V
        (q (a ^ (n + 1))) :=
      (congrArg (fun h ↦ h.app V (a ^ (n + 1))) ht).symm
    _ = 0 := by rw [hq, map_zero]

private theorem quotientUnit_isCokernel (W : Scheme.{t}) (n : ℕ)
    (M : Mod l E W none) :
    ∃ h : uniformizerPower l E W n M ≫ (quotientUnit l E W n).app M = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((quotientUnit l E W n).app M) h)) := by
  let q := projection l E W none n
  let uM := (quotientUnit l E W n).app M
  have hu : uniformizerPower l E W n M ≫ uM = 0 := by
    ext V x
    change uM.val.app V (uniformizerSection l E W V ^ (n + 1) • x) = 0
    rw [map_smul]
    change (q.hom.app V (uniformizerSection l E W V ^ (n + 1))) •
      (show ((reduction l E W none n).obj M).val.obj V from uM.val.app V x) = 0
    rw [projection_uniformizer_zero, zero_smul]
  have huEpi : Epi uM := quotientUnit_epi l E W n M
  have hdesc {N : Mod l E W none} (g : M ⟶ N)
      (hg : uniformizerPower l E W n M ≫ g = 0) : kernel.ι uM ≫ g = 0 := by
    ext V x
    let y := (kernel.ι uM).val.app V x
    have hy : uM.val.app V y = 0 :=
      congrArg (fun h ↦ h.val.app V x) (kernel.condition uM)
    have hq : Presheaf.IsLocallySurjective (ProEt.topology W) q.hom :=
      Presheaf.isLocallySurjective_of_surjective (ProEt.topology W) q.hom
      (projection_surjective l E W n)
    have hy' : (toSheafify (ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf q M).presheaf).app V
          ((1 : (finite l E W none n).obj.obj V) ⊗ₜ[(ring l E W none).obj.obj V,
            (q.hom.app V).hom] y) = 0 := by
      change (unitModule l E W none n M).val.app V y = 0 at hy
      rw [unitModule_apply] at hy
      have hh := congrArg ((eqToHom (reduction_obj l E W none n M)).val.app V) hy
      simpa only [generator,
        ← SheafOfModules.comp_val, ← PresheafOfModules.comp_app, ← ModuleCat.comp_apply,
        eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply, map_zero, q, topology] using hh
    have hlocal := SheafOfModules.kernel_forward q hq M V y hy'
    have hk (Z : W.ProEtᵒᵖ) :
        Submodule.span ((ring l E W none).obj.obj Z)
          {z | ∃ j ∈ RingHom.ker (q.hom.app Z).hom,
            ∃ p : M.val.obj Z, z = j • p} ≤ LinearMap.ker (g.val.app Z).hom := by
      apply Submodule.span_le.mpr
      rintro z ⟨j, hj, p, rfl⟩
      obtain ⟨b, hb⟩ := AlgebraicGeometry.ProEtale.completedIntegralProjection_divisible
        l E W n Z j hj
      change g.val.app Z (j • p) = 0
      rw [hb, mul_smul]
      exact congrArg (fun h ↦ h.val.app Z (b • p)) hg
    let S := Presheaf.equalizerSieve (F := N.val.presheaf) (g.val.app V y) 0
    have hS : S ∈ ProEt.topology W V.unop := by
      apply (ProEt.topology W).superset_covering ?_ hlocal
      apply (Sieve.generate_le_iff _ S).mpr
      intro Z i hi
      change N.val.map i.op (g.val.app V y) = N.val.map i.op 0
      rw [map_zero, ← PresheafOfModules.naturality_apply g.val i.op y]
      exact hk (op Z) hi
    apply N.isSheaf.isSeparated _ _ hS
    intro Z i hi
    exact hi
  refine ⟨hu, ⟨CokernelCofork.IsColimit.ofπ' uM hu ?_⟩⟩
  intro N g hg
  exact ⟨Abelian.epiDesc uM g (hdesc g hg), Abelian.comp_epiDesc uM g (hdesc g hg)⟩

private theorem constant_direct_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
        coefficientProEtaleDirectRingMap f B =
      coefficientProEtaleDirectRingMap f A ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv _ _ |>.injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [coefficientProEtaleDirectRingMap, constantSheaf,
    Functor.comp_obj, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congr_app ((sheafificationAdjunction (ProEt.topology X)
    CommRingCat.{max u (t + 1)}).unit.naturality
      ((Functor.const X.ProEtᵒᵖ).map a)) ((proEtaleBaseChange f).op.obj V)

private theorem constant_direct_section {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) (V : Y.ProEtᵒᵖ) (a : A) :
    (coefficientProEtaleDirectRingMap f A).hom.app V
        ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app V a) =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange f).op.obj V) a := by
  let T := ((proEtaleBaseChange f).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)
  have h := ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A) T).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun h ↦ h.app V a) h

private theorem completed_direct_scalar {X Y : Scheme.{t}} (f : X ⟶ Y) :
    integralConstantToCompletionOfUniverses l E Y ≫ ordinaryCompletedRingMap l E f =
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (coefficientProEtaleDirectRingMap f
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))) ≫
        (ordinaryRingPush.{t, u} f).map (integralConstantToCompletionOfUniverses l E X) := by
  let G := ordinaryRingPush.{t, u} f
  have hρ (n : ℕ) : ordinaryCompletedRingMap l E f ≫
      G.map (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
      limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
        ordinaryFiniteRingMap l E f n :=
    (ordinaryCompletedRingMap_existsUnique l E f).exists.choose_spec n
  have hc (W : Scheme.{t}) (n : ℕ) : integralConstantToCompletionOfUniverses l E W ≫
      limit.π (integralCoefficientSheafSystem l E W) (op n) =
        integralConstantQuotientOfUniverses l E W n :=
    limit.lift_π (integralConstantConeOfUniverses l E W) (op n)
  apply (isLimitOfPreserves G
    (limit.isLimit (integralCoefficientSheafSystem l E X))).hom_ext
  rintro ⟨n⟩
  change (integralConstantToCompletionOfUniverses l E Y ≫ ordinaryCompletedRingMap l E f) ≫
      G.map (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
    (_ ≫ G.map (integralConstantToCompletionOfUniverses l E X)) ≫
      G.map (limit.π (integralCoefficientSheafSystem l E X) (op n))
  rw [Category.assoc, hρ n, ← Category.assoc, hc Y n]
  rw [Category.assoc, ← G.map_comp, hc X n]
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  let B := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let a : A ⟶ B := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        ULift.ringEquiv.toRingHom))
  have h := congrArg
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map)
    (constant_direct_naturality f a)
  simp only [Functor.map_comp] at h
  exact h

private theorem completed_direct_uniformizer {X Y : Scheme.{t}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) :
    (ordinaryCompletedRingMap l E f).hom.app V (uniformizerSection l E Y V) =
      uniformizerSection l E X ((proEtaleBaseChange f).op.obj V) := by
  have h := congrArg (fun h ↦ h.hom.app V
    ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app V
          (ULift.up (Padic.coefficientExtensionUniformizer l E))))
    (completed_direct_scalar l E f)
  change _ = (integralConstantToCompletionOfUniverses l E X).hom.app
    ((proEtaleBaseChange f).op.obj V)
      ((coefficientProEtaleDirectRingMap f _).hom.app V _) at h
  rw [constant_direct_section] at h
  exact h

private theorem pull_uniformizerPower {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : Mod l E Y none) :
    (ordinaryPull l E f).map (uniformizerPower l E Y n M) =
      uniformizerPower l E X n ((ordinaryPull l E f).obj M) := by
  apply ((ordinaryAdjunction l E f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hn := (ordinaryAdjunction l E f).unit.naturality (uniformizerPower l E Y n M)
  change uniformizerPower l E Y n M ≫ (ordinaryAdjunction l E f).unit.app M =
    (ordinaryAdjunction l E f).unit.app M ≫
      (ordinaryPush l E f).map ((ordinaryPull l E f).map (uniformizerPower l E Y n M)) at hn
  rw [← hn]
  ext V x
  change ((ordinaryAdjunction l E f).unit.app M).val.app V
      (uniformizerSection l E Y V ^ (n + 1) • x) =
    uniformizerSection l E X ((proEtaleBaseChange f).op.obj V) ^ (n + 1) •
      (show ((ordinaryPull l E f).obj M).val.obj ((proEtaleBaseChange f).op.obj V) from
        ((ordinaryAdjunction l E f).unit.app M).val.app V x)
  rw [map_smul]
  change (ordinaryCompletedRingMap l E f).hom.app V
      (uniformizerSection l E Y V ^ (n + 1)) •
        (show ((ordinaryPull l E f).obj M).val.obj ((proEtaleBaseChange f).op.obj V) from
          ((ordinaryAdjunction l E f).unit.app M).val.app V x) =
    uniformizerSection l E X ((proEtaleBaseChange f).op.obj V) ^ (n + 1) •
      (show ((ordinaryPull l E f).obj M).val.obj ((proEtaleBaseChange f).op.obj V) from
        ((ordinaryAdjunction l E f).unit.app M).val.app V x)
  rw [map_pow, completed_direct_uniformizer]

private theorem pull_quotientUnit_isCokernel {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) (M : Mod l E Y none) :
    ∃ h : uniformizerPower l E X n ((ordinaryPull l E f).obj M) ≫
        (ordinaryPull l E f).map ((quotientUnit l E Y n).app M) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((ordinaryPull l E f).map ((quotientUnit l E Y n).app M)) h)) := by
  obtain ⟨h, ⟨hc⟩⟩ := quotientUnit_isCokernel l E Y n M
  have : PreservesColimits (ordinaryPull l E f) :=
    (ordinaryAdjunction l E f).leftAdjoint_preservesColimits
  have h' : uniformizerPower l E X n ((ordinaryPull l E f).obj M) ≫
      (ordinaryPull l E f).map ((quotientUnit l E Y n).app M) = 0 := by
    rw [← pull_uniformizerPower, ← Functor.map_comp, h, Functor.map_zero]
  refine ⟨h', ⟨?_⟩⟩
  have hh := CokernelCofork.mapIsColimit _ hc (ordinaryPull l E f)
  have huE : Epi ((ordinaryPull l E f).map ((quotientUnit l E Y n).app M)) :=
    epi_of_isColimit_cofork hh
  apply CokernelCofork.IsColimit.ofπ' _ h'
  intro N g hg
  have hg' : (ordinaryPull l E f).map (uniformizerPower l E Y n M) ≫ g = 0 := by
    rw [pull_uniformizerPower]
    exact hg
  exact CokernelCofork.IsColimit.desc' hh g hg'

private theorem comparisonComponent_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) (M : Mod l E Y none) :
    ∃! e : (ordinaryPull l E f).obj ((ordinaryQuotientModule l E Y n).obj M) ≅
        (ordinaryQuotientModule l E X n).obj ((ordinaryPull l E f).obj M),
      (ordinaryPull l E f).map ((quotientUnit l E Y n).app M) ≫ e.hom =
        (quotientUnit l E X n).app ((ordinaryPull l E f).obj M) := by
  obtain ⟨hL, ⟨hcL⟩⟩ := pull_quotientUnit_isCokernel l E f n M
  obtain ⟨hX, ⟨hcX⟩⟩ := quotientUnit_isCokernel l E X n ((ordinaryPull l E f).obj M)
  let e := hcL.coconePointUniqueUpToIso hcX
  have he : (ordinaryPull l E f).map ((quotientUnit l E Y n).app M) ≫ e.hom =
      (quotientUnit l E X n).app ((ordinaryPull l E f).obj M) :=
    hcL.comp_coconePointUniqueUpToIso_hom hcX WalkingParallelPair.one
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  exact Cofork.IsColimit.hom_ext hcL (hd.trans he.symm)

private def quotientComparison {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ordinaryQuotientModule l E Y n ⋙ ordinaryPull l E f ≅
      ordinaryPull l E f ⋙ ordinaryQuotientModule l E X n :=
  NatIso.ofComponents
    (fun M ↦ (comparisonComponent_existsUnique l E f n M).exists.choose)
    (by
      intro M N a
      obtain ⟨hL, ⟨hcL⟩⟩ := pull_quotientUnit_isCokernel l E f n M
      apply Cofork.IsColimit.hom_ext hcL
      simp only [Cofork.π_ofπ, Functor.comp_map]
      change (ordinaryPull l E f).map ((quotientUnit l E Y n).app M) ≫
          (ordinaryPull l E f).map ((ordinaryQuotientModule l E Y n).map a) ≫ _ = _
      rw [← Category.assoc, ← Functor.map_comp, ← (quotientUnit l E Y n).naturality,
        Functor.map_comp, Category.assoc,
        (comparisonComponent_existsUnique l E f n N).exists.choose_spec,
        ← Category.assoc,
        (comparisonComponent_existsUnique l E f n M).exists.choose_spec]
      simpa only [Functor.id_map, ordinaryQuotientModule, Functor.comp_map] using
        (quotientUnit l E X n).naturality ((ordinaryPull l E f).map a))

private theorem quotientComparison_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) (M : Mod l E Y none) :
    (ordinaryPull l E f).map ((quotientUnit l E Y n).app M) ≫
        (quotientComparison l E f n).hom.app M =
      (quotientUnit l E X n).app ((ordinaryPull l E f).obj M) :=
  (comparisonComponent_existsUnique l E f n M).exists.choose_spec

private theorem generator_lift (W : Scheme.{t}) (n : ℕ) (M : Mod l E W none)
    (V : W.ProEtᵒᵖ) (r : (ring l E W none).obj.obj V) (x : M.val.obj V) :
    generator l E W none n M V ((projection l E W none n).hom.app V r) x =
      ((quotientUnit l E W n).app M).val.app V (r • x) := by
  rw [show ((quotientUnit l E W n).app M).val.app V (r • x) =
    generator l E W none n M V 1 (r • x) from unitModule_apply l E W none n M V _]
  unfold generator
  congr 2
  let : Module ((ring l E W none).obj.obj V) ((finite l E W none n).obj.obj V) :=
    Module.compHom _ ((projection l E W none n).hom.app V).hom
  rw [TensorProduct.tmul_smul]
  congr 1
  change (projection l E W none n).hom.app V r =
    (projection l E W none n).hom.app V r * 1
  exact (mul_one _).symm

/-- Pullback of a single finite quotient, normalized on adjunction-unit generators.

Source: Stacks Project, Modules on Sites, lemma-tensor-product-pullback (03EL),
and Cohomology on Sites, Tags 06YY and 07A4.
(blueprint: lem-fix-ordinary-quotient-module-comparison).
Proof: the normalized quotient unit M → Q_n tensor M is the cokernel of
multiplication by the (n+1)-st uniformizer power. Indeed, the completed projection
is surjective on sections and its kernel consists of multiples of that power.
The sheaf tensor quotient kernel calculation then gives the asserted cokernel
for every module, without flatness. The completed direct coefficient map preserves
constant integral scalars: test against every finite projection and use naturality
of constant-section maps. Consequently ordinary pullback takes the uniformizer
endomorphism of M to that of its pullback, by the specified module adjunction.
Pullback is additive and left adjoint, so it preserves these cokernels. Uniqueness
of cokernels gives the component isomorphisms preserving the quotient units;
the same universal property proves naturality. Lift an arbitrary finite section
a to a completed coefficient r. Tensor balancing writes a tensor x as the quotient
unit of r times x. Naturality and semilinearity of the ordinary adjunction unit,
together with the finite-projection square, give the displayed normalization.
For uniqueness transpose maps through ordinaryAdjunction and use pure-tensor
extensionality of reduction. No transition, complex, tower or derived comparison
is needed. This includes n=0, zero modules and the empty scheme. -/
theorem ordinaryQuotientModuleComparison
    {X Y : Scheme.{t}} (f : X ⟶ Y) [IsIso (ordinaryCoefficientMap l E f)] (n : ℕ) :
    ∃! e : ordinaryQuotientModule l E Y n ⋙ ordinaryPull l E f ≅
        ordinaryPull l E f ⋙ ordinaryQuotientModule l E X n,
      ∀ (M : Mod l E Y none) (V : Y.ProEt)
        (a : (finite l E Y none n).obj.obj (op V)) (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj V))
          (((ordinaryAdjunction l E f).unit.app
            ((ordinaryQuotientModule l E Y n).obj M)).val.app (op V)
              (generator l E Y none n M (op V) a x)) =
          generator l E X none n ((ordinaryPull l E f).obj M)
            (op ((proEtaleBaseChange f).obj V))
            ((ordinaryFiniteRingMap l E f n).hom.app (op V) a)
            (((ordinaryAdjunction l E f).unit.app M).val.app (op V) x) := by
  let e := quotientComparison l E f n
  have he : ∀ (M : Mod l E Y none) (V : Y.ProEt)
      (a : (finite l E Y none n).obj.obj (op V)) (x : M.val.obj (op V)),
      (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj V))
        (((ordinaryAdjunction l E f).unit.app
          ((ordinaryQuotientModule l E Y n).obj M)).val.app (op V)
            (generator l E Y none n M (op V) a x)) =
      generator l E X none n ((ordinaryPull l E f).obj M)
        (op ((proEtaleBaseChange f).obj V))
        ((ordinaryFiniteRingMap l E f n).hom.app (op V) a)
        (((ordinaryAdjunction l E f).unit.app M).val.app (op V) x) := by
    intro M V a x
    obtain ⟨r, rfl⟩ := projection_surjective l E Y n (op V) a
    rw [generator_lift]
    have hu := congrArg (fun h ↦ h.val.app (op V) (r • x))
      ((ordinaryAdjunction l E f).unit.naturality ((quotientUnit l E Y n).app M))
    change (((ordinaryAdjunction l E f).unit.app
        ((ordinaryQuotientModule l E Y n).obj M)).val.app (op V)
          (((quotientUnit l E Y n).app M).val.app (op V) (r • x))) =
      ((ordinaryPull l E f).map ((quotientUnit l E Y n).app M)).val.app
        (op ((proEtaleBaseChange f).obj V))
          (((ordinaryAdjunction l E f).unit.app M).val.app (op V) (r • x)) at hu
    rw [hu]
    have hc := congrArg (fun h ↦ h.val.app (op ((proEtaleBaseChange f).obj V))
      (((ordinaryAdjunction l E f).unit.app M).val.app (op V) (r • x)))
      (quotientComparison_unit l E f n M)
    change (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj V))
        (((ordinaryPull l E f).map ((quotientUnit l E Y n).app M)).val.app
          (op ((proEtaleBaseChange f).obj V))
            (((ordinaryAdjunction l E f).unit.app M).val.app (op V) (r • x))) = _ at hc
    rw [hc]
    have hp := congrArg (fun h ↦ h.hom.app (op V) r)
      ((ordinaryCompletedRingMap_existsUnique l E f).exists.choose_spec n)
    change (projection l E X none n).hom.app (op ((proEtaleBaseChange f).obj V))
        ((ordinaryCompletedRingMap l E f).hom.app (op V) r) =
      (ordinaryFiniteRingMap l E f n).hom.app (op V)
        ((projection l E Y none n).hom.app (op V) r) at hp
    rw [← hp, generator_lift]
    congr 1
    exact (((ordinaryAdjunction l E f).unit.app M).val.app (op V)).hom.map_smul r x
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((ordinaryAdjunction l E f).homEquiv _ _).injective
  apply unrestrictedReduction_hom_ext l E Y none n M
  intro V a x
  exact (hd M V.unop a x).trans (he M V.unop a x).symm

end WeilConjectures.IntegralOnSlice
