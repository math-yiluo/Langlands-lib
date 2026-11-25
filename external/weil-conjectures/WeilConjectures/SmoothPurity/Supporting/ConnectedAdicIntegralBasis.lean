/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralScalarData
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constant values and prescribed integral bases on connected schemes

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.2.12,
Definition 6.8.1 and Lemma 6.8.2(1), printed pp. 30 and 58--59
(blueprint: lem-pur-connected-adic-integral-basis).

The positive quotient exponent is n+1. The finite direct sum is represented by its
finite product in module sheaves. The basis is prescribed, rather than chosen by the theorem.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped BigOperators

namespace WeilConjectures

private def continuousRingPresheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj V := CommRingCat.of C(V.unop.left, A)
  map h := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom A A h.unop.left.base.hom).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def constantToContinuous (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ continuousRingPresheaf X A where
  app V := CommRingCat.ofHom (ContinuousMap.C : A →+* C(V.unop.left, A))
  naturality _ _ h := by ext; rfl

private theorem continuousRingPresheaf_isSheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousRingPresheaf X A) := by
  let G := forget CommRingCat.{max u (t + 1)}
  let : HasLimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink.{_, _, t + 1, t} _
  let : PreservesLimitsOfSize.{t, t + 1} G :=
    preservesLimitsOfSize_shrink.{t + 1, 0, t, max u (t + 1)} G
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (continuousRingPresheaf X A) G]
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology (continuousMapPresheaf A)
    ((isSheaf_fpqcTopology_continuousMapPresheaf A).of_le
      Scheme.proetaleTopology_le_fpqcTopology)

private theorem constantToContinuous_locallyInjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  equalizerSieve_mem {V} a b h := by
    classical
    by_cases he : IsEmpty V.unop.left
    · let _ := he
      exact (Scheme.ProEt.topology X).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology V.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp he
      have hab : a = b := congrArg (fun f : C(V.unop.left, A) ↦ f x) h
      subst b
      simp

private theorem constantToContinuous_locallySurjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  imageSieve_mem {V} f := by
    classical
    change C(V.left, A) at f
    let U (x : V.left) : V.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete {f x}).preimage f.continuous⟩
    let W (x : V.left) : X.ProEt := Scheme.ProEt.mk ((U x).ι ≫ V.hom)
    let i (x : V.left) : W x ⟶ V :=
      MorphismProperty.Over.homMk (U x).ι rfl
    have hm : Presieve.ofArrows W i ∈ Scheme.ProEt.precoverage X V := by
      change (Presieve.ofArrows W i).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
      · intro x
        change IsOpenImmersion (U x).ι
        infer_instance
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hm)
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨x⟩
    refine ⟨f x, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact y.property.symm

private theorem connected_constant_bijective (X : Scheme.{t}) [ConnectedSpace X]
    (A : Type (max u (t + 1))) [CommRing A] :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
        (op (Scheme.ProEt.mk (𝟙 X)))) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective
      CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)
  let F := continuousRingPresheaf X A
  let φ := constantToContinuous X A
  have hF : Presheaf.IsSheaf J F := continuousRingPresheaf_isSheaf X A
  have : Presheaf.IsLocallyInjective J φ := constantToContinuous_locallyInjective X A
  have : Presheaf.IsLocallySurjective J φ := constantToContinuous_locallySurjective X A
  have : IsIso ((presheafToSheaf J CommRingCat.{max u (t + 1)}).map φ) :=
    (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  have : IsIso (sheafifyMap J φ) := inferInstance
  let e : sheafify J P ≅ F := asIso (sheafifyMap J φ) ≪≫ (isoSheafify J hF).symm
  have he : toSheafify J P ≫ e.hom = φ := by
    dsimp [e]
    rw [← Category.assoc, ← toSheafify_naturality]
    simp only [toSheafify_naturality, isoSheafify_inv, Category.assoc,
      sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
    exact Category.comp_id φ
  let U := op (Scheme.ProEt.mk (𝟙 X))
  let θ : (sheafify J P).obj U ≃+* C(X, A) := (e.app U).commRingCatIsoToRingEquiv
  have hθ (a : A) : θ ((toSheafify J P).app U a) = ContinuousMap.const X a :=
    congrArg (fun k ↦ k.app U a) he
  let x : X := Classical.choice inferInstance
  constructor
  · intro a b h
    have hh := congrArg (fun z ↦ θ z x) h
    change θ ((toSheafify J P).app U a) x = θ ((toSheafify J P).app U b) x at hh
    simpa only [hθ, ContinuousMap.const_apply] using hh
  · intro s
    refine ⟨θ s x, θ.injective ?_⟩
    rw [hθ]
    apply ContinuousMap.ext
    intro y
    have hlc := (IsLocallyConstant.iff_continuous _).mpr (θ s).continuous
    exact hlc.apply_eq_of_preconnectedSpace x y

section
universe cs vs rs is js
private theorem ringSheafLimit_ext
    {C : Type cs} [Category.{vs} C] {J : GrothendieckTopology C}
    {I : Type is} [Category.{js} I] (D : I ⥤ Sheaf J RingCat.{rs})
    [HasLimit D] [PreservesLimit D (sheafToPresheaf J RingCat)]
    (U : Cᵒᵖ)
    [PreservesLimit (D ⋙ sheafToPresheaf J RingCat) ((evaluation _ _).obj U)]
    [PreservesLimit ((D ⋙ sheafToPresheaf J RingCat) ⋙ (evaluation _ _).obj U)
      (forget RingCat)]
    (x y : (limit D).obj.obj U)
    (h : ∀ i, ((limit.π D i).hom.app U) x = ((limit.π D i).hom.app U) y) : x = y := by
  let h₁ := isLimitOfPreserves (sheafToPresheaf J RingCat) (limit.isLimit D)
  let h₂ := isLimitOfPreserves ((evaluation _ _).obj U) h₁
  exact Concrete.isLimit_ext _ h₂ x y h

end

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t})

private noncomputable def scalarValue (U : Y.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  ((integralConstantToCompletionOfUniverses l E Y).hom.app U).hom.comp
    (((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom.comp
      ULift.ringEquiv.symm.toRingHom)

private theorem scalarValue_projection (U : Y.ProEtᵒᵖ)
    (x : Padic.coefficientExtensionIntegers l E) (n : ℕ) :
    (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U
      (scalarValue l E Y U x) = integralScalarFiniteConstant l E Y n U x := by
  have hc := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up x)))
    (limit.lift_π (integralConstantConeOfUniverses l E Y) (op n))
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  let B := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let q : A ⟶ B := CommRingCat.ofHom
    (RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
  have hn := congrArg (fun f ↦ f.app U (ULift.up x))
    (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))
  exact hc.trans hn.symm

private theorem scalarValue_naturality {U V : Y.ProEtᵒᵖ} (f : U ⟶ V)
    (x : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
      (scalarValue l E Y U x) = scalarValue l E Y V x := by
  let α := Functor.whiskerRight
    (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
    (forget₂ CommRingCat RingCat) ≫ (integralConstantToCompletionOfUniverses l E Y).hom
  exact (ConcreteCategory.congr_hom (α.naturality f) (ULift.up x)).symm

private noncomputable def finiteConstantEquiv [ConnectedSpace Y] (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) ≃+*
      (integralCoefficientSheaf l E Y n).obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) :=
  ULift.ringEquiv.symm.trans (RingEquiv.ofBijective
    ((toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op (Scheme.ProEt.mk (𝟙 Y)))).hom
    (connected_constant_bijective Y _))

private theorem finiteConstantEquiv_mk [ConnectedSpace Y] (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    finiteConstantEquiv l E Y n (Ideal.Quotient.mk _ a) =
      integralScalarFiniteConstant l E Y n (op (Scheme.ProEt.mk (𝟙 Y))) a := rfl

private theorem finiteConstantEquiv_transition [ConnectedSpace Y] (n : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 2)) :
    (integralCoefficientSheafTransition l E Y n).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y))) (finiteConstantEquiv l E Y (n + 1) a) =
      finiteConstantEquiv l E Y n (Padic.coefficientExtensionTransition l E (n + 1) a) := by
  let q : CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)))
  exact (congrArg (fun f ↦ f.app (op (Scheme.ProEt.mk (𝟙 Y))) (ULift.up a))
    (toSheafify_naturality (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))).symm

private noncomputable def residueValue [ConnectedSpace Y] (n : ℕ) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
      (op (Scheme.ProEt.mk (𝟙 Y))) →+* Padic.coefficientExtensionRing l E (n + 1) :=
  (finiteConstantEquiv l E Y n).symm.toRingHom.comp
    ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y)))).hom

private theorem residueValue_transition [ConnectedSpace Y] (n : ℕ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
      (op (Scheme.ProEt.mk (𝟙 Y)))) :
    Padic.coefficientExtensionTransition l E (n + 1) (residueValue l E Y (n + 1) x) =
      residueValue l E Y n x := by
  apply (finiteConstantEquiv l E Y n).injective
  rw [← finiteConstantEquiv_transition]
  simp only [residueValue, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have hw := limit.w (integralCoefficientSheafSystem l E Y)
    (homOfLE (Nat.le_succ n)).op
  have hm : (integralCoefficientSheafSystem l E Y).map
      (homOfLE (Nat.le_succ n)).op = integralCoefficientSheafTransition l E Y n := by
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
  rw [hm] at hw
  exact congrArg (fun f ↦ (f.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))).hom x) hw

private theorem scalarValue_bijective [ConnectedSpace Y] :
    Function.Bijective (scalarValue l E Y (op (Scheme.ProEt.mk (𝟙 Y)))) := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A)
  have hc := (Padic.finite_module_adic_complete_and_hom.{u, u, u} l E).1 A
  let : IsAdicComplete I A := AdicCompletion.of_bijective_iff.mp hc.2.1
  let S := (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
    (op (Scheme.ProEt.mk (𝟙 Y)))
  let f : (n : ℕ) → S →+* A ⧸ I ^ n
    | 0 => by
      have : Subsingleton (A ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
      exact
        { toFun := fun _ ↦ 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ ↦ Subsingleton.elim _ _
          map_zero' := rfl
          map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    | n + 1 => residueValue l E Y n
  have hf : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow I h).comp (f n) = f m := by
    intro m n h
    ext x
    apply Eq.symm
    apply Ideal.Quotient.eq_factor_of_eq_factor_succ
      (fun _ _ h ↦ Ideal.pow_le_pow_right h) (fun n ↦ f n x)
    · intro n
      cases n with
      | zero =>
        have : Subsingleton (A ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
        exact Subsingleton.elim _ _
      | succ n => exact (residueValue_transition l E Y n x).symm
    · exact h
  let g := (AdicCompletion.ofAlgEquiv I).symm.toRingHom.comp
    (AdicCompletion.liftRingHom I f hf)
  have hg (n : ℕ) (x : S) :
      Ideal.Quotient.mk (I ^ (n + 1)) (g x) = residueValue l E Y n x := by
    exact (AdicCompletion.mk_ofAlgEquiv_symm I (n + 1) _).trans
      (AdicCompletion.evalₐ_liftRingHom I f hf (n + 1) x)
  have hres (n : ℕ) (a : A) :
      residueValue l E Y n (scalarValue l E Y (op (Scheme.ProEt.mk (𝟙 Y))) a) =
        Ideal.Quotient.mk (I ^ (n + 1)) a := by
    apply (finiteConstantEquiv l E Y n).injective
    exact (finiteConstantEquiv l E Y n).apply_symm_apply _ |>.trans
      ((scalarValue_projection l E Y _ a n).trans (finiteConstantEquiv_mk l E Y n a).symm)
  constructor
  · intro a b hab
    apply congrFun (IsHausdorff.StrictMono.funext' I (f := fun _ : Unit ↦ a)
      (g := fun _ : Unit ↦ b) (a := Nat.succ) (fun _ _ h ↦ Nat.succ_lt_succ h) ?_) ()
    intro n _
    rw [← hres n a, ← hres n b, hab]
  · intro x
    refine ⟨g x, ?_⟩
    apply ringSheafLimit_ext (integralCoefficientSheafSystem l E Y) _
    rintro ⟨n⟩
    have hp := scalarValue_projection l E Y (op (Scheme.ProEt.mk (𝟙 Y))) (g x) n
    change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app _).hom
      (scalarValue l E Y _ (g x)) = _ at hp
    refine hp.trans ?_
    have h := congrArg (finiteConstantEquiv l E Y n) (hg n x)
    change finiteConstantEquiv l E Y n (Ideal.Quotient.mk _ (g x)) = _ at h
    rw [finiteConstantEquiv_mk] at h
    dsimp only [residueValue, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at h
    rw [RingEquiv.apply_symm_apply] at h
    exact h

private theorem scalarValue_map
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (U : Y.ProEtᵒᵖ) (x : Padic.coefficientExtensionIntegers l E) :
    (completedCoefficientMap l E L ι Y).hom.app U (scalarValue l E Y U x) =
      scalarValue l L Y U (integralScalarIntegerInclusion l E L ι x) := by
  apply ringSheafLimit_ext (integralCoefficientSheafSystem l L Y) U
  intro n
  have hφ := congrArg (fun f ↦ f.hom.app U (scalarValue l E Y U x))
    ((completedCoefficientMap_existsUnique l E L ι Y).exists.choose_spec n.unop)
  change (completedIntegralCommRingProjectionUnrestricted l L Y n.unop).hom.app U
    ((completedCoefficientMap l E L ι Y).hom.app U (scalarValue l E Y U x)) =
    (integralScalarQuotientSheafMap l E L ι Y n.unop).hom.app U
      ((completedIntegralCommRingProjectionUnrestricted l E Y n.unop).hom.app U
        (scalarValue l E Y U x)) at hφ
  erw [hφ, scalarValue_projection, scalarValue_projection]
  let q : CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))) ⟶
      CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l L (n.unop + 1))) :=
    CommRingCat.ofHom (RingHom.ulift (integralScalarQuotientMap l E L ι n.unop))
  have hn := congrArg (fun f ↦ f.app U
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)) x)))
    (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))
  exact hn.symm

section FreeDetection
universe ca cv cr
variable {C : Type ca} [Category.{cv} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{cr}) (T : C) (hT : IsTerminal T)
include hT

end FreeDetection

end WeilConjectures
