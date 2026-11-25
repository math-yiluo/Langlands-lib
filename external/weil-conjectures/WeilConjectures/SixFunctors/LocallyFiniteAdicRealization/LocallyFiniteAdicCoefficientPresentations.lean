/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import all WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeLocal

/-! # Coefficient and section transport for the native adic realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

section PresentationConstruction
set_option synthInstance.maxSize 2048

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem tower_step (n : ℕ) :
    (finiteCoefficientTower l X E ⋙
      sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (homOfLE (Nat.le_succ n)).op = integralCoefficientSheafTransition l E X n := by
  let q : finiteCoefficientRing l E (n + 1) ⟶ finiteCoefficientRing l E n :=
    CommRingCat.ofHom (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)))
  have h : finiteCoefficientRingMap l E (Nat.le_succ n) = q := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn' with
    | h x => rfl
  exact congrArg (fun f ↦
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map f)) h

private def towerIso :
    finiteCoefficientTower l X E ⋙
      sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≅
      integralCoefficientSheafSystem l E X := by
  let a : finiteCoefficientTower l X E ⋙
      sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⟶
      integralCoefficientSheafSystem l E X := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simp only [Category.comp_id, Category.id_comp, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact tower_step l X E n)
  exact NatIso.ofComponents (fun n ↦ Iso.refl _) (fun f ↦ a.naturality f)

private def completionIso : finiteCoefficientLimit l X E ≅
    completedIntegralCommRingSheafUnrestricted l E X := by
  let F := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  exact F.preimageIso (X := finiteCoefficientLimit l X E)
    (Y := completedIntegralCommRingSheafUnrestricted l E X)
    (preservesLimitIso F (finiteCoefficientTower l X E) ≪≫
      HasLimit.isoOfNatIso (towerIso l X E))

@[reassoc] private theorem completionIso_projection (n : ℕ) :
    (completionIso l X E).hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
      limit.π (finiteCoefficientTower l X E) (op n) := by
  let F := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  have hp : F.map (completedIntegralCommRingProjectionUnrestricted l E X n) =
      limit.π (integralCoefficientSheafSystem l E X) (op n) := rfl
  rw [Functor.map_comp, hp]
  unfold completionIso
  erw [Functor.preimageIso_hom, Functor.map_preimage]
  erw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  simp only [towerIso, NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
  exact preservesLimitIso_hom_π _ _ _

variable [IsCommMonObj (abRing l X)]
private theorem native_mul (U : X.ProEtᵒᵖ) (a b : (ringSheaf l X).obj.obj U) :
    (a * b).down.1 = a.down.1 * b.down.1 := by
  have h := CategoryTheory.ScalarForgetting.sectionRing_mul
    (ProEt.topology X) (ULift.{u + 1} (PadicAlgCl l)) (ProEtale.adicConstantSheaf l X) U a b
  change a * b = ((Functor.LaxMonoidal.μ
    (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l)) _ _ ≫
      (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l)).map
        CategoryTheory.MonObj.mul).app U) (a ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] b) at h
  rw [Sheaf.μ_comp_map_mul] at h
  exact congrArg (fun s ↦ s.down.1) (h.trans
    (ProEtale.adicConstantSheaf_mul_app_tmul X a b))

private theorem native_one (U : X.ProEtᵒᵖ) :
    ((1 : (ringSheaf l X).obj.obj U).down.1 : C(U.unop.left, PadicAlgCl l)) = 1 := by
  let b : (ringSheaf l X).obj.obj U := ULift.up
    ⟨ContinuousMap.const U.unop.left 1, PadicAlgCl.const_mem_locallyFiniteFunctions 1⟩
  apply ContinuousMap.ext
  intro x
  have h := congrArg (fun s : (ringSheaf l X).obj.obj U ↦ s.down.1 x) (one_mul b)
  rw [native_mul] at h
  change (1 : (ringSheaf l X).obj.obj U).down.1 x * 1 = 1 at h
  simpa only [mul_one, ContinuousMap.one_apply] using h

private def rationalNativeInclusion (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    rationalCoefficientSheaf l X E ⟶ ringSheaf l X := by
  letI := coefficientExtensionNormedField l E
  let f : AbsoluteValue E ℝ :=
    (NormedField.toAbsoluteValue (PadicAlgCl l)).comp i.toRingHom.injective
  have hf (a : ℚ_[l]) : f (algebraMap ℚ_[l] E a) = ‖a‖ := by
    change ‖i (algebraMap ℚ_[l] E a)‖ = ‖a‖
    rw [i.commutes]
    exact PadicAlgCl.norm_extends l a
  have hi : Continuous i := by
    apply Isometry.continuous
    apply AddMonoidHomClass.isometry_of_norm i
    exact spectralNorm_unique_field_norm_ext hf

  let val (U : X.ProEtᵒᵖ) (s : C(U.unop.left, ULift.{u + 1, u} E)) :
      C(U.unop.left, PadicAlgCl l) :=
    ⟨fun x ↦ i (s x).down, hi.comp (continuous_uliftDown.comp s.continuous)⟩
  have hf (U : X.ProEtᵒᵖ) (s : C(U.unop.left, ULift.{u + 1, u} E)) :
      val U s ∈ PadicAlgCl.locallyFiniteFunctions l U.unop.left := by
    apply PadicAlgCl.mem_locallyFiniteFunctions_of_finiteDimensional
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range i.toLinearMap)
    apply Submodule.span_le.mpr
    rintro y ⟨x, rfl⟩
    exact ⟨(s x).down, rfl⟩
  let φ (U : X.ProEtᵒᵖ) : (rationalCoefficientSheaf l X E).obj.obj U →+*
      (ringSheaf l X).obj.obj U := by
    refine {
      toFun := fun s ↦ ULift.up ⟨val U s, hf U s⟩
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
    · apply ULift.ext
      apply Subtype.ext
      rw [native_one]
      ext x
      exact i.map_one
    · intro a b
      apply ULift.ext
      apply Subtype.ext
      erw [native_mul]
      ext x
      exact i.map_mul _ _
    · apply ULift.ext
      apply Subtype.ext
      ext x
      exact i.map_zero
    · intro a b
      apply ULift.ext
      apply Subtype.ext
      ext x
      exact i.map_add _ _
  refine ⟨{ app := fun U ↦ (ConcreteCategory.ofHom (C := CommRingCat)
      (X := (rationalCoefficientSheaf l X E).obj.obj U)
      (Y := (ringSheaf l X).obj.obj U) (φ U)), naturality := ?_ }⟩
  intro U V f
  ext s
  rfl

private theorem presentation_exists (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    Nonempty (CoefficientPresentation l X E i) := by
  classical
  obtain ⟨a, ha⟩ := continuousCoefficientCompletion l E X
  choose q hq hr using ha
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  refine ⟨{ integral := a ≪≫ completionIso l X E
            finite := q
            finite_constants := hq
            integral_residues := ?_
            localization := b
            localization_normalized := hb
            integralInclusion := integralRationalCoefficientMap l E X
            integralInclusion_normalized := integralRationalCoefficientMap_normalized l E X
            rationalInclusion := rationalNativeInclusion l X E i
            rationalInclusion_normalized := ?_ }⟩
  · intro n U s x
    have h := hr n U s x
    rw [Iso.trans_hom, Category.assoc, completionIso_projection_assoc]
    exact h
  · intro U s x
    rfl

private theorem finite_hom_eq {i : E →ₐ[ℚ_[l]] PadicAlgCl l}
    (C : CoefficientPresentation l X E i) (n : ℕ) :
    (C.finite n).hom = (discreteContinuousCoefficientIso X).hom.app
      (finiteCoefficientRing l E n) := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))
    (finiteContinuousCoefficientSheaf l X E n)).injective
  change toSheafify (ProEt.topology X) _ ≫ (C.finite n).hom.hom =
    toSheafify (ProEt.topology X) _ ≫ (continuousCoefficientConstantComparison X
      (finiteCoefficientRing l E n)).hom
  rw [continuousCoefficientConstantComparison_unit]
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply ContinuousMap.ext
  intro x
  exact C.finite_constants n U a x

@[reassoc] private theorem presentation_reduction {i : E →ₐ[ℚ_[l]] PadicAlgCl l}
    (C : CoefficientPresentation l X E i) (n : ℕ) :
    C.integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n ≫
      (C.finite n).hom = continuousCoefficientReduction l E X n := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  exact C.integral_residues n U s x

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)

private def continuousIntegralScalarMap :
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l X E ⟶
      AlgebraicGeometry.Scheme.integralCoefficientSheaf l X L := by
  letI := coefficientExtensionNormedField l E
  letI := coefficientExtensionNormedField l L
  have hi : Continuous ι := by
    apply Isometry.continuous
    apply AddMonoidHomClass.isometry_of_norm ι
    exact integralScalar_absoluteValue l E L ι
  let φ : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l L) :=
    RingHom.ulift (integralScalarIntegerInclusion l E L ι)
  have hc : Continuous φ := continuous_uliftUp.comp
    ((hi.comp continuous_subtype_val).subtype_mk _ |>.comp continuous_uliftDown)
  exact continuousCoefficientMap φ hc X

private theorem finite_scalar {i : E →ₐ[ℚ_[l]] PadicAlgCl l}
    {j : L →ₐ[ℚ_[l]] PadicAlgCl l}
    (C : CoefficientPresentation l X E i) (D : CoefficientPresentation l X L j) (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι X n ≫ (D.finite n).hom =
      (C.finite n).hom ≫ (discreteContinuousCoefficientFunctor X).map
        (CommRingCat.ofHom (RingHom.ulift (integralScalarQuotientMap l E L ι n))) := by
  rw [finite_hom_eq, finite_hom_eq]
  exact discreteConstantComparison_naturality X
    (CommRingCat.ofHom (RingHom.ulift (integralScalarQuotientMap l E L ι n)))

private theorem integral_scalar {i : E →ₐ[ℚ_[l]] PadicAlgCl l}
    {j : L →ₐ[ℚ_[l]] PadicAlgCl l}
    (C : CoefficientPresentation l X E i) (D : CoefficientPresentation l X L j) :
    C.integral.inv ≫ continuousIntegralScalarMap l X E L ι ≫ D.integral.hom =
      completedCoefficientMap l E L ι X := by
  apply (completedCoefficientMap_existsUnique l E L ι X).unique
  · intro n
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    let : TopologicalSpace (finiteCoefficientRing l L n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l L n) := ⟨rfl⟩
    apply (cancel_epi C.integral.hom).mp
    apply (cancel_mono (D.finite n).hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    erw [presentation_reduction l X L D n, finite_scalar l X E L ι C D n,
      presentation_reduction_assoc l X E C n]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply ContinuousMap.ext
    intro x
    rfl
  · exact (completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec

private theorem presentation_scalar {i : E →ₐ[ℚ_[l]] PadicAlgCl l}
    {j : L →ₐ[ℚ_[l]] PadicAlgCl l}
    (C : CoefficientPresentation l X E i) (D : CoefficientPresentation l X L j)
    (h : j.comp ι = i) :
    completedCoefficientMap l E L ι X ≫ D.integralMap l X = C.integralMap l X := by
  rw [← integral_scalar l X E L ι C D]
  apply (cancel_epi C.integral.hom).mp
  simp only [CoefficientPresentation.integralMap, Category.assoc, Iso.hom_inv_id_assoc]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (D.rationalInclusion.hom.app U
    (D.integralInclusion.hom.app U
      ((continuousIntegralScalarMap l X E L ι).hom.app U s))).down.1 x =
    (C.rationalInclusion.hom.app U (C.integralInclusion.hom.app U s)).down.1 x
  erw [D.rationalInclusion_normalized, C.rationalInclusion_normalized]
  erw [D.integralInclusion_normalized U.unop, C.integralInclusion_normalized U.unop]
  change j (ι (integralCoefficientValue l E X U s x)) =
    i (integralCoefficientValue l E X U s x)
  exact congrArg (fun k : E →ₐ[ℚ_[l]] PadicAlgCl l ↦
    k (integralCoefficientValue l E X U s x)) h

end PresentationConstruction

set_option backward.isDefEq.respectTransparency false in
/-- Finite-field continuous coefficient presentations, compatible with field inclusion.

Source: Bhatt--Scholze, Lemma 6.8.2; native realization proof step 2
(blueprint: lem-sf-locally-finite-adic-coefficient-presentations).

Proof in words: for each positive residue quotient, the constant-sheaf comparison to
continuous functions is an isomorphism: locally a discrete-valued function is constant,
and constants are locally injective. Use these comparisons as the finite components.
Both the completed integral ring sheaf and the sheaf of continuous integral functions
are limits of this same residue tower. The unique comparison of limiting cones gives
the integral isomorphism and its residue normalization. Localizing the integral function
sheaf at a uniformizer gives the rational function sheaf: each continuous rational
function is locally bounded, so locally some uniformizer power makes it integral.
The integral inclusion and localization comparison have the specified pointwise values.
Postcomposition by the displayed finite-field embedding gives rational inclusion into
the native ring: its range lies in a finite-dimensional subspace, hence is locally finite.
These maps are natural on site objects. Their pointwise definitions preserve zero, one,
addition and multiplication. For a finite-field extension, evaluation of the completed
scalar map followed by native inclusion is the original embedded rational function.
For each target residue precision, use continuity of integral field inclusion to
choose a source precision whose ideal maps into the target ideal. Compare at that
precision using the defining completed scalar map and the integral comparison. The
comparison is unchanged on deepening the source precision, including ramified field
extensions. Joint injectivity of the target projections identifies the integral section.
Composition of the two field embeddings is the original embedding,
which proves the scalar equation. All pointwise and limiting arguments include the
empty site object and repeated fields without any nonemptiness assumption.
-/
theorem coefficientPresentations_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsCommMonObj (abRing l X)] :
    ∃ coefficient : ∀ E : Index l (PadicAlgCl l),
      CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E),
      ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
        completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
          (coefficient L).integralMap l X = (coefficient E).integralMap l X := by
  classical
  let coefficient (E : Index l (PadicAlgCl l)) :=
    Classical.choice (presentation_exists l X (Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E))
  refine ⟨coefficient, ?_⟩
  intro E L h
  apply presentation_scalar l X (Coefficient.{u} l (PadicAlgCl l) E)
    (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
    (coefficient E) (coefficient L)
  ext a
  simp [embedding, coefficientInclusion]

end WeilConjectures.LocallyFiniteAdicRealization
