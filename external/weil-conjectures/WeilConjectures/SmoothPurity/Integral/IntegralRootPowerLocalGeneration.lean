/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Local generation of integral root tensor powers

The recursive scalar/root sections locally span every completed integral root tensor
power, and maps out of such a power are determined by their values on them.

Source: Stacks, Modules on Sites, Tags 03EK and 03EL
(blueprint: lem-weil-integral-root-power-generators-local-span,
lem-weil-integral-root-power-generators-local-ext).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures

/-- A family of sections is locally spanning when every section becomes a finite
linear combination of the displayed family after a covering sieve. -/
structure IntegralRootPowerLocallySpans
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (G : ∀ (d : ℕ) (V : T.ProEtᵒᵖ)
      (_a : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj V),
      (Fin d → (purTwistZlOne T l).obj.obj V) →
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) d).val.obj V) where
  local_span : ∀ (d : ℕ) (U : T.ProEtᵒᵖ)
    (z : (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
      (purTwistIntegralModule T l E) d).val.obj U),
    ∃ S : Sieve U.unop, S ∈ ProEt.topology T U.unop ∧
      ∀ (V : T.ProEt) (i : V ⟶ U.unop), S.arrows i →
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) d).val.map i.op z ∈
          Submodule.span
            (((sheafCompose (ProEt.topology T)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (completedIntegralCommRingSheafUnrestricted l E T)).obj.obj
              (Opposite.op V))
            (Set.range (fun q : (((sheafCompose (ProEt.topology T)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (completedIntegralCommRingSheafUnrestricted l E T)).obj.obj
                (Opposite.op V)) ×
              (Fin d → (purTwistZlOne T l).obj.obj (Opposite.op V)) ↦
              G d (Opposite.op V) q.1 q.2))

section RootFormulas
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private abbrev rootLine (d : ℕ) :=
  coefficientTwistPower X
    (R := completedIntegralCommRingSheafUnrestricted l E X)
    (purTwistIntegralModule X l E) d

/-- The recursive root generators (the formulas of the hypotheses `hzero`, `hone`,
`hsucc`). -/
private def rootGen (W : X.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj W) :
    (d : ℕ) → (Fin d → (purTwistZlOne X l).obj.obj W) → (rootLine l E X d).val.obj W
  | 0, _ => a
  | 1, x => @SMul.smul _ _ (purTwistIntegralAction X l E W).toSMul a
      (purTwistIntegralTensor X l E W 1 (x 0))
  | d + 2, x => siteSheafTensorTmul
      (rootLine l E X (d + 1)) (purTwistIntegralModule X l E) W
      (rootGen W a (d + 1) (fun i ↦ x i.castSucc))
      (purTwistIntegralTensor X l E W 1 (x (Fin.last (d + 1))))

private theorem rootGen_snoc (U : X.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin (d + 1) → (purTwistZlOne X l).obj.obj U)
    (z : (purTwistZlOne X l).obj.obj U) :
    rootGen l E X U a (d + 2) (Fin.snoc x z) =
      siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (rootGen l E X U a (d + 1) x)
        (purTwistIntegralTensor X l E U 1 z) := by
  simp only [rootGen, Fin.snoc_castSucc, Fin.snoc_last]

private theorem rootTensor_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (purTwistZlOne X l).obj.obj U) :
    (purTwistIntegralModule X l E).val.map f (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlOne X l).obj.map f x) := by
  change (purTwistIntegralOne X l E).val.map f
    (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlModule X l).val.map f x)
  have h := scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l)) f 1 x
  rw [map_one] at h
  exact h

private theorem rootGen_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    (rootLine l E X d).val.map f (rootGen l E X U a d x) =
      rootGen l E X V
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map f a) d
        (fun i ↦ (purTwistZlOne X l).obj.map f (x i)) := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    change (purTwistIntegralModule X l E).val.map f
      (@SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul a
            (purTwistIntegralTensor X l E U 1 (x 0))) = _
    erw [(purTwistIntegralModule X l E).val.map_smul, rootTensor_restrict]
    rfl
  | more d _ ih =>
    let M := rootLine l E X (d + 1)
    let L := purTwistIntegralModule X l E
    exact (scalarTensorTmul_naturality
      (R := completedIntegralCommRingSheafUnrestricted l E X) M L f
        (rootGen l E X U a (d + 1) (fun i ↦ x i.castSucc))
        (purTwistIntegralTensor X l E U 1 (x (Fin.last (d + 1))))).trans
      (congrArg₂ (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M L V) (ih (fun i ↦ x i.castSucc))
        (rootTensor_restrict l E X f (x (Fin.last (d + 1)))))

private def rootSpan (d : ℕ) (U : X.ProEtᵒᵖ) :
    Submodule ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
      ((rootLine l E X d).val.obj U) :=
  Submodule.span _ (Set.range (fun q :
    ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U) ×
      (Fin d → (purTwistZlOne X l).obj.obj U) ↦ rootGen l E X U q.1 d q.2))

private theorem rootSpan_restrict (d : ℕ) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (rootLine l E X d).val.obj U) (hx : x ∈ rootSpan l E X d U) :
    (rootLine l E X d).val.map f x ∈ rootSpan l E X d V := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, z⟩, rfl⟩ := hx
    erw [rootGen_restrict]
    exact Submodule.subset_span ⟨(_, _), rfl⟩
  | zero => simpa only [map_zero] using (rootSpan l E X d V).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    erw [(rootLine l E X d).val.map_smul]
    exact Submodule.smul_mem _ _ hx

private def rootSpanSieve (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X d).val.obj U) : Sieve U.unop where
  arrows V f := (rootLine l E X d).val.map f.op x ∈ rootSpan l E X d (op V)
  downward_closed := by
    intro V W f hf g
    simpa only [op_comp, PresheafOfModules.map_comp_apply] using
      rootSpan_restrict l E X d g.op _ hf

private def rootLocalSpan (d : ℕ) (U : X.ProEtᵒᵖ) :
    Submodule ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
      ((rootLine l E X d).val.obj U) where
  carrier := {x | rootSpanSieve l E X d U x ∈ ProEt.topology X U.unop}
  zero_mem' := by
    apply (ProEt.topology X).superset_covering _ ((ProEt.topology X).top_mem _)
    intro V f _
    change (rootLine l E X d).val.map f.op 0 ∈ rootSpan l E X d (op V)
    simpa only [map_zero] using (rootSpan l E X d (op V)).zero_mem
  add_mem' := by
    intro x y hx hy
    apply (ProEt.topology X).superset_covering _
      ((ProEt.topology X).intersection_covering hx hy)
    intro V f hf
    change (rootLine l E X d).val.map f.op (x + y) ∈ _
    simpa only [map_add] using (rootSpan l E X d (op V)).add_mem hf.1 hf.2
  smul_mem' := by
    intro a x hx
    apply (ProEt.topology X).superset_covering _ hx
    intro V f hf
    change (rootLine l E X d).val.map f.op (a • x) ∈ _
    erw [(rootLine l E X d).val.map_smul]
    exact Submodule.smul_mem _ _ hf

private theorem span_mem_rootLocalSpan (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X d).val.obj U) (hx : x ∈ rootSpan l E X d U) :
    x ∈ rootLocalSpan l E X d U := by
  apply (ProEt.topology X).superset_covering _ ((ProEt.topology X).top_mem _)
  intro V f _
  exact rootSpan_restrict l E X d f.op x hx

private theorem rootLocalSpan_descent (d : ℕ)
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (φ : P ⟶ (rootLine l E X d).val.presheaf)
    [Presheaf.IsLocallySurjective (ProEt.topology X) φ]
    (h : ∀ U t, φ.app U t ∈ rootLocalSpan l E X d U)
    (U : X.ProEtᵒᵖ) (x : (rootLine l E X d).val.obj U) :
    x ∈ rootLocalSpan l E X d U := by
  apply (ProEt.topology X).transitive (Presheaf.imageSieve_mem _ φ x)
  rintro V f ⟨t, ht⟩
  change φ.app (op V) t = (rootLine l E X d).val.map f.op x at ht
  have he : (rootSpanSieve l E X d U x).pullback f =
      rootSpanSieve l E X d (op V) (φ.app (op V) t) := by
    ext W g
    change ((rootLine l E X d).val.map (g ≫ f).op x ∈ _) ↔ _
    erw [op_comp, PresheafOfModules.map_comp_apply, ← ht]
    rfl
  erw [he]
  exact h (op V) t

private theorem rootTensor_mem_span (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X (d + 1)).val.obj U)
    (y : (rootLine l E X 1).val.obj U)
    (hx : x ∈ rootSpan l E X (d + 1) U)
    (hy : y ∈ rootSpan l E X 1 U) :
    siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U x y ∈
      rootSpan l E X (d + 2) U := by
  induction hx using Submodule.span_induction with
  | zero =>
    simpa only [scalarTensorTmul_zero_first] using (rootSpan l E X (d + 2) U).zero_mem
  | add x x' _ _ hx hx' =>
    simpa only [scalarTensorTmul_add_first] using Submodule.add_mem _ hx hx'
  | smul a x _ hx =>
    exact (congrArg (fun z ↦ z ∈ rootSpan l E X (d + 2) U)
      (scalarTensorTmul_smul_first
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (rootLine l E X (d + 1)) (rootLine l E X 1) U a x y)).mpr
          (Submodule.smul_mem _ a hx)
  | mem x hx =>
    obtain ⟨⟨a, z⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | zero =>
      simpa only [siteSheafTensorTmul, TensorProduct.tmul_zero, map_zero] using
        (rootSpan l E X (d + 2) U).zero_mem
    | add y y' _ _ hy hy' =>
      simpa only [siteSheafTensorTmul, TensorProduct.tmul_add, map_add] using
        Submodule.add_mem _ hy hy'
    | smul b y _ hy =>
      exact (congrArg (fun z ↦ z ∈ rootSpan l E X (d + 2) U)
        (scalarTensorTmul_smul_second
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          (rootLine l E X (d + 1)) (rootLine l E X 1) U b
          (rootGen l E X U a (d + 1) z) y)).mpr (Submodule.smul_mem _ b hy)
    | mem y hy =>
      obtain ⟨⟨b, w⟩, rfl⟩ := hy
      exact (congrArg (fun t ↦ t ∈ rootSpan l E X (d + 2) U)
        (scalarTensorTmul_smul_second
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          (rootLine l E X (d + 1)) (rootLine l E X 1) U b
          (rootGen l E X U a (d + 1) z)
          (purTwistIntegralTensor X l E U 1 (w 0)))).mpr
        (Submodule.smul_mem _ b (Submodule.subset_span
          ⟨(a, Fin.snoc z (w 0)), rootGen_snoc l E X U a d z (w 0)⟩))

private theorem rootTensor_mem_localSpan (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X (d + 1)).val.obj U)
    (y : (rootLine l E X 1).val.obj U)
    (hx : x ∈ rootLocalSpan l E X (d + 1) U) (hy : y ∈ rootLocalSpan l E X 1 U) :
    siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U x y ∈
      rootLocalSpan l E X (d + 2) U := by
  apply (ProEt.topology X).superset_covering _
    ((ProEt.topology X).intersection_covering hx hy)
  intro V f hf
  exact (congrArg (fun z ↦ z ∈ rootSpan l E X (d + 2) (op V))
    (scalarTensorTmul_naturality
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (rootLine l E X (d + 1)) (rootLine l E X 1) f.op x y)).mpr
        (rootTensor_mem_span l E X d (op V) _ _ hf.1 hf.2)

private theorem integralTensor_rootGen (U : X.ProEtᵒᵖ)
    (b : (purTwistIntegralConstant X l E).obj.obj U)
    (x : (purTwistZlOne X l).obj.obj U) :
    purTwistIntegralTensor X l E U b x =
      rootGen l E X U ((purTwistIntegralCompletionMap X l E).hom.app U b) 1
        (fun _ ↦ x) := by
  have h := (purTwistIntegralAction_existsUnique X l E).exists.choose_spec.2.1 U b
    (purTwistIntegralTensor X l E U 1 x)
  change _ = @SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul _ _
  erw [show @SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul _ _ = _ from h]
  dsimp only [purTwistIntegralTensor]
  erw [← map_smul]
  congr 1
  let N := ((SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l))
  simpa only [mul_one] using
    (ModuleCat.ExtendScalars.smul_tmul
      ((purTwistConstantIntegersMap X l E).hom.app U).hom
      (M := N.val.obj U) b 1 x).symm

private theorem first_rootLocalSpan (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X 1).val.obj U) : x ∈ rootLocalSpan l E X 1 U := by
  let P := changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l))
  let φ := (PresheafOfModules.toPresheaf _).map
    (scalarSheafificationUnit (J := ProEt.topology X) P)
  have : Presheaf.IsLocallySurjective (ProEt.topology X) φ := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ P.presheaf)
    infer_instance
  apply rootLocalSpan_descent l E X 1 P.presheaf φ _ U x
  intro V t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | tmul b z =>
    apply span_mem_rootLocalSpan
    change purTwistIntegralTensor X l E V b z ∈ _
    erw [integralTensor_rootGen]
    exact Submodule.subset_span ⟨(_, _), rfl⟩

private theorem rootGen_locally_span (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X d).val.obj U) : x ∈ rootLocalSpan l E X d U := by
  induction d using Nat.twoStepInduction generalizing U with
  | zero =>
    apply span_mem_rootLocalSpan
    exact Submodule.subset_span ⟨(x, Fin.elim0), rfl⟩
  | one => exact first_rootLocalSpan l E X U x
  | more d _ hd =>
    let P := siteTensorPresheaf (rootLine l E X (d + 1)).val
      (purTwistIntegralModule X l E).val
    let φ := (PresheafOfModules.toPresheaf _).map
      (scalarSheafificationUnit (J := ProEt.topology X) P)
    have : Presheaf.IsLocallySurjective (ProEt.topology X) φ := by
      change Presheaf.IsLocallySurjective _ (toSheafify _ P.presheaf)
      infer_instance
    apply rootLocalSpan_descent l E X (d + 2) P.presheaf φ _ U x
    intro V t
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | tmul a b =>
      apply rootTensor_mem_localSpan l E X d V a b (hd V a)
      exact first_rootLocalSpan l E X V b

end RootFormulas

/-- The recursive root formulas locally span every positive tensor power.
Source: Stacks, Modules on Sites, Tags 03EK and 03EL; the tensor-sheafification
argument in the proof of local generation.
(blueprint: lem-weil-integral-root-power-generators-local-span).
Proof: degree zero is the coefficient sheaf. In degree one, use the
sheafification unit for scalar extension and the tensor-product induction. For
higher degrees, refine the local spans of the two factors to a common cover,
expand bilinearly, and use the recursion equation for G. The sieve formulation
records exactly the local descent needed by the sheaf separatedness argument. -/
theorem integralRootPower_local_spanning
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (G : ∀ (d : ℕ) (V : T.ProEtᵒᵖ)
      (_a : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj V),
      (Fin d → (purTwistZlOne T l).obj.obj V) →
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) d).val.obj V)
    (hzero : ∀ V a x, G 0 V a x = a)
    (hone : ∀ V a x, G 1 V a (fun _ ↦ x) =
      @SMul.smul _ _ (purTwistIntegralAction T l E V).toSMul a
          (purTwistIntegralTensor T l E V 1 x))
    (hsucc : ∀ d V a x, G (d + 2) V a x =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) (d + 1))
        (purTwistIntegralModule T l E) V (G (d + 1) V a (fun i ↦ x i.castSucc))
        (purTwistIntegralTensor T l E V 1 (x (Fin.last (d + 1))))) :
    IntegralRootPowerLocallySpans l E T G := by
  have hG : ∀ d V a x, G d V a x = rootGen l E T V a d x := by
    intro d
    induction d using Nat.twoStepInduction with
    | zero => exact hzero
    | one =>
      intro V a x
      have hx : x = fun _ ↦ x 0 := funext fun i ↦ congrArg x (Subsingleton.elim i 0)
      exact (congrArg (G 1 V a) hx).trans (hone V a (x 0))
    | more d _ ih =>
      intro V a x
      rw [hsucc, ih]
      rfl
  refine ⟨fun d U z ↦ ⟨_, rootGen_locally_span l E T d U z, ?_⟩⟩
  intro V i hi
  have hrange : (Set.range (fun q :
      ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V)) ×
        (Fin d → (purTwistZlOne T l).obj.obj (op V)) ↦ G d (op V) q.1 q.2)) =
      Set.range (fun q :
      ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V)) ×
        (Fin d → (purTwistZlOne T l).obj.obj (op V)) ↦ rootGen l E T (op V) q.1 d q.2) := by
    congr 1
    funext q
    exact hG d (op V) q.1 q.2
  change _ ∈ rootSpan l E T d (op V) at hi
  unfold rootSpan at hi
  erw [hrange]
  exact hi

/-- Local spanning of the prescribed sections implies extensionality of maps.
The generation assertion is the strictly smaller geometric part of the argument.
Source: Stacks, Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-weil-integral-root-power-generators-local-ext).
Proof: use sheaf extensionality and separatedness of the target. On each member
of the covering sieve supplied by local spanning, induct on the submodule span;
linearity reduces the equality to the displayed generators, where the
hypothesis h applies. -/
theorem integralRootPower_hom_ext_of_locallySpans
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (G : ∀ (d : ℕ) (V : T.ProEtᵒᵖ)
      (_a : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj V),
      (Fin d → (purTwistZlOne T l).obj.obj V) →
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) d).val.obj V)
    (hgen : IntegralRootPowerLocallySpans l E T G)
    (d : ℕ) (N : proEtaleRingModules T (completedIntegralCommRingSheafUnrestricted l E T))
    (f g : coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
      (purTwistIntegralModule T l E) d ⟶ N)
    (h : ∀ V a x, f.val.app V (G d V a x) = g.val.app V (G d V a x)) :
    f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨S, hS, hspan⟩ := hgen.local_span d U z
  apply N.isSheaf.isSeparated _ _ hS
  intro V i hi
  change N.val.map i.op (f.val.app U z) = N.val.map i.op (g.val.app U z)
  rw [← PresheafOfModules.naturality_apply f.val i.op z,
    ← PresheafOfModules.naturality_apply g.val i.op z]
  have hEq := LinearMap.eqOn_span' (f := (f.val.app (op V)).hom)
    (g := (g.val.app (op V)).hom) (s := Set.range (fun q : (((sheafCompose (ProEt.topology T)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (completedIntegralCommRingSheafUnrestricted l E T)).obj.obj
                (Opposite.op V)) ×
              (Fin d → (purTwistZlOne T l).obj.obj (Opposite.op V)) ↦
              G d (Opposite.op V) q.1 q.2)) (by
      rintro _ ⟨⟨a, x⟩, rfl⟩
      exact h (op V) a x)
  exact hEq (hspan V i hi)
end WeilConjectures
