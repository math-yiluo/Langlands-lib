/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

set_option linter.privateModule false

/-! # Local generation of finite root powers

Source: Stacks, Modules on Sites, Tag 03EK, and coefficient-twist clause 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  MorphismProperty.Over.pullback constantSheaf Padic

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  purTwistFiniteOne purTwistIntegralOne purTwistIntegralTensor purTwistZlModule
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj' sheafCompose
  scalarTensorPower siteSheafTensorRight PresheafOfModules.ofPresheaf
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj

section RootFormulas
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ)

private abbrev rootScalar (W : X.ProEtᵒᵖ) :=
  (((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralCoefficientCommRingSheaf l E X n)).obj.obj W)

private abbrev rootLine (d : ℕ) :=
  coefficientTwistPower X
    (R := integralCoefficientCommRingSheaf l E X n)
    (purTwistFiniteOne X l E n) d

/-- The recursive root generators (the formulas of the hypotheses `hzero`, `hone`,
`hsucc`). -/
private def finiteGen (W : X.ProEtᵒᵖ)
    (a : rootScalar l E X n W) :
    (d : ℕ) → (Fin d → (purTwistZlOne X l).obj.obj W) → (rootLine l E X n d).val.obj W
  | 0, _ => a
  | 1, x => scalarExtensionSection (purTwistIntegralQuotient X l E n)
      (purTwistIntegralOne X l E) W a (purTwistIntegralTensor X l E W 1 (x 0))
  | d + 2, x => siteSheafTensorTmul
      (rootLine l E X n (d + 1)) (purTwistFiniteOne X l E n) W
      (finiteGen W a (d + 1) (fun i ↦ x i.castSucc))
      (scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) W 1
        (purTwistIntegralTensor X l E W 1 (x (Fin.last (d + 1)))))

private theorem finiteGen_snoc (U : X.ProEtᵒᵖ)
    (a : rootScalar l E X n U)
    (d : ℕ) (x : Fin (d + 1) → (purTwistZlOne X l).obj.obj U)
    (z : (purTwistZlOne X l).obj.obj U) :
    finiteGen l E X n U a (d + 2) (Fin.snoc x z) =
      siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf l E X n) _ _ U (finiteGen l E X n U a (d + 1) x)
        (scalarExtensionSection (purTwistIntegralQuotient X l E n)
          (purTwistIntegralOne X l E) U 1 (purTwistIntegralTensor X l E U 1 z)) := by
  simp only [finiteGen, Fin.snoc_castSucc, Fin.snoc_last]
  rfl

private theorem integralTensor_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (purTwistZlOne X l).obj.obj U) :
    (purTwistIntegralOne X l E).val.map f (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlOne X l).obj.map f x) := by
  have h := scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l)) f 1 x
  rw [map_one] at h
  exact h

private theorem rootTensor_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (purTwistZlOne X l).obj.obj U) :
    (purTwistFiniteOne X l E n).val.map f
      (scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) U 1 (purTwistIntegralTensor X l E U 1 x)) =
      scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) V 1
        (purTwistIntegralTensor X l E V 1 ((purTwistZlOne X l).obj.map f x)) := by
  have ht := scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
    (purTwistIntegralQuotient X l E n) (purTwistIntegralOne X l E) f 1
      (purTwistIntegralTensor X l E U 1 x)
  rw [map_one] at ht
  exact ht.trans (congrArg (scalarExtensionSection (purTwistIntegralQuotient X l E n)
    (purTwistIntegralOne X l E) V 1) (integralTensor_restrict l E X f x))

private theorem finiteGen_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : rootScalar l E X n U)
    (d : ℕ) (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    (rootLine l E X n d).val.map f (finiteGen l E X n U a d x) =
      finiteGen l E X n V
        ((integralCoefficientSheaf l E X n).obj.map f a) d
        (fun i ↦ (purTwistZlOne X l).obj.map f (x i)) := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    change (purTwistFiniteOne X l E n).val.map f
      (scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) U a (purTwistIntegralTensor X l E U 1 (x 0))) = _
    exact (scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
      (purTwistIntegralQuotient X l E n) (purTwistIntegralOne X l E) f a
        (purTwistIntegralTensor X l E U 1 (x 0))).trans
      (congrArg (scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) V ((integralCoefficientCommRingSheaf l E X n).obj.map f a))
          (integralTensor_restrict l E X f (x 0)))
  | more d _ ih =>
    let M := rootLine l E X n (d + 1)
    let L := purTwistFiniteOne X l E n
    exact (scalarTensorTmul_naturality
      (R := integralCoefficientCommRingSheaf l E X n) M L f
        (finiteGen l E X n U a (d + 1) (fun i ↦ x i.castSucc))
        (scalarExtensionSection (purTwistIntegralQuotient X l E n)
          (purTwistIntegralOne X l E) U 1
          (purTwistIntegralTensor X l E U 1 (x (Fin.last (d + 1)))))).trans
      (congrArg₂ (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf l E X n) M L V) (ih (fun i ↦ x i.castSucc))
        (rootTensor_restrict l E X n f (x (Fin.last (d + 1)))))

private def rootSpan (d : ℕ) (U : X.ProEtᵒᵖ) :
    Submodule (rootScalar l E X n U)
      ((rootLine l E X n d).val.obj U) :=
  Submodule.span _ (Set.range (fun q :
    (rootScalar l E X n U) ×
      (Fin d → (purTwistZlOne X l).obj.obj U) ↦ finiteGen l E X n U q.1 d q.2))

private theorem rootSpan_restrict (d : ℕ) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (rootLine l E X n d).val.obj U) (hx : x ∈ rootSpan l E X n d U) :
    (rootLine l E X n d).val.map f x ∈ rootSpan l E X n d V := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, z⟩, rfl⟩ := hx
    erw [finiteGen_restrict]
    exact Submodule.subset_span ⟨(_, _), rfl⟩
  | zero => simpa only [map_zero] using (rootSpan l E X n d V).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    erw [(rootLine l E X n d).val.map_smul]
    exact Submodule.smul_mem _ _ hx

private def rootSpanSieve (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n d).val.obj U) : Sieve U.unop where
  arrows V f := (rootLine l E X n d).val.map f.op x ∈ rootSpan l E X n d (op V)
  downward_closed := by
    intro V W f hf g
    simpa only [op_comp, PresheafOfModules.map_comp_apply] using
      rootSpan_restrict l E X n d g.op _ hf

private def rootLocalSpan (d : ℕ) (U : X.ProEtᵒᵖ) :
    Submodule (rootScalar l E X n U)
      ((rootLine l E X n d).val.obj U) where
  carrier := {x | rootSpanSieve l E X n d U x ∈ ProEt.topology X U.unop}
  zero_mem' := by
    apply (ProEt.topology X).superset_covering _ ((ProEt.topology X).top_mem _)
    intro V f _
    change (rootLine l E X n d).val.map f.op 0 ∈ rootSpan l E X n d (op V)
    simpa only [map_zero] using (rootSpan l E X n d (op V)).zero_mem
  add_mem' := by
    intro x y hx hy
    apply (ProEt.topology X).superset_covering _
      ((ProEt.topology X).intersection_covering hx hy)
    intro V f hf
    change (rootLine l E X n d).val.map f.op (x + y) ∈ _
    simpa only [map_add] using (rootSpan l E X n d (op V)).add_mem hf.1 hf.2
  smul_mem' := by
    intro a x hx
    apply (ProEt.topology X).superset_covering _ hx
    intro V f hf
    change (rootLine l E X n d).val.map f.op (a • x) ∈ _
    erw [(rootLine l E X n d).val.map_smul]
    exact Submodule.smul_mem _ _ hf

private theorem span_mem_rootLocalSpan (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n d).val.obj U) (hx : x ∈ rootSpan l E X n d U) :
    x ∈ rootLocalSpan l E X n d U := by
  apply (ProEt.topology X).superset_covering _ ((ProEt.topology X).top_mem _)
  intro V f _
  exact rootSpan_restrict l E X n d f.op x hx

private theorem rootLocalSpan_descent (d : ℕ)
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (φ : P ⟶ (rootLine l E X n d).val.presheaf)
    (hφ : Presheaf.IsLocallySurjective (ProEt.topology X) φ)
    (h : ∀ U t, φ.app U t ∈ rootLocalSpan l E X n d U)
    (U : X.ProEtᵒᵖ) (x : (rootLine l E X n d).val.obj U) :
    x ∈ rootLocalSpan l E X n d U := by
  apply (ProEt.topology X).transitive (Presheaf.imageSieve_mem _ φ x)
  rintro V f ⟨t, ht⟩
  change φ.app (op V) t = (rootLine l E X n d).val.map f.op x at ht
  have he : (rootSpanSieve l E X n d U x).pullback f =
      rootSpanSieve l E X n d (op V) (φ.app (op V) t) := by
    ext W g
    change ((rootLine l E X n d).val.map (g ≫ f).op x ∈ _) ↔ _
    erw [op_comp, PresheafOfModules.map_comp_apply, ← ht]
    rfl
  erw [he]
  exact h (op V) t

private theorem rootTensor_zero_second (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n (d + 1)).val.obj U) :
    siteSheafTensorTmul (rootLine l E X n (d + 1)) (rootLine l E X n 1) U x 0 = 0 := by
  let P := siteTensorPresheaf (rootLine l E X n (d + 1)).val (rootLine l E X n 1).val
  let η := (scalarSheafificationUnit (J := ProEt.topology X) P).app U
  exact (congrArg η.hom
    (TensorProduct.tmul_zero ((rootLine l E X n 1).val.obj U) x)).trans η.hom.map_zero

private theorem rootTensor_add_second (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n (d + 1)).val.obj U)
    (y y' : (rootLine l E X n 1).val.obj U) :
    siteSheafTensorTmul (rootLine l E X n (d + 1)) (rootLine l E X n 1) U x (y + y') =
      siteSheafTensorTmul (rootLine l E X n (d + 1)) (rootLine l E X n 1) U x y +
      siteSheafTensorTmul (rootLine l E X n (d + 1)) (rootLine l E X n 1) U x y' := by
  let P := siteTensorPresheaf (rootLine l E X n (d + 1)).val (rootLine l E X n 1).val
  let η := (scalarSheafificationUnit (J := ProEt.topology X) P).app U
  exact (congrArg η.hom (TensorProduct.tmul_add x y y')).trans (η.hom.map_add _ _)

private theorem rootTensor_mem_span (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n (d + 1)).val.obj U)
    (y : (rootLine l E X n 1).val.obj U)
    (hx : x ∈ rootSpan l E X n (d + 1) U)
    (hy : y ∈ rootSpan l E X n 1 U) :
    siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf l E X n) _ _ U x y ∈
      rootSpan l E X n (d + 2) U := by
  induction hx using Submodule.span_induction with
  | zero =>
    simpa only [scalarTensorTmul_zero_first] using (rootSpan l E X n (d + 2) U).zero_mem
  | add x x' _ _ hx hx' =>
    simpa only [scalarTensorTmul_add_first] using Submodule.add_mem _ hx hx'
  | smul a x _ hx =>
    exact (congrArg (fun z ↦ z ∈ rootSpan l E X n (d + 2) U)
      (scalarTensorTmul_smul_first
        (R := integralCoefficientCommRingSheaf l E X n)
        (rootLine l E X n (d + 1)) (rootLine l E X n 1) U a x y)).mpr
          (Submodule.smul_mem _ a hx)
  | mem x hx =>
    obtain ⟨⟨a, z⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | zero =>
      exact (congrArg (fun t ↦ t ∈ rootSpan l E X n (d + 2) U)
        (rootTensor_zero_second l E X n d U _)).mpr
          (rootSpan l E X n (d + 2) U).zero_mem
    | add y y' _ _ hy hy' =>
      exact (congrArg (fun t ↦ t ∈ rootSpan l E X n (d + 2) U)
        (rootTensor_add_second l E X n d U _ y y')).mpr (Submodule.add_mem _ hy hy')
    | smul b y _ hy =>
      exact (congrArg (fun z ↦ z ∈ rootSpan l E X n (d + 2) U)
        (scalarTensorTmul_smul_second
          (R := integralCoefficientCommRingSheaf l E X n)
          (rootLine l E X n (d + 1)) (rootLine l E X n 1) U b
          (finiteGen l E X n U a (d + 1) z) y)).mpr (Submodule.smul_mem _ b hy)
    | mem y hy =>
      obtain ⟨⟨b, w⟩, rfl⟩ := hy
      change siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := integralCoefficientCommRingSheaf l E X n) _ _ U _
        (scalarExtensionSection (purTwistIntegralQuotient X l E n)
          (purTwistIntegralOne X l E) U b (purTwistIntegralTensor X l E U 1 (w 0))) ∈ _
      have hb := scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
        (purTwistIntegralQuotient X l E n) (purTwistIntegralOne X l E) U b 1
          (purTwistIntegralTensor X l E U 1 (w 0))
      rw [mul_one] at hb
      apply (congrArg (fun t ↦ siteSheafTensorTmul
        (rootLine l E X n (d + 1)) (rootLine l E X n 1) U
          (finiteGen l E X n U a (d + 1) z) t ∈ rootSpan l E X n (d + 2) U) hb).mp
      exact (congrArg (fun t ↦ t ∈ rootSpan l E X n (d + 2) U)
        (scalarTensorTmul_smul_second
          (R := integralCoefficientCommRingSheaf l E X n)
          (rootLine l E X n (d + 1)) (rootLine l E X n 1) U b
          (finiteGen l E X n U a (d + 1) z)
          (scalarExtensionSection (purTwistIntegralQuotient X l E n)
            (purTwistIntegralOne X l E) U 1 (purTwistIntegralTensor X l E U 1 (w 0))))).mpr
        (Submodule.smul_mem _ b (Submodule.subset_span
          ⟨(a, Fin.snoc z (w 0)), finiteGen_snoc l E X n U a d z (w 0)⟩))

private theorem rootTensor_mem_localSpan (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n (d + 1)).val.obj U)
    (y : (rootLine l E X n 1).val.obj U)
    (hx : x ∈ rootLocalSpan l E X n (d + 1) U) (hy : y ∈ rootLocalSpan l E X n 1 U) :
    siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf l E X n) _ _ U x y ∈
      rootLocalSpan l E X n (d + 2) U := by
  apply (ProEt.topology X).superset_covering _
    ((ProEt.topology X).intersection_covering hx hy)
  intro V f hf
  exact (congrArg (fun z ↦ z ∈ rootSpan l E X n (d + 2) (op V))
    (scalarTensorTmul_naturality
      (R := integralCoefficientCommRingSheaf l E X n)
      (rootLine l E X n (d + 1)) (rootLine l E X n 1) f.op x y)).mpr
        (rootTensor_mem_span l E X n d (op V) _ _ hf.1 hf.2)

private theorem rootLocalSpan_local (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n d).val.obj U) (S : Sieve U.unop)
    (hS : S ∈ ProEt.topology X U.unop)
    (h : ∀ (V : X.ProEt) (i : V ⟶ U.unop), S i →
      (rootLine l E X n d).val.map i.op x ∈ rootLocalSpan l E X n d (op V)) :
    x ∈ rootLocalSpan l E X n d U := by
  apply (ProEt.topology X).transitive hS
  intro V i hi
  have he : (rootSpanSieve l E X n d U x).pullback i =
      rootSpanSieve l E X n d (op V) ((rootLine l E X n d).val.map i.op x) := by
    ext W j
    change ((rootLine l E X n d).val.map (j ≫ i).op x ∈ _) ↔ _
    rw [op_comp, PresheafOfModules.map_comp_apply]
    rfl
  rw [he]
  exact h V i hi

-- Comparing the two scalar-extension units unfolds several module wrappers.
private theorem finiteTensor_generator (U : X.ProEtᵒᵖ)
    (a : rootScalar l E X n U)
    (b : (purTwistIntegralConstant X l E).obj.obj U)
    (x : (purTwistZlOne X l).obj.obj U) :
    scalarExtensionSection (purTwistIntegralQuotient X l E n)
      (purTwistIntegralOne X l E) U a (purTwistIntegralTensor X l E U b x) =
      finiteGen l E X n U (a * (show rootScalar l E X n U from
      (purTwistIntegralQuotient X l E n).hom.app U b))
        1 (fun _ ↦ x) := by
  let M := (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l)
  have hb := scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E) M U b 1 x
  rw [mul_one] at hb
  calc
    _ = scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) U a
          (b • scalarExtensionSection (purTwistConstantIntegersMap X l E) M U 1 x) :=
      congrArg (fun y ↦ scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) U a y) hb.symm
    _ = scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) U
          (a * (show rootScalar l E X n U from
            (purTwistIntegralQuotient X l E n).hom.app U b))
          (scalarExtensionSection (purTwistConstantIntegersMap X l E) M U 1 x) :=
      scalarExtensionSection_base_smul (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) U a b _
    _ = _ := rfl

private theorem first_rootLocalSpan (U : X.ProEtᵒᵖ)
    (x : (rootLine l E X n 1).val.obj U) : x ∈ rootLocalSpan l E X n 1 U := by
  let P := changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistIntegralQuotient X l E n) (purTwistIntegralOne X l E)
  let φ := (PresheafOfModules.toPresheaf _).map
    (scalarSheafificationUnit (J := ProEt.topology X) P)
  have hφ : Presheaf.IsLocallySurjective (ProEt.topology X) φ := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ P.presheaf)
    infer_instance
  apply rootLocalSpan_descent l E X n 1 P.presheaf φ hφ _ U x
  intro V t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb =>
    exact (congrArg (fun z ↦ z ∈ rootLocalSpan l E X n 1 V)
      ((φ.app V).hom.map_add a b)).mpr (Submodule.add_mem _ ha hb)
  | tmul a y =>
    let Q := changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistConstantIntegersMap X l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l))
    let η := scalarSheafificationUnit (J := ProEt.topology X) Q
    change scalarExtensionSection (purTwistIntegralQuotient X l E n)
      (purTwistIntegralOne X l E) V a y ∈ _
    let ψ := (PresheafOfModules.toPresheaf _).map η
    have : Presheaf.IsLocallySurjective (ProEt.topology X) ψ := by
      change Presheaf.IsLocallySurjective _ (toSheafify _ Q.presheaf)
      infer_instance
    apply rootLocalSpan_local l E X n 1 V _
      (Presheaf.imageSieve ψ y) (Presheaf.imageSieve_mem (ProEt.topology X) ψ y)
    intro W i hi
    obtain ⟨s, hs⟩ := hi
    change η.app (op W) s = (purTwistIntegralOne X l E).val.map i.op y at hs
    let c := (integralCoefficientCommRingSheaf l E X n).obj.map i.op a
    let F := scalarExtensionSection (purTwistIntegralQuotient X l E n)
      (purTwistIntegralOne X l E) (op W) c
    have hres : (rootLine l E X n 1).val.map i.op
        (scalarExtensionSection (purTwistIntegralQuotient X l E n)
          (purTwistIntegralOne X l E) V a y) = F (η.app (op W) s) :=
      (scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
        (purTwistIntegralQuotient X l E n) (purTwistIntegralOne X l E) i.op a y).trans
          (congrArg F hs.symm)
    apply (congrArg (fun z ↦ z ∈ rootLocalSpan l E X n 1 (op W)) hres).mpr
    clear hres hs
    induction s using TensorProduct.inductionOn with
    | add b b' hb hb' =>
      have ha : F (η.app (op W) (b + b')) =
          F (η.app (op W) b) + F (η.app (op W) b') :=
        (congrArg F ((η.app (op W)).hom.map_add b b')).trans
          (scalarExtensionSection_add (purTwistIntegralQuotient X l E n)
            (purTwistIntegralOne X l E) (op W) c _ _)
      exact (congrArg (fun z ↦ z ∈ rootLocalSpan l E X n 1 (op W)) ha).mpr
        ((rootLocalSpan l E X n 1 (op W)).add_mem hb hb')
    | tmul b z =>
      apply span_mem_rootLocalSpan
      change scalarExtensionSection (purTwistIntegralQuotient X l E n)
        (purTwistIntegralOne X l E) (op W) _
        (purTwistIntegralTensor X l E (op W) b z) ∈ _
      rw [finiteTensor_generator]
      exact Submodule.subset_span ⟨(_, _), rfl⟩

end RootFormulas

-- Keep the original generator-family binder names, including the implicit scalar binder.

end WeilConjectures
