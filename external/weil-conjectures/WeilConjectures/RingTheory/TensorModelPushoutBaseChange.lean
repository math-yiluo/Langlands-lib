/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IsTensorProduct

/-! # Extending a tensor pushout square

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph, base-change step.
(blueprint: lem-pc-tensor-model-pushout-base-change)
-/

@[expose] public section

universe u v w x y z
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A pushout square between two scalar extensions remains a pushout after another
scalar extension, with the `P`-structure on `T ⊗[R] A` induced from the given one on
`S ⊗[R] A` by the transition map. No directed diagram or finite-presentation hypothesis
is needed.

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph, base-change step.
(blueprint: lem-pc-tensor-model-pushout-base-change)

Proof:
1. Put D0 = S tensor_R A, E0 = S tensor_R B, D1 = T tensor_R A, and
   E1 = T tensor_R B. Let mD and mE be the tensor transitions. Their square with
   id tensor f commutes by induction on tensors. The P-structure on D1 is the one
   through mD and the Q-structure on E1 is the one through mE. The commuting square and the
   given P-Q-E0 scalar tower prove the P-Q-E1 scalar tower.
2. The squares S-T-D0-D1 and S-T-E0-E1 are pushouts: transport the canonical
   tensor pushouts using cancellation of base change. On generators the right
   inclusion followed by cancellation sends s tensor a to t(s) tensor a, and
   likewise for B. Thus the transported maps are exactly mD and mE.
3. Paste the first square with the square D0-E0-D1-E1. The resulting rectangle
   is the second square, so pushout cancellation shows D0-E0-D1-E1 is a pushout.
   Flip it to D0-D1-E0-E1. Paste this square with P-D0-Q-E0, which is a pushout
   by hypothesis. Pushout composition gives P-D1-Q-E1. All scalar towers used
   in pasting follow from the commuting square; no finite presentation or
   nonzero-ring hypothesis occurs.
-/
theorem tensor_model_pushout_base_change
    (R : Type u) (S : Type v) (T : Type w) (A : Type x) (B : Type y)
    (P Q : Type z)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [CommRing P] [CommRing Q] [Algebra R S] [Algebra R T]
    [Algebra R A] [Algebra R B] [Algebra P Q]
    (t : S →ₐ[R] T) (f : A →ₐ[R] B) (q : Q →+* S ⊗[R] B) (aP : Algebra P (S ⊗[R] A))
    (h : let D := S ⊗[R] A
      let E := S ⊗[R] B
      let d : D →+* E :=
        (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
      letI : Algebra D E := d.toAlgebra
      letI : Algebra Q E := q.toAlgebra
      letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
      letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
      ∃ hPQ : IsScalarTower P Q E,
        letI := hPQ
        Algebra.IsPushout P D Q E) :
    let D := T ⊗[R] A
    let E := T ⊗[R] B
    let d : D →+* E := (Algebra.TensorProduct.map (AlgHom.id T T) f).toRingHom
    letI : Algebra D E := d.toAlgebra
    letI : Algebra Q E :=
      ((Algebra.TensorProduct.map t (AlgHom.id R B)).toRingHom.comp q).toAlgebra
    letI : Algebra P D :=
      ((Algebra.TensorProduct.map t (AlgHom.id R A)).toRingHom.comp
        (algebraMap P (S ⊗[R] A))).toAlgebra
    letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
    letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
    ∃ hPQ : IsScalarTower P Q E,
      letI := hPQ
      Algebra.IsPushout P D Q E := by
  let D₀ := S ⊗[R] A
  let E₀ := S ⊗[R] B
  let D₁ := T ⊗[R] A
  let E₁ := T ⊗[R] B
  let d₀ : D₀ →+* E₀ :=
    (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
  let d₁ : D₁ →+* E₁ :=
    (Algebra.TensorProduct.map (AlgHom.id T T) f).toRingHom
  let mD : D₀ →+* D₁ := (Algebra.TensorProduct.map t (AlgHom.id R A)).toRingHom
  let mE : E₀ →+* E₁ := (Algebra.TensorProduct.map t (AlgHom.id R B)).toRingHom
  let : Algebra D₀ E₀ := d₀.toAlgebra
  let : Algebra Q E₀ := q.toAlgebra
  obtain ⟨hPQ, hp⟩ := h
  let : Algebra P E₀ := (d₀.comp (algebraMap P D₀)).toAlgebra
  let : IsScalarTower P D₀ E₀ := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower P Q E₀ := hPQ
  let : Algebra.IsPushout P D₀ Q E₀ := hp
  let : Algebra D₀ D₁ := mD.toAlgebra
  let : Algebra E₀ E₁ := mE.toAlgebra
  let : Algebra D₁ E₁ := d₁.toAlgebra
  let : Algebra Q E₁ := (mE.comp q).toAlgebra
  let : Algebra P D₁ := (mD.comp (algebraMap P D₀)).toAlgebra
  let : Algebra P E₁ := (d₁.comp (algebraMap P D₁)).toAlgebra
  let : IsScalarTower P D₁ E₁ := .of_algebraMap_eq fun _ ↦ rfl
  have square : d₁.comp mD = mE.comp d₀ := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s a =>
      change Algebra.TensorProduct.map (AlgHom.id T T) f
        (Algebra.TensorProduct.map t (AlgHom.id R A) (s ⊗ₜ[R] a)) =
        Algebra.TensorProduct.map t (AlgHom.id R B)
          (Algebra.TensorProduct.map (AlgHom.id S S) f (s ⊗ₜ[R] a))
      simp
  have hPE : (algebraMap P E₁) = mE.comp (algebraMap P E₀) := by
    apply RingHom.ext
    intro p
    exact DFunLike.congr_fun square (algebraMap P D₀ p)
  let : IsScalarTower P Q E₁ := .of_algebraMap_eq fun p ↦ by
    rw [hPE]
    change mE (algebraMap P E₀ p) = mE (q (algebraMap P Q p))
    exact congrArg mE (IsScalarTower.algebraMap_apply P Q E₀ p)
  refine ⟨inferInstance, ?_⟩
  let : Algebra S T := t.toRingHom.toAlgebra
  let : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ (t.commutes r).symm
  let : Algebra S D₁ := Algebra.TensorProduct.leftAlgebra
  let : Algebra S E₁ := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower S T D₁ := inferInstance
  let : IsScalarTower S T E₁ := inferInstance
  let : IsScalarTower S D₀ D₁ := .of_algebraMap_eq fun s ↦ by
    change t s ⊗ₜ[R] (1 : A) =
      Algebra.TensorProduct.map t (AlgHom.id R A) (s ⊗ₜ[R] (1 : A))
    simp
  let : IsScalarTower S E₀ E₁ := .of_algebraMap_eq fun s ↦ by
    change t s ⊗ₜ[R] (1 : B) =
      Algebra.TensorProduct.map t (AlgHom.id R B) (s ⊗ₜ[R] (1 : B))
    simp
  have HD : Algebra.IsPushout S T D₀ D₁ := by
    let : Algebra D₀ (T ⊗[S] D₀) := Algebra.TensorProduct.rightAlgebra
    apply Algebra.IsPushout.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R S T T A)
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s a =>
      change (Algebra.TensorProduct.cancelBaseChange R S T T A)
        (1 ⊗ₜ[S] (s ⊗ₜ[R] a)) = t s ⊗ₜ[R] a
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have HE : Algebra.IsPushout S T E₀ E₁ := by
    let : Algebra E₀ (T ⊗[S] E₀) := Algebra.TensorProduct.rightAlgebra
    apply Algebra.IsPushout.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R S T T B)
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s b =>
      change (Algebra.TensorProduct.cancelBaseChange R S T T B)
        (1 ⊗ₜ[S] (s ⊗ₜ[R] b)) = t s ⊗ₜ[R] b
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let : Algebra.IsPushout S D₀ T D₁ := HD.symm
  let : Algebra D₀ E₁ := (mE.comp d₀).toAlgebra
  let : IsScalarTower S D₀ E₀ := .of_algebraMap_eq fun s ↦ by
    change s ⊗ₜ[R] (1 : B) =
      Algebra.TensorProduct.map (AlgHom.id S S) f (s ⊗ₜ[R] (1 : A))
    simp
  let : IsScalarTower D₀ E₀ E₁ := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower D₀ D₁ E₁ := .of_algebraMap_eq fun a ↦
    (DFunLike.congr_fun square a).symm
  let : IsScalarTower S D₁ E₁ := .of_algebraMap_eq fun s ↦ by
    change t s ⊗ₜ[R] (1 : B) =
      Algebra.TensorProduct.map (AlgHom.id T T) f (t s ⊗ₜ[R] (1 : A))
    simp
  have HDE : Algebra.IsPushout D₀ E₀ D₁ E₁ :=
    (Algebra.IsPushout.comp_iff S D₀ (T := E₀) T D₁).mp HE.symm
  let : Algebra.IsPushout D₀ D₁ E₀ E₁ := HDE.symm
  let : IsScalarTower P D₀ D₁ := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower P E₀ E₁ := .of_algebraMap_eq fun p ↦
    DFunLike.congr_fun hPE p
  let : IsScalarTower P D₀ E₁ := .of_algebraMap_eq fun p ↦ by
    rw [hPE]
    rfl
  let : IsScalarTower Q E₀ E₁ := .of_algebraMap_eq fun _ ↦ rfl
  exact (Algebra.IsPushout.comp_iff P D₀ (T := D₁) Q E₀).mpr inferInstance

end AlgebraicGeometry
