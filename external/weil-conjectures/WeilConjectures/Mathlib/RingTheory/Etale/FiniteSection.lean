/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting

/-!
# Étale-local sections of étale algebras over a finite algebra, at a geometric point

Let `B` be a finite `A`-algebra with a *unique* point `t` over a geometric point `φ : A →+* Ω`
(`Ω` algebraically closed), and let `C` be an étale `B`-algebra with a point `ψ` over `t`. Then,
étale-locally on `A` at `φ`, the map `B → C` has a section through `ψ`: there is an étale
`A`-algebra `A'` with a point `φ'` over `φ` and a `B`-algebra map `h : C → A' ⊗[A] B` such that
the point `(φ', t)` of `A' ⊗[A] B` composed with `h` is `ψ`
(`Algebra.exists_etale_algHom_tensor_comp_eq`).

This is the geometric-point form of property (C) of [Stacks 04DW]
(`Algebra.Etale.exists_etale_algHom_comap_eq_of_bijective_residueFieldMap'`): the uniqueness
of the point `t` makes the residue field extension of `B/A` at `ker t` purely inseparable, so
that after the residue field trivialisation
`Algebra.Etale.exists_etale_bijective_residueFieldMap'` the prime `ker ψ` has trivial residue
field extension over `B`, and the prime `ker t` is the only prime of `B` over `ker φ`. The point
`ψ` is then recovered from the prime produced by property (C) because a point is determined
by its kernel when the residue field extension is trivial.

## Main results

- `Algebra.exists_etale_algHom_tensor_comp_eq`: the étale-local section through a point.

-/

@[expose] public section

universe u v w

open TensorProduct RingHom

namespace Algebra

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C] {Ω : Type w} [Field Ω]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The restriction of a point of `C` over `φ` to the `A`-algebra `B` through which `C` is an
algebra. -/
def _root_.RingHom.PointsOver.restrictScalars (φ : A →+* Ω) (ψ : PointsOver φ C) :
    PointsOver φ B :=
  ⟨ψ.1.comp (algebraMap B C), by rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ψ.2]⟩

@[simp]
lemma _root_.RingHom.PointsOver.restrictScalars_apply (φ : A →+* Ω) (ψ : PointsOver φ C)
    (b : B) : ψ.restrictScalars (B := B) φ b = ψ (algebraMap B C b) := rfl

variable [IsAlgClosed Ω]

-- long proof with many local algebra instances
/-- **Étale-local sections through a geometric point.** Let `B` be a finite `A`-algebra with a
unique point over the geometric point `φ : A →+* Ω`, `C` an étale `B`-algebra and `ψ` a point
of `C` over `φ`. Then there is an étale `A`-algebra `A'` with a point `φ'` over `φ` and a
`B`-algebra map `h : C → A' ⊗[A] B` through which `ψ` factors as the point `(φ', ψ|_B)` of
`A' ⊗[A] B`. -/
theorem exists_etale_algHom_tensor_comp_eq [Module.Finite A B] [Algebra.Etale B C]
    (φ : A →+* Ω) [Subsingleton (PointsOver φ B)] (ψ : PointsOver φ C) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (φ' : A' →+* Ω) (hφ' : φ'.comp (algebraMap A A') = φ) (h : C →ₐ[A] A' ⊗[A] B),
      h.comp (IsScalarTower.toAlgHom A B C) = Algebra.TensorProduct.includeRight ∧
        ((ψ.restrictScalars φ).tensor hφ').1.comp h.toRingHom = ψ.1 := by
  classical
  set t : PointsOver φ B := ψ.restrictScalars φ with ht
  set q : Ideal C := RingHom.ker ψ.1 with hq
  -- Step 1: the residue field extension of `B/A` at `ker t = q ∩ B` is purely inseparable.
  have hker : RingHom.ker φ = (q.under B).under A := by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, hq, RingHom.comap_ker,
      ← IsScalarTower.algebraMap_eq, ψ.2]
  have hpi : (Ideal.ResidueField.map ((q.under B).under A) (q.under B) (algebraMap A B)
      rfl).IsPurelyInseparable :=
    PointsOver.isPurelyInseparable_of_forall_eq' t (fun t' _ ↦ Subsingleton.elim _ _) _ hker
      (q.under B) rfl rfl
  -- Step 2: trivialise the residue field extension of `ψ` over `B`.
  obtain ⟨A₁, _, _, _, θ, hθ, hres₁⟩ :=
    Algebra.Etale.exists_etale_bijective_residueFieldMap' (A := A) q hpi
  let B₁ := A₁ ⊗[A] B
  let C₁ := B₁ ⊗[B] C
  let ψL : q.ResidueField →+* Ω := ψ.residueFieldLift q rfl
  -- the point `ψ₁` of `C₁` and the point `φ₁` of `A₁`
  let ψ₁ : C₁ →+* Ω := ψL.comp θ.toRingHom
  have hψ₁B : ∀ b : B, ψ₁ (algebraMap B C₁ b) = t b := fun b ↦ by
    change ψL (θ (algebraMap B C₁ b)) = t b
    rw [θ.commutes, IsScalarTower.algebraMap_apply B C q.ResidueField]
    exact PointsOver.residueFieldLift_algebraMap ψ q rfl _
  have hψ₁C : ∀ c : C, ψ₁ (Algebra.TensorProduct.includeRight c) = ψ c := fun c ↦ by
    change ψL (θ (Algebra.TensorProduct.includeRight c)) = ψ c
    rw [hθ]
    exact PointsOver.residueFieldLift_algebraMap ψ q rfl c
  let φ₁ : A₁ →+* Ω := ψ₁.comp (algebraMap A₁ C₁)
  have hA₁C₁ : ∀ a : A,
      algebraMap A₁ C₁ (algebraMap A A₁ a) = algebraMap B C₁ (algebraMap A B a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply A A₁ C₁, ← IsScalarTower.algebraMap_apply A B C₁]
  have hφ₁ : φ₁.comp (algebraMap A A₁) = φ := by
    ext a
    simp only [φ₁, RingHom.comp_apply, hA₁C₁, hψ₁B]
    exact t.apply_algebraMap a
  have hB₁C₁ : ∀ x : B₁, algebraMap B₁ C₁ x = x ⊗ₜ 1 := fun x ↦ rfl
  -- the point `ψ₁` restricted to `B₁ = A₁ ⊗[A] B` is `(φ₁, t)`
  have hψ₁B₁ : ψ₁.comp (algebraMap B₁ C₁) = (t.tensor hφ₁).1 := by
    let := φ.toAlgebra
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a₁ b =>
      rw [RingHom.comp_apply, PointsOver.tensor_tmul, hB₁C₁]
      have : (a₁ ⊗ₜ[A] b) ⊗ₜ[B] (1 : C) = algebraMap A₁ C₁ a₁ * algebraMap B C₁ b := by
        change _ = (algebraMap A₁ B₁ a₁ ⊗ₜ 1) * ((1 ⊗ₜ b) ⊗ₜ 1)
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]
        rfl
      rw [this, map_mul, hψ₁B]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  -- Step 3: property (C) at the prime `q₁ = ker ψ₁` over `A₁`.
  set q₁ : Ideal C₁ := RingHom.ker θ.toRingHom with hq₁def
  have hq₁ : q₁ = RingHom.ker ψ₁ := by
    rw [hq₁def]
    change RingHom.ker θ.toRingHom = RingHom.ker (ψL.comp θ.toRingHom)
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot ψL).mp ψL.injective,
      ← RingHom.ker_eq_comap_bot]
  have hq₁A₁ : q₁.under A₁ = RingHom.ker φ₁ := by
    rw [hq₁, Ideal.under, RingHom.comap_ker]
  have hq₁B₁ : q₁.under B₁ = RingHom.ker (t.tensor hφ₁).1 := by
    rw [hq₁, Ideal.under, RingHom.comap_ker, hψ₁B₁]
  have huniqB : ∀ (Q : Ideal B₁) [Q.IsPrime], Q.under A₁ = q₁.under A₁ → Q = q₁.under B₁ := by
    intro Q _ hQ
    rw [hq₁A₁] at hQ
    have : Q.LiesOver (RingHom.ker φ₁) := ⟨hQ.symm⟩
    obtain ⟨t₁, ht₁⟩ := PointsOver.exists_ker_eq (φ := φ₁) Q
    have : t₁ = t.tensor hφ₁ := by
      rw [← (PointsOver.tensorEquiv hφ₁).symm_apply_apply t₁, PointsOver.tensorEquiv_symm_apply,
        Subsingleton.elim (PointsOver.tensorEquiv hφ₁ t₁) t]
    rw [hq₁B₁, ← ht₁, this]
  obtain ⟨A₁', _, _, _, h₁, hh₁, P', _, hP', hresP', q', _, hq'P', hq₁'⟩ :=
    Algebra.Etale.exists_etale_algHom_comap_eq_of_bijective_residueFieldMap' (A := A₁) (B := B₁)
      (C := C₁) q₁ huniqB hres₁
  have hh₁' : ∀ x : B₁, h₁ (algebraMap B₁ C₁ x) = algebraMap B₁ (A₁' ⊗[A₁] B₁) x :=
    fun x ↦ congr($hh₁ x)
  -- Step 4: the point `φ₁'` of `A₁'` over `φ₁`, through `κ(P') ≅ κ(q₁ ∩ A₁)`.
  have hq₁A₁' : q₁.under A₁ ≤ RingHom.ker φ₁ := hq₁A₁.le
  let ρ : (q₁.under A₁).ResidueField →+* Ω := Ideal.ResidueField.lift _ φ₁ hq₁A₁' (fun x hx ↦
    (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 (by
      simpa [Ideal.primeCompl, hq₁A₁, RingHom.mem_ker] using hx)))
  have hρ : ∀ a, ρ (algebraMap A₁ _ a) = φ₁ a := fun a ↦
    Ideal.ResidueField.lift_algebraMap _ _ _ _ a
  let E : (q₁.under A₁).ResidueField ≃+* P'.ResidueField :=
    RingEquiv.ofBijective (Ideal.ResidueField.map (q₁.under A₁) P' (algebraMap A₁ A₁')
      (P'.over_def _)) hresP'
  let φ₁' : A₁' →+* Ω := ρ.comp (E.symm.toRingHom.comp (algebraMap A₁' P'.ResidueField))
  have hφ₁' : φ₁'.comp (algebraMap A₁ A₁') = φ₁ := by
    ext a
    simp only [φ₁', RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← Ideal.ResidueField.map_algebraMap (q₁.under A₁) P' (algebraMap A₁ A₁') (P'.over_def _)]
    have hE : E (algebraMap A₁ _ a) = Ideal.ResidueField.map (q₁.under A₁) P' (algebraMap A₁ A₁')
        (P'.over_def _) (algebraMap A₁ _ a) := RingEquiv.ofBijective_apply _ _ _
    rw [← hE, E.symm_apply_apply, hρ]
  have hker₁' : RingHom.ker φ₁' = P' := by
    ext x
    simp only [φ₁', RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [map_eq_zero_iff ρ ρ.injective, map_eq_zero_iff E.symm E.symm.injective,
      Ideal.algebraMap_residueField_eq_zero]
  -- Step 5: assemble.
  let _ : Algebra A A₁' := ((algebraMap A₁ A₁').comp (algebraMap A A₁)).toAlgebra
  have : IsScalarTower A A₁ A₁' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.Etale A A₁' := Algebra.Etale.comp A A₁ A₁'
  have hφ'A : φ₁'.comp (algebraMap A A₁') = φ := PointsOver.comp_algebraMap_of_tower hφ₁ hφ₁'
  let κ : A₁' ⊗[A₁] B₁ ≃ₐ[A₁'] A₁' ⊗[A] B := Algebra.TensorProduct.cancelBaseChange A A₁ A₁' A₁' B
  let ι : C →ₐ[A] C₁ := (Algebra.TensorProduct.includeRight : C →ₐ[B] C₁).restrictScalars A
  let h : C →ₐ[A] A₁' ⊗[A] B :=
    (κ.toAlgHom.restrictScalars A).comp ((h₁.restrictScalars A).comp ι)
  refine ⟨A₁', inferInstance, inferInstance, inferInstance, φ₁', hφ'A, h, ?_, ?_⟩
  · ext b
    have h1 : ι (algebraMap B C b) = algebraMap B₁ C₁ (algebraMap B B₁ b) := by
      change Algebra.TensorProduct.includeRight (algebraMap B C b) = _
      rw [Algebra.TensorProduct.includeRight.commutes, IsScalarTower.algebraMap_apply B B₁ C₁]
    have h2 : h₁ (algebraMap B₁ C₁ (algebraMap B B₁ b)) =
        Algebra.TensorProduct.includeRight (algebraMap B B₁ b) := by
      have := congr($hh₁ (algebraMap B B₁ b))
      simpa using this
    simp only [h, AlgHom.comp_apply, AlgHom.coe_restrictScalars']
    change κ (h₁ (ι (algebraMap B C b))) = _
    rw [h1, h2]
    change κ (1 ⊗ₜ[A₁] (1 ⊗ₜ[A] b)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    rfl
  · -- the two points `ψ₃ := (φ₁', t) ∘ κ ∘ h₁` and `ψ₁` of `C₁` over `(φ₁, t)` have kernel `q₁`
    let f : B₁ →ₐ[A] A₁' ⊗[A] B :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A₁ A₁') (AlgHom.id A B)
    have hκf : ∀ x : B₁, κ (algebraMap B₁ (A₁' ⊗[A₁] B₁) x) = f x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a₁ b =>
        change κ (1 ⊗ₜ[A₁] (a₁ ⊗ₜ[A] b)) = _
        rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
        rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    set T : PointsOver φ₁' (A₁' ⊗[A] B) := t.tensor hφ'A with hT
    let ψ₃ : C₁ →+* Ω := T.1.comp (κ.toRingHom.comp h₁.toRingHom)
    have hψ₃ : ∀ c, ψ₃ c = T (κ (h₁ c)) := fun _ ↦ rfl
    have hψ₃B₁ : ψ₃.comp (algebraMap B₁ C₁) = (t.tensor hφ₁).1 := by
      apply RingHom.ext
      intro x
      rw [RingHom.comp_apply, hψ₃, hh₁', hκf]
      exact PointsOver.tensor_map hφ₁ hφ₁' t x
    -- the kernel of `(φ₁', t)` on `A₁' ⊗[A₁] B₁` is `q'`
    have hq'κ : (RingHom.ker T.1).comap κ.toRingHom = q' := by
      have h₁' : ((RingHom.ker T.1).comap κ.toRingHom).under A₁' = P' := by
        rw [Ideal.under, Ideal.comap_comap]
        have : κ.toRingHom.comp (algebraMap A₁' (A₁' ⊗[A₁] B₁)) = algebraMap A₁' (A₁' ⊗[A] B) :=
          RingHom.ext fun a ↦ κ.commutes a
        rw [this, RingHom.comap_ker, T.2, hker₁']
      have h₂' : ((RingHom.ker T.1).comap κ.toRingHom).under B₁ = q₁.under B₁ := by
        rw [Ideal.under, Ideal.comap_comap, hq₁B₁, RingHom.comap_ker]
        congr 1
        apply RingHom.ext
        intro x
        change T (κ (algebraMap B₁ (A₁' ⊗[A₁] B₁) x)) = _
        rw [hκf]
        exact PointsOver.tensor_map hφ₁ hφ₁' t x
      have h₃' : q'.under B₁ = q₁.under B₁ := by
        rw [Ideal.under, hq₁', Ideal.under, Ideal.comap_comap]
        congr 1
        exact RingHom.ext fun x ↦ (hh₁' x).symm
      have : ((RingHom.ker T.1).comap κ.toRingHom).LiesOver P' := ⟨h₁'.symm⟩
      have : ((RingHom.ker T.1).comap κ.toRingHom).LiesOver (q₁.under B₁) := ⟨h₂'.symm⟩
      have : q'.LiesOver (q₁.under B₁) := ⟨h₃'.symm⟩
      exact Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hresP' _ _ (h₂'.trans h₃'.symm)
    have hψ₃ker : RingHom.ker ψ₃ = q₁ := by
      rw [hq₁']
      change (RingHom.ker T.1).comap (κ.toRingHom.comp h₁.toRingHom) = _
      rw [← Ideal.comap_comap, hq'κ]
    -- hence the two points agree, since the residue field extension at `q₁` is trivial
    let Ψ₃ : PointsOver (t.tensor hφ₁).1 C₁ := ⟨ψ₃, hψ₃B₁⟩
    let Ψ₁ : PointsOver (t.tensor hφ₁).1 C₁ := ⟨ψ₁, hψ₁B₁⟩
    have hΨ : Ψ₃ = Ψ₁ :=
      PointsOver.ext_of_ker_eq_of_isPurelyInseparable' (q₁.under B₁) hq₁B₁.symm q₁ hψ₃ker hq₁.symm
        (RingHom.IsPurelyInseparable.of_bijective _ hres₁)
    apply RingHom.ext
    intro c
    have := congrArg (fun Ψ : PointsOver (t.tensor hφ₁).1 C₁ ↦
      Ψ (Algebra.TensorProduct.includeRight c)) hΨ
    change ψ₃ (Algebra.TensorProduct.includeRight c) =
      ψ₁ (Algebra.TensorProduct.includeRight c) at this
    change ψ₃ (Algebra.TensorProduct.includeRight c) = ψ c
    rw [this, hψ₁C]

end Algebra
