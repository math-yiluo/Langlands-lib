/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint
public import WeilConjectures.Mathlib.RingTheory.Etale.PropertyC
public import WeilConjectures.Mathlib.RingTheory.Etale.ResidueField
public import WeilConjectures.Mathlib.RingTheory.Etale.ResidueFieldBaseChange
public import WeilConjectures.Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# Étale-local splitting of finite algebras at a geometric point

Let `B` be a finite `A`-algebra, `Ω` an algebraically closed field and `φ : A →+* Ω` a
geometric point of `A`. Every point `t` of `B` over `φ` can be isolated étale-locally on `A`:
there is an étale `A`-algebra `A'` with a point `φ'` over `φ` and an idempotent `e` of
`A' ⊗[A] B` such that `t` is the only point of `B` over `φ` at which `e` does not vanish
(`Algebra.exists_etale_isIdempotentElem_forall_eq`). This is the geometric-point form of
Mathlib's étale local structure of finite algebras, [Stacks 00UJ]
(`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`), which isolates a *prime*;
to isolate a point one first enlarges the residue field of `φ` by the separable closure of
`κ(ker φ)` in `κ(ker t)` (`Algebra.exists_etale_residueField_equiv`), after which the residue
field extension at `ker t` is purely inseparable, so that a point is determined by its
kernel.

## Main results

- `Algebra.exists_etale_isIdempotentElem_forall_eq`: the splitting at one point.

-/

@[expose] public section

universe u v w

open TensorProduct RingHom

section Helpers

/-- A ring homomorphism of fields is purely inseparable as soon as, after an injective
embedding of its target into a field `L`, every element of the target has a `q`-th power
in the image of the source. -/
lemma RingHom.IsPurelyInseparable.of_comp_eq {F E L : Type*} [Field F] [Field E] [Field L]
    (f : F →+* E) (ι₀ : F →+* L) (ι₁ : E →+* L) (h : ι₁.comp f = ι₀) (q : ℕ) [ExpChar F q]
    (H : ∀ y : E, ∃ n : ℕ, ι₁ y ^ q ^ n ∈ ι₀.range) : f.IsPurelyInseparable := by
  algebraize [f]
  change IsPurelyInseparable F E
  rw [isPurelyInseparable_iff_pow_mem F q]
  intro y
  obtain ⟨n, x, hx⟩ := H y
  refine ⟨n, x, ι₁.injective ?_⟩
  change ι₁ (f x) = ι₁ (y ^ q ^ n)
  rw [← RingHom.comp_apply, h, hx, map_pow]

end Helpers

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {Ω : Type w} [Field Ω]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- long proof with many local algebra instances on residue fields
/-- **Étale-local splitting of a finite algebra at a geometric point.** Let `B` be a finite
`A`-algebra and `t` a point of `B` over a geometric point `φ : A →+* Ω`. Then there is an
étale `A`-algebra `A'` with a point `φ'` over `φ` and an idempotent `e` of `A' ⊗[A] B` which is
`1` at `t` and `0` at every other point of `B` over `φ`. -/
theorem exists_etale_isIdempotentElem_forall_eq [Module.Finite A B] (φ : A →+* Ω)
    (t : PointsOver φ B) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (φ' : A' →+* Ω) (hφ' : φ'.comp (algebraMap A A') = φ) (e : A' ⊗[A] B),
      IsIdempotentElem e ∧ t.tensor hφ' e = 1 ∧
        ∀ t' : PointsOver φ B, t'.tensor hφ' e = 1 → t' = t := by
  classical
  -- Step 1: enlarge the residue field of `φ` by the separable closure of `κ(ker φ)` in
  -- `κ(ker t)`.
  set p : Ideal A := RingHom.ker φ with hp
  set 𝔮 : Ideal B := RingHom.ker t.1 with h𝔮
  have : 𝔮.LiesOver p := t.ker_liesOver
  let := Localization.AtPrime.algebraOfLiesOver p 𝔮
  let K := p.ResidueField
  let L := 𝔮.ResidueField
  let Ks := separableClosure K L
  have : FiniteDimensional K Ks := inferInstance
  obtain ⟨A₁, _, _, _, P₁, _, hP₁, e₁, he₁⟩ := Algebra.exists_etale_residueField_equiv p Ks
  let tL : L →+* Ω := t.residueFieldLift 𝔮 rfl
  -- the point of `A₁` over `φ`
  let φ₁ : A₁ →+* Ω :=
    tL.comp (Ks.val.toRingHom.comp (e₁.toRingHom.comp (algebraMap A₁ P₁.ResidueField)))
  have hφ₁ : φ₁.comp (algebraMap A A₁) = φ := by
    ext a
    simp only [φ₁, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [← Ideal.ResidueField.map_algebraMap p P₁ (algebraMap A A₁) hP₁, he₁,
      IntermediateField.coe_val, ← IntermediateField.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply K Ks L,
      ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]
    exact (PointsOver.residueFieldLift_algebraMap t 𝔮 rfl _).trans (t.apply_algebraMap a)
  have hker₁ : RingHom.ker φ₁ = P₁ := by
    ext x
    simp only [φ₁, RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_eq_zero_iff tL tL.injective, map_eq_zero_iff Ks.val Ks.val.toRingHom.injective,
      map_eq_zero_iff e₁ e₁.injective, Ideal.algebraMap_residueField_eq_zero]
  -- Step 2: the residue field extension of `A₁ ⊗[A] B` over `A₁` at the point `t` is purely
  -- inseparable, since it embeds into `κ(ker t)` over the separable closure.
  let ι₀ : P₁.ResidueField →+* L := Ks.val.toRingHom.comp e₁.toRingHom
  let φ₁L : A₁ →+* L := ι₀.comp (algebraMap A₁ P₁.ResidueField)
  have hφ₁L : φ₁L.comp (algebraMap A A₁) = algebraMap A L := by
    ext a
    simp only [φ₁L, ι₀, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [← Ideal.ResidueField.map_algebraMap p P₁ (algebraMap A A₁) hP₁, he₁,
      IntermediateField.coe_val, ← IntermediateField.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply K Ks L, ← IsScalarTower.algebraMap_apply A K L]
  let tB : PointsOver (algebraMap A L) B :=
    ⟨algebraMap B L, (IsScalarTower.algebraMap_eq A B L).symm⟩
  let θ : PointsOver φ₁L (A₁ ⊗[A] B) := tB.tensor hφ₁L
  have hθ : tL.comp θ.1 = (t.tensor hφ₁).1 := by
    let := φ.toAlgebra
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a₁ b =>
      simp only [RingHom.comp_apply, θ, PointsOver.tensor_tmul, map_mul]
      congr 1
      exact PointsOver.residueFieldLift_algebraMap t 𝔮 rfl b
    | add x y hx hy => simp only [map_add, hx, hy]
  set 𝔮₁ : Ideal (A₁ ⊗[A] B) := RingHom.ker (t.tensor hφ₁).1 with h𝔮₁
  have hθker : RingHom.ker θ.1 = 𝔮₁ := by
    rw [h𝔮₁, ← hθ, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot tL).mp tL.injective,
      ← RingHom.ker_eq_comap_bot]
  have h𝔮₁P₁ : 𝔮₁.LiesOver P₁ := by
    rw [← hker₁]
    exact (t.tensor hφ₁).ker_liesOver
  -- the residue field embedding of `𝔮₁` into `L`
  let ι₁ : 𝔮₁.ResidueField →+* L := θ.residueFieldLift 𝔮₁ hθker
  have hι₁ : ι₁.comp (Ideal.ResidueField.map P₁ 𝔮₁ (algebraMap A₁ _) (𝔮₁.over_def P₁)) = ι₀ := by
    refine Ideal.ResidueField.ringHom_ext ?_
    ext a
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap, ι₁,
      PointsOver.residueFieldLift_algebraMap]
    exact θ.apply_algebraMap a
  have hpi₁ : (Ideal.ResidueField.map P₁ 𝔮₁ (algebraMap A₁ _)
      (𝔮₁.over_def P₁)).IsPurelyInseparable := by
    refine RingHom.IsPurelyInseparable.of_comp_eq _ ι₀ ι₁ hι₁ (ringExpChar P₁.ResidueField) ?_
    intro y
    have : ExpChar Ks (ringExpChar P₁.ResidueField) :=
      expChar_of_injective_ringHom (f := e₁.toRingHom) e₁.injective _
    obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem Ks (ringExpChar P₁.ResidueField) (ι₁ y)
    refine ⟨n, e₁.symm z, ?_⟩
    rw [← hz]
    simp [ι₀]
  -- Step 3: isolate the prime `𝔮₁` by Mathlib's étale local structure of finite algebras.
  have : Algebra.QuasiFiniteAt A₁ 𝔮₁ := inferInstance
  obtain ⟨A₂, _, _, _, P₂, _, _, e, he, P', _, _, hP'q, heP', hres₂, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq P₁ 𝔮₁
  -- Step 4: the point of `A₂` over `φ₁`, through `κ(P₂) ≅ κ(P₁)`.
  let E : P₁.ResidueField ≃+* P₂.ResidueField :=
    RingEquiv.ofBijective (Ideal.ResidueField.map P₁ P₂ (algebraMap A₁ A₂) (P₂.over_def P₁)) hres₂
  let ρ₁ : P₁.ResidueField →+* Ω := tL.comp ι₀
  have hρ₁ : ρ₁.comp (algebraMap A₁ P₁.ResidueField) = φ₁ := rfl
  let φ₂ : A₂ →+* Ω := ρ₁.comp (E.symm.toRingHom.comp (algebraMap A₂ P₂.ResidueField))
  have hφ₂ : φ₂.comp (algebraMap A₁ A₂) = φ₁ := by
    ext a
    simp only [φ₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← Ideal.ResidueField.map_algebraMap P₁ P₂ (algebraMap A₁ A₂) (P₂.over_def P₁)]
    have hE : E (algebraMap A₁ P₁.ResidueField a) = Ideal.ResidueField.map P₁ P₂ (algebraMap A₁ A₂)
        (P₂.over_def P₁) (algebraMap A₁ P₁.ResidueField a) := RingEquiv.ofBijective_apply _ _ _
    rw [← hE, E.symm_apply_apply]
    exact RingHom.congr_fun hρ₁ a
  have hker₂ : RingHom.ker φ₂ = P₂ := by
    ext x
    simp only [φ₂, RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [map_eq_zero_iff ρ₁ ρ₁.injective, map_eq_zero_iff E.symm E.symm.injective,
      Ideal.algebraMap_residueField_eq_zero]
  -- Step 5: assemble. `A' := A₂` as an `A`-algebra, and the idempotent transported to
  -- `A₂ ⊗[A] B`.
  let _ : Algebra A A₂ := ((algebraMap A₁ A₂).comp (algebraMap A A₁)).toAlgebra
  have : IsScalarTower A A₁ A₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale A A₂ := Algebra.Etale.comp A A₁ A₂
  have hφ₂' : φ₂.comp (algebraMap A A₂) = φ := by
    rw [IsScalarTower.algebraMap_eq A A₁ A₂, ← RingHom.comp_assoc, hφ₂, hφ₁]
  let ψ : A₂ ⊗[A₁] (A₁ ⊗[A] B) ≃ₐ[A₂] A₂ ⊗[A] B :=
    Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B
  -- the points of `A₂ ⊗[A₁] (A₁ ⊗[A] B)` over `φ₂` are the points of `A₂ ⊗[A] B` over `φ₂`
  have hψ : ∀ (t' : PointsOver φ B) (x : A₂ ⊗[A₁] (A₁ ⊗[A] B)), (t'.tensor hφ₂') (ψ x) =
      ((t'.tensor hφ₁).tensor hφ₂) x := by
    intro t' x
    let := φ.toAlgebra
    induction x using TensorProduct.inductionOn with
    | tmul a₂ y =>
      induction y using TensorProduct.inductionOn with
      | tmul a₁ b =>
        rw [show ψ (a₂ ⊗ₜ (a₁ ⊗ₜ b)) = (a₁ • a₂) ⊗ₜ b from
          Algebra.TensorProduct.cancelBaseChange_tmul A A₁ A₂ A₂ B a₂ a₁ b]
        simp only [PointsOver.tensor_tmul, Algebra.smul_def, map_mul]
        rw [← RingHom.comp_apply φ₂ (algebraMap A₁ A₂), hφ₂]
        ring
      | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- the kernel of the point `t` in `A₂ ⊗[A₁] (A₁ ⊗[A] B)` is `P'`
  have hker' : ∀ t' : PointsOver φ B, (RingHom.ker ((t'.tensor hφ₁).tensor hφ₂).1).LiesOver P₂ := by
    intro t'
    rw [← hker₂]
    exact ((t'.tensor hφ₁).tensor hφ₂).ker_liesOver
  have hkerR : ∀ t' : PointsOver φ B, (RingHom.ker ((t'.tensor hφ₁).tensor hφ₂).1).comap
      Algebra.TensorProduct.includeRight.toRingHom = RingHom.ker (t'.tensor hφ₁).1 :=
    fun t' ↦ PointsOver.ker_tensor_comap_includeRight hφ₂ _
  have hP'𝔮₁ : P'.LiesOver 𝔮₁ := ⟨hP'q.symm⟩
  have hkt : RingHom.ker ((t.tensor hφ₁).tensor hφ₂).1 = P' := by
    have := hker' t
    have : (RingHom.ker ((t.tensor hφ₁).tensor hφ₂).1).LiesOver 𝔮₁ := ⟨(hkerR t).symm⟩
    exact Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hres₂ _ _
      ((hkerR t).trans hP'q.symm)
  refine ⟨A₂, inferInstance, inferInstance, inferInstance, φ₂, hφ₂', ψ e, he.map ψ.toRingHom,
    ?_, ?_⟩
  · -- `e` does not lie in the kernel of the point `t`, so its value is a nonzero idempotent.
    rw [hψ]
    have hne : ((t.tensor hφ₁).tensor hφ₂).1 e ≠ 0 := fun h0 ↦
      heP' (hkt ▸ RingHom.mem_ker.mpr h0)
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp
      (he.map ((t.tensor hφ₁).tensor hφ₂).1)).resolve_left hne
  · intro t' ht'
    -- the kernel of `t'` is a prime over `P₂` not containing `e`, hence equal to `P'`
    rw [hψ] at ht'
    have hkt' : RingHom.ker ((t'.tensor hφ₁).tensor hφ₂).1 = P' := by
      refine huniq _ inferInstance (hker' t') fun h0 ↦ ?_
      have h0' : ((t'.tensor hφ₁).tensor hφ₂).1 e = 0 := RingHom.mem_ker.mp h0
      exact one_ne_zero (ht'.symm.trans h0')
    -- the residue field extension of `P'` over `P₂` is purely inseparable
    have hpi' : (Ideal.ResidueField.map P₂ P' (algebraMap A₂ _)
        (P'.over_def P₂)).IsPurelyInseparable := by
      have h₁ := Ideal.ResidueField.bijective_map_includeRight P₁ P₂ (P₂.over_def P₁) hres₂ 𝔮₁ P'
        hP'q.symm (P'.over_def P₂)
      refine RingHom.IsPurelyInseparable.of_comp_eq_comp'
        (e := Ideal.ResidueField.map P₁ P₂ (algebraMap A₁ A₂) (P₂.over_def P₁))
        (e' := Ideal.ResidueField.map 𝔮₁ P' Algebra.TensorProduct.includeRight.toRingHom hP'q.symm)
        hres₂ h₁ ?_ hpi₁
      refine Ideal.ResidueField.ringHom_ext ?_
      ext a
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      rw [← IsScalarTower.algebraMap_apply A₁ A₂ (A₂ ⊗[A₁] (A₁ ⊗[A] B)),
        IsScalarTower.algebraMap_apply A₁ (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B))]
      rfl
    have h₂ : (t'.tensor hφ₁).tensor hφ₂ = (t.tensor hφ₁).tensor hφ₂ :=
      PointsOver.ext_of_ker_eq_of_isPurelyInseparable' P₂ hker₂ P' hkt' hkt hpi'
    exact (PointsOver.tensorEquiv hφ₁).symm.injective
      ((PointsOver.tensorEquiv hφ₂).symm.injective h₂)

end Algebra

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {Ω : Type w} [Field Ω] [IsAlgClosed Ω]

/-- **Shrinking away from an idempotent without points.** Let `B` be a finite `A`-algebra and
`e` an idempotent of `B` vanishing at every point of `B` over a geometric point `φ` of `A`.
Then `e` vanishes after inverting an element `a` of `A` with `φ a ≠ 0`: the support of `e`
is closed in `Spec B`, its image in `Spec A` is closed and does not contain `ker φ`. -/
theorem exists_algebraMap_mul_eq_zero_of_forall_apply_eq_zero [Module.Finite A B]
    (φ : A →+* Ω) (e : B) (he : IsIdempotentElem e) (h : ∀ t : PointsOver φ B, t e = 0) :
    ∃ a : A, φ a ≠ 0 ∧ algebraMap A B a * e = 0 := by
  classical
  -- the primes of `B` not containing `e` are those containing `1 - e`
  set Z : Set (PrimeSpectrum A) :=
    PrimeSpectrum.comap (algebraMap A B) '' PrimeSpectrum.zeroLocus {1 - e} with hZ
  have hZc : IsClosed Z :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _
      ((algebraMap_isIntegral_iff (R := A) (A := B)).mpr inferInstance) _
      (PrimeSpectrum.isClosed_zeroLocus _)
  have hp : (⟨RingHom.ker φ, inferInstance⟩ : PrimeSpectrum A) ∉ Z := by
    rintro ⟨x, hx, hxp⟩
    have : x.asIdeal.LiesOver (RingHom.ker φ) := ⟨(PrimeSpectrum.ext_iff.mp hxp).symm⟩
    obtain ⟨t, ht⟩ := PointsOver.exists_ker_eq (φ := φ) x.asIdeal
    have h1 : 1 - e ∈ x.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hx (Set.mem_singleton _)
    rw [← ht, RingHom.mem_ker, map_sub, map_one, h t, sub_zero] at h1
    exact one_ne_zero h1
  obtain ⟨_, ⟨a, rfl⟩, ha, haZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hZc.isOpen_compl
  -- `a * e` lies in every prime of `B`, hence is nilpotent
  have hnil : IsNilpotent (algebraMap A B a * e) := by
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    rintro 𝔯 (h𝔯 : 𝔯.IsPrime)
    by_cases hea : algebraMap A B a ∈ 𝔯
    · exact 𝔯.mul_mem_right _ hea
    · refine 𝔯.mul_mem_left _ ?_
      by_contra hne
      have hmem : (⟨𝔯, h𝔯⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.zeroLocus {1 - e} := by
        rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
        refine (h𝔯.mem_or_mem (x := e) (y := 1 - e) ?_).resolve_left hne
        rw [he.mul_one_sub_self]
        exact 𝔯.zero_mem
      have hZ𝔯 : PrimeSpectrum.comap (algebraMap A B) ⟨𝔯, h𝔯⟩ ∈ Z := ⟨_, hmem, rfl⟩
      refine hea ?_
      by_contra hea'
      exact haZ (show PrimeSpectrum.comap (algebraMap A B) ⟨𝔯, h𝔯⟩ ∈ PrimeSpectrum.basicOpen a
        from hea') hZ𝔯
  obtain ⟨n, hn⟩ := hnil
  refine ⟨a ^ (n + 1), ?_, ?_⟩
  · rw [map_pow]
    refine pow_ne_zero _ fun ha0 ↦ ?_
    exact ha (show a ∈ (⟨RingHom.ker φ, inferInstance⟩ : PrimeSpectrum A).asIdeal from ha0)
  · rw [map_pow, ← he.pow_succ_eq n, ← mul_pow, pow_succ, hn, zero_mul]

end Algebra

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {Ω : Type w} [Field Ω]

-- induction over the finite set of points, with a tensor product bookkeeping at each step
/-- Auxiliary statement for `Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq`:
orthogonal idempotents separating the points in a finite set `S`. -/
private lemma exists_etale_orthogonalIdempotents_aux [Module.Finite A B] (φ : A →+* Ω)
    [DecidableEq (PointsOver φ B)] (S : Finset (PointsOver φ B)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (φ' : A' →+* Ω) (hφ' : φ'.comp (algebraMap A A') = φ) (e : PointsOver φ B → A' ⊗[A] B),
      (∀ t ∈ S, IsIdempotentElem (e t)) ∧ (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → e t * e t' = 0) ∧
      (∀ t ∈ S, ∀ t', t'.tensor hφ' (e t) = if t' = t then 1 else 0) := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨A, inferInstance, inferInstance, inferInstance, φ,
      RingHom.ext fun a ↦ congrArg φ (Algebra.algebraMap_self_apply a), fun _ ↦ 0, by simp,
      by simp, by simp⟩
  | insert t₀ S ht₀S ih =>
    obtain ⟨A', _, _, _, φ', hφ', e, he, hortho, hval⟩ := ih
    -- isolate the point `t₀` over `A'`
    obtain ⟨A'', _, _, _, φ'', hφ'', e'', he'', h₁, h₂⟩ :=
      exists_etale_isIdempotentElem_forall_eq (A := A') (B := A' ⊗[A] B) φ' (t₀.tensor hφ')
    let _ : Algebra A A'' := ((algebraMap A' A'').comp (algebraMap A A')).toAlgebra
    have : IsScalarTower A A' A'' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.Etale A A'' := Algebra.Etale.comp A A' A''
    have hφ''A : φ''.comp (algebraMap A A'') = φ := PointsOver.comp_algebraMap_of_tower hφ' hφ''
    let ψ : A'' ⊗[A'] (A' ⊗[A] B) ≃ₐ[A''] A'' ⊗[A] B :=
      Algebra.TensorProduct.cancelBaseChange A A' A'' A'' B
    let f : A' ⊗[A] B →ₐ[A] A'' ⊗[A] B :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' A'') (AlgHom.id A B)
    -- the new family of idempotents
    let e' : PointsOver φ B → A'' ⊗[A] B := fun t ↦
      if t = t₀ then ψ e'' * ∏ s ∈ S, (1 - f (e s)) else f (e t)
    have hidem : ∀ t ∈ S, IsIdempotentElem (f (e t)) := fun t ht ↦ (he t ht).map f
    have hprod : IsIdempotentElem (∏ s ∈ S, (1 - f (e s))) := by
      refine Finset.prod_induction _ IsIdempotentElem (fun x y hx hy ↦ ?_) ?_ ?_
      · exact IsIdempotentElem.mul_of_commute (Commute.all _ _) hx hy
      · exact IsIdempotentElem.one
      · exact fun s hs ↦ (hidem s hs).one_sub
    have hval' : ∀ (t' : PointsOver φ B) (x : A' ⊗[A] B), t'.tensor hφ''A (f x) = t'.tensor hφ' x :=
      fun t' x ↦ PointsOver.tensor_map hφ' hφ'' t' x
    have hval'' : ∀ (t' : PointsOver φ B) (x : A'' ⊗[A'] (A' ⊗[A] B)),
        t'.tensor hφ''A (ψ x) = (t'.tensor hφ').tensor hφ'' x :=
      fun t' x ↦ PointsOver.tensor_cancelBaseChange hφ' hφ'' t' x
    -- the value of `e'' ` at a point `t' ≠ t₀` is zero
    have hzero : ∀ t' : PointsOver φ B, t' ≠ t₀ → (t'.tensor hφ').tensor hφ'' e'' = 0 := by
      intro t' ht'
      refine (IsIdempotentElem.iff_eq_zero_or_one.mp
        (he''.map ((t'.tensor hφ').tensor hφ'').1)).resolve_right fun h ↦ ht' ?_
      exact (PointsOver.tensorEquiv hφ').symm.injective (h₂ _ h)
    refine ⟨A'', inferInstance, inferInstance, inferInstance, φ'', hφ''A, e', ?_, ?_, ?_⟩
    · intro t ht
      simp only [e']
      split_ifs with h
      · exact IsIdempotentElem.mul_of_commute (Commute.all _ _) (he''.map ψ.toRingHom) hprod
      · exact hidem t (Finset.mem_of_mem_insert_of_ne ht h)
    · intro t ht t' ht' htt'
      simp only [e']
      -- a product of the form `(1 - x) * x` with `x` idempotent appears in each case
      have key : ∀ s ∈ S, (∏ s ∈ S, (1 - f (e s))) * f (e s) = 0 := by
        intro s hs
        rw [← Finset.mul_prod_erase S _ hs, mul_assoc, mul_comm (∏ x ∈ S.erase s, (1 - f (e x))),
          ← mul_assoc, (hidem s hs).one_sub_mul_self, zero_mul]
      split_ifs with h h' h'
      · exact absurd (h.trans h'.symm) htt'
      · have hs := Finset.mem_of_mem_insert_of_ne ht' h'
        rw [mul_assoc, key t' hs, mul_zero]
      · have hs := Finset.mem_of_mem_insert_of_ne ht h
        rw [mul_comm, mul_assoc, key t hs, mul_zero]
      · have hs := Finset.mem_of_mem_insert_of_ne ht h
        have hs' := Finset.mem_of_mem_insert_of_ne ht' h'
        rw [← map_mul, hortho t hs t' hs' htt', map_zero]
    · intro t ht t'
      by_cases h : t = t₀
      · rw [show e' t = ψ e'' * ∏ s ∈ S, (1 - f (e s)) from ite_eq_left h, map_mul, hval'',
          map_prod]
        simp only [map_sub, map_one, hval']
        by_cases ht' : t' = t
        · rw [ite_eq_left ht', ht', h, h₁, one_mul]
          refine Finset.prod_eq_one fun s hs ↦ ?_
          rw [hval s hs, ite_eq_right (fun h' : t₀ = s ↦ ht₀S (h' ▸ hs)), sub_zero]
        · rw [ite_eq_right ht']
          by_cases ht'S : t' ∈ S
          · rw [Finset.prod_eq_zero ht'S (by rw [hval t' ht'S, ite_eq_left rfl, sub_self]),
              mul_zero]
          · rw [hzero t' (fun h' ↦ ht' (h'.trans h.symm)), zero_mul]
      · rw [show e' t = f (e t) from ite_eq_right h, hval']
        exact hval t (Finset.mem_of_mem_insert_of_ne ht h) t'

variable [IsAlgClosed Ω]

end Algebra

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {Ω : Type w} [Field Ω] [IsAlgClosed Ω]

/-- **Étale-local splitting of a finite algebra at a geometric point.** Let `B` be a finite
`A`-algebra and `φ : A →+* Ω` a geometric point of `A`, `Ω` algebraically closed. Then there is
an étale `A`-algebra `A'` with a point `φ'` over `φ` and a complete family of orthogonal
idempotents `e t` of `A' ⊗[A] B`, indexed by the points `t` of `B` over `φ`, such that `e t` is
`1` at `t` and `0` at every other point over `φ`. Geometrically: étale-locally at `φ`, `Spec B`
decomposes as a disjoint union of open and closed subschemes, each containing exactly one
geometric point over `φ`. -/
theorem exists_etale_completeOrthogonalIdempotents_forall_tensor_eq [Module.Finite A B]
    (φ : A →+* Ω) [Fintype (PointsOver φ B)] [DecidableEq (PointsOver φ B)] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (φ' : A' →+* Ω) (hφ' : φ'.comp (algebraMap A A') = φ) (e : PointsOver φ B → A' ⊗[A] B),
      CompleteOrthogonalIdempotents e ∧
        ∀ t t' : PointsOver φ B, t'.tensor hφ' (e t) = if t' = t then 1 else 0 := by
  classical
  obtain ⟨A', _, _, _, φ', hφ', e, he, hortho, hval⟩ :=
    exists_etale_orthogonalIdempotents_aux (B := B) φ Finset.univ
  have hoi : OrthogonalIdempotents e :=
    ⟨fun t ↦ he t (Finset.mem_univ _),
      fun t t' h ↦ hortho t (Finset.mem_univ _) t' (Finset.mem_univ _) h⟩
  -- the idempotent `1 - ∑ e t` vanishes at every point over `φ'`
  have hsum : IsIdempotentElem (1 - ∑ t, e t) := hoi.isIdempotentElem_sum.one_sub
  have hzero : ∀ t' : PointsOver φ' (A' ⊗[A] B), t' (1 - ∑ t, e t) = 0 := by
    intro t'
    obtain ⟨t', rfl⟩ := (PointsOver.tensorEquiv hφ').symm.surjective t'
    rw [PointsOver.tensorEquiv_symm_apply, map_sub, map_one, map_sum]
    simp only [hval _ (Finset.mem_univ _)]
    simp
  obtain ⟨a, ha, hae⟩ := exists_algebraMap_mul_eq_zero_of_forall_apply_eq_zero φ' _ hsum hzero
  -- invert `a`
  let A'' := Localization.Away a
  let φ'' : A'' →+* Ω := IsLocalization.Away.lift a (g := φ') (isUnit_iff_ne_zero.2 ha)
  have hφ'' : φ''.comp (algebraMap A' A'') = φ' := IsLocalization.lift_comp _
  have : Algebra.Etale A A'' := Algebra.Etale.comp A A' A''
  have hφ''A : φ''.comp (algebraMap A A'') = φ := PointsOver.comp_algebraMap_of_tower hφ' hφ''
  let f : A' ⊗[A] B →ₐ[A] A'' ⊗[A] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' A'') (AlgHom.id A B)
  refine ⟨A'', inferInstance, inferInstance, inferInstance, φ'', hφ''A, fun t ↦ f (e t), ?_, ?_⟩
  · refine ⟨hoi.map f.toRingHom, ?_⟩
    -- `a` is a unit in `A''`, so `f (1 - ∑ e t) = 0`
    have hu : IsUnit (algebraMap A'' (A'' ⊗[A] B) (algebraMap A' A'' a)) :=
      (IsLocalization.Away.algebraMap_isUnit a).map _
    have h0 : algebraMap A'' (A'' ⊗[A] B) (algebraMap A' A'' a) * (1 - ∑ t, f (e t)) = 0 := by
      rw [← map_sum, ← map_one f, ← map_sub, ← IsScalarTower.algebraMap_apply A' A'' _]
      have : algebraMap A' (A'' ⊗[A] B) a = f (algebraMap A' (A' ⊗[A] B) a) := by
        simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, f,
          IsScalarTower.coe_toAlgHom', map_one, Algebra.algebraMap_self_apply]
        rw [IsScalarTower.algebraMap_apply A' A'' (A'' ⊗[A] B),
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [this, ← map_mul, hae, map_zero]
    have := hu.mul_right_eq_zero.mp h0
    exact (sub_eq_zero.mp this).symm
  · intro t t'
    exact (PointsOver.tensor_map hφ' hφ'' t' (e t)).trans (hval t (Finset.mem_univ _) t')

end Algebra
