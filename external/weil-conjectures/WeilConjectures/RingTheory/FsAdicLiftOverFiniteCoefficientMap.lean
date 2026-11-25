/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FsAdicClosedFiberModel
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteCoefficientTensorReductionSurjective
import WeilConjectures.RingTheory.FiniteCoefficientTensorKernelReduction
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import WeilConjectures.RingTheory.FiniteModuleComplete

/-!
# Lifting over a finite coefficient map

Source: Stacks Project, More on Algebra, Remark 07NS (parts (3), (4)),
Lemmas 07NR and 07NJ, and Proposition 07PM.
(blueprint: lem-weil-pbc-fs-adic-lift-over-finite-coefficient-map)
-/

@[expose] public section

universe u v w

namespace RingHom

private theorem closed_ideal_of_complete_local
    {R : Type w} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    J = ⨅ (n : ℕ) (_ : 1 ≤ n), J ⊔ IsLocalRing.maximalIdeal R ^ n := by
  have hproper : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJ
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J) =
      IsLocalRing.maximalIdeal (R ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  apply le_antisymm
  · exact le_iInf fun n ↦ le_iInf fun _ ↦ le_sup_left
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hzero := Ideal.iInf_pow_eq_bot_of_isLocalRing
      (IsLocalRing.maximalIdeal (R ⧸ J))
      (IsLocalRing.maximalIdeal.isMaximal (R ⧸ J)).ne_top
    have hmem : Ideal.Quotient.mk J x ∈
        ⨅ n : ℕ, IsLocalRing.maximalIdeal (R ⧸ J) ^ n := by
      refine Ideal.mem_iInf.mpr fun n ↦ ?_
      by_cases hn : 1 ≤ n
      · have hx' := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx n) hn
        have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hx'
        simp only [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow,
          hmax] at h
        exact h
      · have : n = 0 := Nat.eq_zero_of_not_pos hn
        simp [this]
    simpa only [hzero, Ideal.mem_bot] using hmem

/-- Lifting a formally smooth complete local algebra along a finite coefficient map.

Source: Stacks Project, More on Algebra, Remark 07NS (parts (3), (4)),
Lemmas 07NR and 07NJ, and Proposition 07PM.
(blueprint: lem-weil-pbc-fs-adic-lift-over-finite-coefficient-map)

Proof (the eight steps of the node):
1. The closed fibre E = B/m_A B is complete Noetherian local by
   `lem-weil-pbc-complete-local-quotient`. Its maximal ideal is the image of m_B.
   The induced residue-field isomorphism transports its formal smoothness over
   k = A/m_A to k₀ = A₀/m₀ (`theorem-finite-etale-covers-proper-henselian--2`).
2. Apply `lem-weil-pbc-fs-adic-lift-from-residue-field` to A₀ and E. Obtain a
   complete Noetherian local C, a local formally smooth γ : A₀ → C, and an
   A₀-algebra isomorphism C/m₀C ≅ E. The resulting θ : C → E is surjective,
   has kernel m₀C, and maps m_C onto the maximal ideal of E.
3. Apply `lem-weil-pbc-fs-adic-lift-into-complete` to lift θ through B → E.
   The ideal m_A B lies in m_B and is m_B-adically closed by
   `lem-weil-pbc-krull-intersection-jacobson`. The lift ψ is an A₀-algebra map,
   hence ψγ = φα, and is local because θ maps m_C into the maximal ideal of E.
4. The finite k₀-algebra A/m₀A is Artinian local. By
   `lem-weil-pbc-artinian-local-noetherian-nilpotent`, some positive power
   of m_A is contained in m₀A (`def-weil-finitely-generated-module`).
5. Form D = C ⊗[A₀] A and Φ(c ⊗ a) = ψ(c)φ(a), using
   `lem-weil-pbc-algebra-tensor-pushout-universal-property` and
   `def-weil-module-base-change`. Finite module generators of A give finite
   C-module generators of D. By `lem-weil-pbc-finite-algebra-noetherian` and
   `lem-weil-pbc-finite-algebra-local-radical`, D is Noetherian and m_C D is
   in every maximal ideal. Step 4 then puts m_A D in the Jacobson radical.
6. Since θ is onto, B = ψ(C) + m_A B. Iterating and using Step 4 gives
   B = Φ(D) + m_C B. The images of the chosen finite generators generate
   B/m_C B. Locality of ψ and `lem-weil-pbc-krull-intersection-jacobson`
   make B m_C-adically separated. By `lem-weil-pbc-finite-over-complete-ring`,
   those images generate B over C; thus Φ is surjective.
7. Put K = ker Φ. Flatness of B over A (`def-weil-pbc-flat-ring-map`) and
   `lem-weil-pbc-flat-quotient-tensor-injective` make K/m_A K inject into
   D/m_A D. The latter maps isomorphically to E: residue surjectivity reduces
   every tensor to c ⊗ 1, and θ(c) = 0 means c ∈ m₀C, hence c ⊗ 1 ∈ m_A D.
   Therefore K/m_A K = 0. Since D is Noetherian and m_A D lies in its
   Jacobson radical, `lem-weil-pbc-nakayama-jacobson` gives K = 0.
8. Thus Φ is bijective, yielding the required ring isomorphism, with C, γ,
   and ψ having all the properties from Steps 2 and 3.
-/
theorem exists_fs_adic_lift_over_finite_coefficient_map
    {A₀ : Type u} {A : Type v} {B : Type w}
    [CommRing A₀] [CommRing A] [CommRing B]
    [Algebra A₀ A] [Algebra A B]
    [IsNoetherianRing A₀] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    [Module.Finite A₀ A]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (φ : A →+* B) (hφ : algebraMap A B = φ) [IsLocalHom φ] (hflat : RingHom.Flat φ) :
    letI : Algebra (IsLocalRing.ResidueField A)
        (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Eq.mpr (congrArg (fun f : A →+* B => IsLocalRing.maximalIdeal A ≤
          (Ideal.map φ (IsLocalRing.maximalIdeal A)).comap f) hφ)
          Ideal.le_comap_map)
    Algebra.FormallySmoothAdic (IsLocalRing.ResidueField A)
      (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))
      (Ideal.map (Ideal.Quotient.mk (Ideal.map φ (IsLocalRing.maximalIdeal A)))
        (IsLocalRing.maximalIdeal B)) →
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : IsLocalRing C)
      (_ : Algebra A₀ C),
      IsNoetherianRing C ∧
      IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧
      ∃ (γ : A₀ →+* C),
        algebraMap A₀ C = γ ∧ IsLocalHom γ ∧
        Algebra.FormallySmoothAdic A₀ C (IsLocalRing.maximalIdeal C) ∧
        ∃ (ψ : C →+* B),
          IsLocalHom ψ ∧ ψ.comp γ = φ.comp α ∧
          ∃ F : RingHom (TensorProduct A₀ C A) B,
            Function.Bijective F ∧
            ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a := by
  intro hfs
  obtain ⟨C, instC, instLocalC, instAlgC, hnoeth, hcomplete, γ, hγ, hlocalγ,
    hsmooth, θ, hsurjθ, hkerθ, hθγ⟩ :=
    exists_fs_adic_closed_fiber_model α hα hres φ hφ hfs
  let : CommRing C := instC
  let : IsLocalRing C := instLocalC
  let : Algebra A₀ C := instAlgC
  let : IsNoetherianRing C := hnoeth
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := hcomplete
  let : IsLocalHom γ := hlocalγ
  let : Algebra A₀ B := (φ.comp α).toAlgebra
  let J : Ideal B := (IsLocalRing.maximalIdeal A).map φ
  have hJ : J ≤ IsLocalRing.maximalIdeal B := IsLocalRing.map_maximalIdeal_le φ
  have hproper : J ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top hJ
  let : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let g : C →ₐ[A₀] B ⧸ J :=
    { θ with
      commutes' := fun a ↦ by
        change θ (algebraMap A₀ C a) = Ideal.Quotient.mk J (φ (α a))
        rw [hγ]
        exact RingHom.congr_fun hθγ a }
  have hg : ∀ x ∈ IsLocalRing.maximalIdeal C ^ 1,
      g x ∈ (IsLocalRing.maximalIdeal B).map (Ideal.Quotient.mk J) := by
    intro x hx
    let : IsLocalHom θ := IsLocalHom.of_surjective θ hsurjθ
    have h := map_nonunit θ x (by simpa using hx)
    rwa [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective] at h
  obtain ⟨ψalg, hψθ, hψm⟩ := hsmooth.exists_lift_into_complete
    (IsLocalRing.maximalIdeal C) (IsLocalRing.maximalIdeal B) J
    1 le_rfl (by simpa using hJ) (closed_ideal_of_complete_local J hJ) g
    1 le_rfl hg
  let ψ : C →+* B := ψalg.toRingHom
  have hlocalψ : IsLocalHom ψ := by
    refine ⟨fun x hx ↦ ?_⟩
    by_contra hunit
    have hx' : x ∈ IsLocalRing.maximalIdeal C := hunit
    have hmem : ψ x ∈ IsLocalRing.maximalIdeal B := by
      change ψalg x ∈ IsLocalRing.maximalIdeal B
      simpa only [mul_one, pow_one] using hψm x (by simpa using hx')
    exact hmem hx
  have hψγ : ψ.comp γ = φ.comp α := by
    ext a
    change ψalg (γ a) = (algebraMap A₀ B) a
    rw [← hγ]
    exact ψalg.commutes a
  have hqψ : (Ideal.Quotient.mk J).comp ψ = θ := by
    ext x
    exact AlgHom.congr_fun hψθ x
  let : IsLocalHom ψ := hlocalψ
  let φalg : A →ₐ[A₀] B :=
    { φ with
      commutes' := fun a ↦ by
        change φ (algebraMap A₀ A a) = φ (α a)
        rw [hα] }
  let F : TensorProduct A₀ C A →+* B :=
    (Algebra.TensorProduct.productMap ψalg φalg).toRingHom
  have hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a := by
    intro c a
    rfl
  let D := TensorProduct A₀ C A
  let I : Ideal D := (IsLocalRing.maximalIdeal C).map (algebraMap C D)
  have hleft : F.comp (algebraMap C D) = ψ := by
    ext c
    change F (TensorProduct.tmul A₀ c 1) = ψ c
    rw [hF, map_one, mul_one]
  have hmap : I.map F = (IsLocalRing.maximalIdeal C).map ψ := by
    change ((IsLocalRing.maximalIdeal C).map (algebraMap C D)).map F = _
    rw [Ideal.map_map, hleft]
  let : Module.Finite C D := inferInstance
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) D :=
    finite_module_complete_over_complete_noetherian C (IsLocalRing.maximalIdeal C) D
  let : IsAdicComplete I D :=
    (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal C) D).mpr inferInstance
  let : IsHausdorff (I.map F) B := by
    apply IsHausdorff.of_isLocalRing
    rw [hmap]
    exact (IsLocalRing.map_maximalIdeal_lt_top ψ).ne
  have hsurj : Function.Surjective F := by
    apply surjective_of_mk_map_comp_surjective F (I := I)
    rw [hmap]
    exact finite_coefficient_tensor_reduction_surjective α hα γ hγ φ ψ hψγ F hF
      (by rw [hqψ]; exact hsurjθ)
  let ιA : A →+* D := Algebra.TensorProduct.includeRight.toRingHom
  let L : Ideal D := (IsLocalRing.maximalIdeal A).map ιA
  have hbase : ιA.comp α = (algebraMap C D).comp γ := by
    ext a
    rw [← hα, ← hγ]
    exact (Algebra.TensorProduct.includeRight.commutes a).trans
      (Algebra.TensorProduct.includeLeft.commutes a).symm
  have hrad : L ≤ Ideal.jacobson (⊥ : Ideal D) := by
    apply le_sInf
    intro M hM
    let : M.IsMaximal := hM.2
    let : (M.comap (algebraMap C D)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hMC : M.comap (algebraMap C D) = IsLocalRing.maximalIdeal C :=
      IsLocalRing.eq_maximalIdeal (inferInstance)
    have hM₀ : (M.comap ιA).comap (algebraMap A₀ A) =
        IsLocalRing.maximalIdeal A₀ := by
      rw [Ideal.comap_comap, hα, hbase, ← Ideal.comap_comap, hMC]
      exact IsLocalRing.maximalIdeal_comap γ
    let : (M.comap ιA).IsPrime := Ideal.comap_isPrime ιA M
    let : (M.comap ιA).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under _
        (hM₀.symm ▸ IsLocalRing.maximalIdeal.isMaximal A₀)
    have hMA : M.comap ιA = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (inferInstance)
    exact Ideal.map_le_iff_le_comap.mpr hMA.symm.le
  let : IsNoetherianRing D := IsNoetherianRing.of_finite C D
  have hK : (RingHom.ker F : Submodule D D) ≤ L • (RingHom.ker F : Submodule D D) :=
    finite_coefficient_tensor_kernel_reduction α hα hres γ hγ φ ψ hψγ F hF hflat hsurj
      (by rw [hqψ]; exact hkerθ)
  have hker : RingHom.ker F = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot L (RingHom.ker F)
      (IsNoetherian.noetherian _) hK hrad
  have hinj : Function.Injective F := (RingHom.injective_iff_ker_eq_bot F).mpr hker
  exact ⟨C, instC, instLocalC, instAlgC, hnoeth, hcomplete, γ, hγ, hlocalγ,
    hsmooth, ψ, hlocalψ, hψγ, F, ⟨hinj, hsurj⟩, hF⟩

end RingHom
