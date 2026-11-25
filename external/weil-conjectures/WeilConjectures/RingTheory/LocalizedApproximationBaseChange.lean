/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.LocalizedApproximationColimits
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Transition base changes after localization at compatible primes

Source: Stacks Project, Algebra, Tag 02JO, first paragraph, and Tag 00QX.
(blueprint: lem-pc-localized-approximation-base-change)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Localize each tensor factor, compose the localizations, then change the base ring. -/
private theorem localizedTensor_isLocalization
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] (r : Ideal B) [r.IsPrime]
    (hq : p = q.comap (algebraMap R A)) (hr : p = r.comap (algebraMap R B)) :
    let Rp := Localization.AtPrime p
    let Aq := Localization.AtPrime q
    let Br := Localization.AtPrime r
    letI := (Localization.localRingHom p q (algebraMap R A) hq).toAlgebra
    letI := (Localization.localRingHom p r (algebraMap R B) hr).toAlgebra
    ∀ θ : A ⊗[R] B →+* Aq ⊗[Rp] Br,
      (∀ (a : A) (b : B), θ (a ⊗ₜ[R] b) =
        algebraMap A Aq a ⊗ₜ[Rp] algebraMap B Br b) →
      letI := θ.toAlgebra
      ∃ M : Submonoid (A ⊗[R] B), IsLocalization M (Aq ⊗[Rp] Br) := by
  let Rp := Localization.AtPrime p
  let Aq := Localization.AtPrime q
  let Br := Localization.AtPrime r
  let := (Localization.localRingHom p q (algebraMap R A) hq).toAlgebra
  let := (Localization.localRingHom p r (algebraMap R B) hr).toAlgebra
  dsimp only
  intro θ hθ
  have : IsScalarTower R Rp Aq := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap A Aq (algebraMap R A x) =
      Localization.localRingHom p q (algebraMap R A) hq (algebraMap R Rp x)
    exact (Localization.localRingHom_to_map p q (algebraMap R A) hq x).symm
  have : IsScalarTower R Rp Br := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap B Br (algebraMap R B x) =
      Localization.localRingHom p r (algebraMap R B) hr (algebraMap R Rp x)
    exact (Localization.localRingHom_to_map p r (algebraMap R B) hr x).symm
  let T₀ := A ⊗[R] B
  let U := Aq ⊗[R] B
  let V := Aq ⊗[R] Br
  let T := Aq ⊗[Rp] Br
  let la := IsScalarTower.toAlgHom R A Aq
  let lb := IsScalarTower.toAlgHom R B Br
  let θ₁ := (Algebra.TensorProduct.map la (AlgHom.id R B)).toRingHom
  let θ₂ := (Algebra.TensorProduct.map (AlgHom.id R Aq) lb).toRingHom
  let θ₁₂ := (Algebra.TensorProduct.map la lb).toRingHom
  have h₁₂ : θ₂.comp θ₁ = θ₁₂ := by
    apply Algebra.TensorProduct.ringHom_ext <;> ext x <;> simp [θ₁, θ₂, θ₁₂]
  let c := (IsLocalization.algebraTensorEquiv p.primeCompl Rp Aq Br).symm.toRingEquiv
  have hθeq : θ = c.toRingHom.comp θ₁₂ := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext a
      change θ (a ⊗ₜ[R] 1) = c (θ₁₂ (a ⊗ₜ[R] 1))
      rw [hθ]
      simp [θ₁₂, c, la, lb, IsLocalization.algebraTensorEquiv,
        Algebra.TensorProduct.equivOfCompatibleSMul]
      rfl
    · ext b
      change θ (1 ⊗ₜ[R] b) = c (θ₁₂ (1 ⊗ₜ[R] b))
      rw [hθ]
      simp [θ₁₂, c, la, lb, IsLocalization.algebraTensorEquiv,
        Algebra.TensorProduct.equivOfCompatibleSMul]
      rfl
  have : IsScalarTower R A U := IsScalarTower.to₁₂₄ R A Aq U
  let : Algebra T₀ U := θ₁.toAlgebra
  have : IsScalarTower A T₀ U := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A Aq a ⊗ₜ[R] (1 : B) = θ₁ (a ⊗ₜ[R] (1 : B))
    simp [θ₁, la]
  let M₁ := Algebra.algebraMapSubmonoid T₀ q.primeCompl
  have h₁ : IsLocalization M₁ U :=
    IsLocalization.tensorProduct_tensorProduct R B q.primeCompl Aq (by
      ext b
      change θ₁ (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] b
      simp [θ₁])
  let := h₁
  let : Algebra U V := θ₂.toAlgebra
  have : IsScalarTower Aq U V := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change a ⊗ₜ[R] (1 : Br) = θ₂ (a ⊗ₜ[R] (1 : B))
    simp [θ₂, lb]
  let M₂ := r.primeCompl.map (Algebra.TensorProduct.includeRight (R := R) (A := Aq))
  have h₂ : IsLocalization M₂ V :=
    IsLocalization.tensorProduct_tensorProduct_right R Aq r.primeCompl Br (by
      ext b
      change θ₂ (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] algebraMap B Br b
      simp [θ₂, lb])
  let : Algebra U T := (c.toRingHom.comp θ₂).toAlgebra
  have h₂T : IsLocalization M₂ T :=
    (IsLocalization.isLocalization_iff_of_ringEquiv M₂ c).mp h₂
  let := h₂T
  let : Algebra T₀ T := θ.toAlgebra
  have : IsScalarTower T₀ U T := IsScalarTower.of_algebraMap_eq' (by
    change θ = (c.toRingHom.comp θ₂).comp θ₁
    rw [RingHom.comp_assoc, h₁₂, hθeq])
  exact ⟨IsLocalization.localizationLocalizationSubmodule M₁ M₂,
    IsLocalization.localization_localization_isLocalization M₁ M₂ T⟩


private theorem primeModuleMap_baseChange
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    [Module R N] [IsScalarTower R S N]
    (g : M →ₗ[R] N) (hg : IsBaseChange S g) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hp : p = q.comap (algebraMap R S)) :
    let f := Localization.localRingHom p q (algebraMap R S) hp
    let := f.toAlgebra
    let : Module (Localization.AtPrime p) (LocalizedModule q.primeCompl N) :=
      Module.compHom _ f
    ∃ e : Localization.AtPrime q ⊗[Localization.AtPrime p]
        LocalizedModule p.primeCompl M ≃ₗ[Localization.AtPrime q] LocalizedModule q.primeCompl N,
      ∀ b x, e (b ⊗ₜ x) = b • primeModuleMap p q (algebraMap R S) hp g.toAddMonoidHom
        (fun r x ↦ (g.map_smul r x).trans (IsScalarTower.algebraMap_smul S r (g x)).symm) x := by
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let Mp := LocalizedModule p.primeCompl M
  let Nq := LocalizedModule q.primeCompl N
  let f := Localization.localRingHom p q (algebraMap R S) hp
  let := f.toAlgebra
  let : Module Rp Nq := Module.compHom _ f
  have : IsScalarTower R S Sq := by infer_instance
  have : IsScalarTower R Rp Sq := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change (algebraMap S Sq) ((algebraMap R S) r) = f ((algebraMap R Rp) r)
    exact (Localization.localRingHom_to_map p q (algebraMap R S) hp r).symm
  have : IsScalarTower R Sq Nq := by infer_instance
  have : IsScalarTower Rp Sq Nq := ⟨fun r s x ↦ by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul _ _ _⟩
  have : IsScalarTower R S Nq := IsScalarTower.to₁₂₄ R S Sq Nq
  have : IsScalarTower R Rp Nq := IsScalarTower.to₁₂₄ R Rp Sq Nq
  let gq : Mp →ₗ[Rp] Nq :=
    { toAddHom := primeModuleMap p q (algebraMap R S) hp g.toAddMonoidHom
        (fun r x ↦ (g.map_smul r x).trans (IsScalarTower.algebraMap_smul S r (g x)).symm)
      map_smul' := fun r x ↦ primeModuleMap_smul p q (algebraMap R S) hp
        g.toAddMonoidHom
        (fun r x ↦ (g.map_smul r x).trans
          (IsScalarTower.algebraMap_smul S r (g x)).symm) r x }
  have hm : IsBaseChange Rp (LocalizedModule.mkLinearMap p.primeCompl M) :=
    IsLocalizedModule.isBaseChange p.primeCompl Rp _
  have hn : IsBaseChange Sq (LocalizedModule.mkLinearMap q.primeCompl N) :=
    IsLocalizedModule.isBaseChange q.primeCompl Sq _
  have hc := hg.comp hn
  have heq : (gq.restrictScalars R).comp (LocalizedModule.mkLinearMap p.primeCompl M) =
      ((LocalizedModule.mkLinearMap q.primeCompl N).restrictScalars R).comp g := by
    ext x
    change primeModuleMap p q (algebraMap R S) hp g.toAddMonoidHom
      (fun r x ↦ (g.map_smul r x).trans (IsScalarTower.algebraMap_smul S r (g x)).symm)
      (LocalizedModule.mk x 1) = LocalizedModule.mk (g x) 1
    rw [primeModuleMap_mk]
    congr 1
    apply Subtype.ext
    exact map_one (algebraMap R S)
  have hq : IsBaseChange Sq gq := hm.of_comp (heq ▸ hc)
  exact ⟨hq.equiv, fun b x ↦ hq.equiv_tmul b x⟩


/-- Localization of transition tensor isomorphisms gives a localization of ring
base change and an isomorphism of module base change. It uses no colimit or flatness.

Source: Stacks Project, Algebra, Tag 02JO, first paragraph; Tag 00QX.
(blueprint: lem-pc-localized-approximation-base-change)

Proof:
1. For i to j, write p_i and q_i for the contracted primes of A_i and B_i.
   The local map A_i,p_i to B_i,q_i and both transition maps are the canonical
   fraction maps. The original tensor formula shows that their square commutes.
2. Apply tensor-localization compatibility to the original isomorphism
   B_i tensor over A_i with A_j to B_j. First invert the images of the complements
   of p_i and q_i, and then those of p_j in A_j. The result identifies
   B_i,q_i tensor over A_i,p_i with A_j,p_j with the localization of B_j at the
   corresponding multiplicative set. These elements avoid q_j by naturality.
3. Further invert every element of B_j outside q_j. The composite localization
   is B_j,q_j. Its preimage multiplicative set in the preceding tensor product
   gives W, and the composite comparison gives the displayed ring homomorphism.
   The original pure-tensor formula, followed by localization, gives its formula.
4. Localize B_j tensor over B_i with D_i to D_j at the complement of q_j.
   Since each element outside q_i maps outside q_j, the localized tensor factors
   through D_i,q_i. Tensor-localization compatibility and cancellation identify
   its domain with B_j,q_j tensor over B_i,q_i with D_i,q_i. This gives the
   displayed linear equivalence, with its pure-tensor formula inherited from the
   original equivalence. This holds also for zero modules and identity transitions.
-/
theorem localized_approximation_baseChange
    {S : Type u} [CommRing S]
    {Λ : Type u} [Preorder Λ]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (D : Λ ⥤ AddCommGrpCat.{v}) [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hring : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (η.app i).hom.toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
        ∀ (x : B.obj i) (y : A.obj j),
          e (x ⊗ₜ[A.obj i] y) = (B.map f).hom x * (η.app j).hom y)
    (hmodule : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
        ∀ (y : B.obj j) (x : D.obj i),
          e (y ⊗ₜ[B.obj i] x) = y • (D.map f).hom x)
    (q : PrimeSpectrum S) :
    let Aq := primeRingDiagram A (η ≫ κ) q
    let Bq := primeRingDiagram B κ q
    let Nq := primeModuleDiagram B κ q D hs
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (primeDiagramHom A B η κ q i).toAlgebra
      letI := (Aq.map f).hom.toAlgebra
      ∃ (t : Bq.obj i ⊗[Aq.obj i] Aq.obj j →+* Bq.obj j)
        (W : Submonoid (Bq.obj i ⊗[Aq.obj i] Aq.obj j)),
        (∀ (b : Bq.obj i) (a : Aq.obj j),
          t (b ⊗ₜ[Aq.obj i] a) =
            (Bq.map f).hom b * primeDiagramHom A B η κ q j a) ∧
        (letI := t.toAlgebra; IsLocalization W (Bq.obj j))) ∧
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (Bq.map f).hom.toAlgebra
      ∃ e : Bq.obj j ⊗[Bq.obj i] Nq.obj i ≃ₗ[Bq.obj j] Nq.obj j,
        ∀ (b : Bq.obj j) (x : Nq.obj i),
          e (b ⊗ₜ[Bq.obj i] x) = b • (Nq.map f).hom x) := by
  dsimp
  constructor
  · intro i j f
    let := (η.app i).hom.toAlgebra
    let := (A.map f).hom.toAlgebra
    let p := q.asIdeal.comap ((η ≫ κ).app i).hom
    let qi := q.asIdeal.comap (κ.app i).hom
    let pj := q.asIdeal.comap ((η ≫ κ).app j).hom
    let qj := q.asIdeal.comap (κ.app j).hom
    let Rp := Localization.AtPrime p
    let Bi := Localization.AtPrime qi
    let Aj := Localization.AtPrime pj
    let Bj := Localization.AtPrime qj
    let α := primeDiagramHom A B η κ q i
    let β := ((primeRingDiagram A (η ≫ κ) q).map f).hom
    let γ := ((primeRingDiagram B κ q).map f).hom
    let δ := primeDiagramHom A B η κ q j
    let := α.toAlgebra
    let := β.toAlgebra
    let : Algebra Rp Bj := (γ.comp α).toAlgebra
    let gb : Bi →ₐ[Rp] Bj := { toRingHom := γ, commutes' := fun _ ↦ rfl }
    let ga : Aj →ₐ[Rp] Bj :=
      { toRingHom := δ
        commutes' := fun x ↦ by
          exact (RingHom.congr_fun (primeDiagramHom_naturality A B η κ q i j f) x).symm }
    let t := (Algebra.TensorProduct.productMap gb ga).toRingHom
    have ht : ∀ (b : Bi) (a : Aj), t (b ⊗ₜ[Rp] a) = γ b * δ a := fun _ _ ↦ rfl
    have : IsScalarTower (A.obj i) (B.obj i) Bi := by infer_instance
    have : IsScalarTower (A.obj i) (A.obj j) Aj := by infer_instance
    have : IsScalarTower (A.obj i) Rp Bi := IsScalarTower.of_algebraMap_eq fun x ↦ by
      change (algebraMap (B.obj i) Bi) ((η.app i).hom x) =
        α (algebraMap (A.obj i) Rp x)
      exact (Localization.localRingHom_to_map p qi (η.app i).hom rfl x).symm
    have : IsScalarTower (A.obj i) Rp Aj := IsScalarTower.of_algebraMap_eq fun x ↦ by
      change (algebraMap (A.obj j) Aj) ((A.map f).hom x) =
        β (algebraMap (A.obj i) Rp x)
      exact (Localization.localRingHom_to_map p pj (A.map f).hom
        (contractedPrime_map A (η ≫ κ) q i j f) x).symm
    let c := IsLocalization.algebraTensorEquiv p.primeCompl Rp Bi Aj
    let lb := IsScalarTower.toAlgHom (A.obj i) (B.obj i) Bi
    let la := IsScalarTower.toAlgHom (A.obj i) (A.obj j) Aj
    let θ := c.symm.toRingHom.comp (Algebra.TensorProduct.map lb la).toRingHom
    have hθ : ∀ (b : B.obj i) (a : A.obj j), θ (b ⊗ₜ[A.obj i] a) =
        algebraMap (B.obj i) Bi b ⊗ₜ[Rp] algebraMap (A.obj j) Aj a := by
      intro b a
      simp [θ, c, lb, la, IsLocalization.algebraTensorEquiv,
        Algebra.TensorProduct.equivOfCompatibleSMul]
    obtain ⟨e, he⟩ := hring i j f
    have hcomp : t.comp θ = (algebraMap (B.obj j) Bj).comp e.toRingHom := by
      apply Algebra.TensorProduct.ringHom_ext
      · ext b
        change t (θ (b ⊗ₜ[A.obj i] 1)) =
          algebraMap (B.obj j) Bj (e (b ⊗ₜ[A.obj i] 1))
        rw [hθ, ht, he]
        simp only [map_one, mul_one]
        exact Localization.localRingHom_to_map qi qj (B.map f).hom
          (contractedPrime_map B κ q i j f) b
      · ext a
        change t (θ (1 ⊗ₜ[A.obj i] a)) =
          algebraMap (B.obj j) Bj (e (1 ⊗ₜ[A.obj i] a))
        rw [hθ, ht, he]
        simp only [map_one, one_mul]
        exact Localization.localRingHom_to_map pj qj (η.app j).hom rfl a
    let := θ.toAlgebra
    obtain ⟨M, hM⟩ := localizedTensor_isLocalization p qi pj rfl
      (contractedPrime_map A (η ≫ κ) q i j f) θ hθ
    let := hM
    let : Algebra (B.obj i ⊗[A.obj i] A.obj j) Bj :=
      ((algebraMap (B.obj j) Bj).comp e.toRingHom).toAlgebra
    let := t.toAlgebra
    have : IsScalarTower (B.obj i ⊗[A.obj i] A.obj j) (Bi ⊗[Rp] Aj) Bj :=
      IsScalarTower.of_algebraMap_eq' hcomp.symm
    let N := qj.primeCompl.map e.symm
    have hN : IsLocalization N Bj :=
      IsLocalization.isLocalization_of_base_ringEquiv qj.primeCompl Bj e.symm
    let := hN
    have hMN : M ≤ N := by
      intro z hz
      have hu := (IsLocalization.map_units (Bi ⊗[Rp] Aj) ⟨z, hz⟩).map t
      have hez : IsUnit (algebraMap (B.obj j) Bj (e z)) := by
        change IsUnit (t (θ z)) at hu
        rw [← RingHom.comp_apply, hcomp] at hu
        exact hu
      have hzq := (IsLocalization.AtPrime.isUnit_to_map_iff Bj qj (e z)).mp hez
      exact ⟨e z, hzq, e.symm_apply_apply z⟩
    let W : Submonoid (Bi ⊗[Rp] Aj) := N.map θ
    refine ⟨t, W, ht, ?_⟩
    exact IsLocalization.isLocalization_of_submonoid_le (Bi ⊗[Rp] Aj) Bj M N hMN
  · intro i j f
    let := (B.map f).hom.toAlgebra
    let : Module (B.obj i) (D.obj j) := Module.compHom _ (B.map f).hom
    have : IsScalarTower (B.obj i) (B.obj j) (D.obj j) := ⟨fun r s x ↦ by
      change ((B.map f).hom r * s) • x = (B.map f).hom r • (s • x)
      exact mul_smul _ _ _⟩
    let g : D.obj i →ₗ[B.obj i] D.obj j :=
      { toAddHom := (D.map f).hom.toAddHom
        map_smul' := hs i j f }
    obtain ⟨e, he⟩ := hmodule i j f
    have hg : IsBaseChange (B.obj j) g := IsBaseChange.of_equiv e (fun x ↦ by
      change e (1 ⊗ₜ[B.obj i] x) = (D.map f).hom x
      simpa only [one_smul] using he 1 x)
    exact primeModuleMap_baseChange g hg _ _ (contractedPrime_map B κ q i j f)

end Algebra
