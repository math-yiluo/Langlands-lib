/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Descending an essentially smooth local factorization to a quotient

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, quotient steps.
-/

@[expose] public section

universe u v w
open scoped TensorProduct

namespace Algebra

private theorem essentiallySmooth_baseChange
    {R : Type u} {D : Type (max u v)} {P : Type u}
    [CommRing R] [CommRing D] [CommRing P] [Algebra R D] [Algebra R P]
    (hD : EssentiallySmooth R D) : EssentiallySmooth P (P ⊗[R] D) := by
  classical
  rcases hD with ⟨S, hS, hRS, hsmooth, U, ⟨e⟩⟩
  let : CommRing S := hS
  let : Algebra R S := hRS
  let : Algebra S D := (e.symm.toRingHom.comp (algebraMap S (Localization U))).toAlgebra
  have : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap R D x = e.symm (algebraMap S (Localization U) (algebraMap R S x))
    rw [← IsScalarTower.algebraMap_apply R S (Localization U), e.symm.commutes]
  have : IsLocalization U D :=
    (IsLocalization.isLocalization_iff_of_ringEquiv U e.symm.toRingEquiv).mp inferInstance
  let V : Submonoid (P ⊗[R] S) := U.map (TensorProduct.includeRight (R := R) (A := P)).toMonoidHom
  have : IsLocalization (U.map (TensorProduct.includeRight (R := R) (A := P)))
      (Localization V) := by
    change IsLocalization V (Localization V)
    infer_instance
  let e' : (P ⊗[R] D) ≃ₐ[P] Localization V :=
    IsLocalization.tensorProductEquivOfMapIncludeRight R P U D (Localization V)
  exact ⟨P ⊗[R] S, inferInstance, inferInstance, inferInstance, V, ⟨e'⟩⟩

/-- Base change an auxiliary local factorization to the localization of a larger quotient.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, items
item-sixth-resolve and item-eighth-resolve; the tensor and quotient universal properties.
(blueprint: lem-weil-pbc-essentially-smooth-localized-quotient-factorization).

Proof: Write Q=R_(q∩R), L=T_q, P=(R/J)_(q₀∩(R/J)), and L₀=(T/JT)_q₀.
The equality lifting q₀ gives local ring maps ρ:Q→P and τ:L→L₀. Their formulas on
localized base elements show that I⊆JQ is killed by ρ and K⊆JL is killed by τ.
They also show that Q→L→L₀ equals Q→P→L₀, by localization extensionality.
Thus ρ factors through Q/I, and the composite D→L/K→L₀ is a Q/I-algebra map.
Set E=P⊗_(Q/I)D. The tensor universal property gives G:E→L₀. The composite
C→Q⊗_R C→D→E maps each base element x to its image under R→R/J→P→E, so
it kills JC. Descend it to C/JC and apply tensor universality to obtain
F:P⊗_(R/J)(C/JC)→E. On pure tensors, GF is the desired map by the given
equality gf and the quotient compatibility equation for γ₀. Tensor induction and
quotient surjectivity extend this equality to every element.
For essential smoothness, present D as a localization of a smooth Q/I-algebra S.
Transport the S-algebra structure and localization instance to D along that presentation.
The smooth algebra P⊗_(Q/I)S has a localization isomorphic over P to E, by
IsLocalization.tensorProductEquivOfMapIncludeRight. This gives the required presentation
of E. Since Q/I and P live in Type u and D in Type(max u v), both E and its smooth
localization model live in Type(max u v). All witnesses are explicit constructions;
no choice from an unproved existence theorem is used. -/
theorem essentiallySmooth_localized_quotient_factorization
    {R : Type u} {C : Type v} {T : Type w}
    [CommRing R] [CommRing C] [CommRing T] [Algebra R C] [Algebra R T]
    (γ : C →ₐ[R] T) (q : PrimeSpectrum T) (J : Ideal R)
    (γ₀ : (C ⧸ J.map (algebraMap R C)) →ₐ[R ⧸ J]
      (T ⧸ J.map (algebraMap R T)))
    (q₀ : PrimeSpectrum (T ⧸ J.map (algebraMap R T)))
    (hγ : γ₀.toRingHom.comp (Ideal.Quotient.mk (J.map (algebraMap R C))) =
      (Ideal.Quotient.mk (J.map (algebraMap R T))).comp γ.toRingHom)
    (hq : PrimeSpectrum.comap (Ideal.Quotient.mk (J.map (algebraMap R T))) q₀ = q)
    (hfactor :
      let Q := Localization.AtPrime (q.asIdeal.under R)
      let L := Localization.AtPrime q.asIdeal
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      let JQ := J.map (algebraMap R Q)
      let JL := (J.map (algebraMap R T)).map (algebraMap T L)
      ∃ (I : Ideal Q) (K : Ideal L),
        I ≤ JQ ∧ K ≤ JL ∧ I.map (algebraMap Q L) ≤ K ∧
        ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra Q D)
          (_ : Algebra (Q ⧸ I) D) (_ : IsScalarTower Q (Q ⧸ I) D),
          EssentiallySmooth (Q ⧸ I) D ∧
          ∃ (f : Q ⊗[R] C →ₐ[Q] D) (g : D →ₐ[Q] L ⧸ K),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId Q (L ⧸ K))
              ((Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R T L).comp γ))
              (fun _ _ ↦ Commute.all _ _)) :
    let R₀ := R ⧸ J
    let C₀ := C ⧸ J.map (algebraMap R C)
    let T₀ := T ⧸ J.map (algebraMap R T)
    let P := Localization.AtPrime (q₀.asIdeal.under R₀)
    let L₀ := Localization.AtPrime q₀.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q₀.asIdeal.under R₀) q₀.asIdeal
    ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
      EssentiallySmooth P E ∧
      ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L₀),
        g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L₀)
          ((IsScalarTower.toAlgHom R₀ T₀ L₀).comp γ₀)
          (fun _ _ ↦ Commute.all _ _) := by
  classical
  let Q := Localization.AtPrime (q.asIdeal.under R)
  let L := Localization.AtPrime q.asIdeal
  let R₀ := R ⧸ J
  let C₀ := C ⧸ J.map (algebraMap R C)
  let T₀ := T ⧸ J.map (algebraMap R T)
  let P := Localization.AtPrime (q₀.asIdeal.under R₀)
  let L₀ := Localization.AtPrime q₀.asIdeal
  let : Algebra Q L :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  let : Algebra P L₀ :=
    Localization.AtPrime.algebraOfLiesOver (q₀.asIdeal.under R₀) q₀.asIdeal
  obtain ⟨I, K, hI, hK, hIK, D, hD, hQD, hID, hTower, hSmooth, f, g, hfg⟩ := hfactor
  let : CommRing D := hD
  let : Algebra Q D := hQD
  let : Algebra (Q ⧸ I) D := hID
  have : IsScalarTower Q (Q ⧸ I) D := hTower
  have hbase : q.asIdeal.under R =
      (q₀.asIdeal.under R₀).comap (Ideal.Quotient.mk J) := by
    ext x
    rw [← hq]
    rfl
  let ρ : Q →+* P := Localization.localRingHom (q.asIdeal.under R)
    (q₀.asIdeal.under R₀) (Ideal.Quotient.mk J) hbase
  let τ : L →+* L₀ := Localization.localRingHom q.asIdeal q₀.asIdeal
    (Ideal.Quotient.mk (J.map (algebraMap R T))) (congrArg PrimeSpectrum.asIdeal hq).symm
  let : Algebra Q P := ρ.toAlgebra
  have : IsScalarTower R Q P := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap R₀ P (Ideal.Quotient.mk J x) = ρ (algebraMap R Q x)
    exact (Localization.localRingHom_to_map _ _ _ _ x).symm
  have hρ : I ≤ RingHom.ker ρ := by
    apply hI.trans
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change ρ (algebraMap R Q x) = 0
    dsimp only [ρ]
    rw [Localization.localRingHom_to_map]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hτ : K ≤ RingHom.ker τ := by
    apply hK.trans
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change τ (algebraMap T L x) = 0
    dsimp only [τ]
    rw [Localization.localRingHom_to_map]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let : Algebra Q L₀ := ((algebraMap P L₀).comp ρ).toAlgebra
  have : IsScalarTower Q P L₀ := IsScalarTower.of_algebraMap_eq' rfl
  have hτQ : τ.comp (algebraMap Q L) = algebraMap Q L₀ := by
    apply IsLocalization.ringHom_ext (q.asIdeal.under R).primeCompl
    ext x
    change τ (algebraMap Q L (algebraMap R Q x)) =
      algebraMap P L₀ (ρ (algebraMap R Q x))
    rw [← IsScalarTower.algebraMap_apply R Q L]
    rw [IsScalarTower.algebraMap_apply R T L]
    dsimp only [τ, ρ]
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
    rw [← IsScalarTower.algebraMap_apply R₀ P L₀]
    rw [IsScalarTower.algebraMap_apply R₀ T₀ L₀]
    rfl
  let ρI : (Q ⧸ I) →+* P := Ideal.Quotient.lift I ρ hρ
  let : Algebra (Q ⧸ I) P := ρI.toAlgebra
  have : IsScalarTower Q (Q ⧸ I) P := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (Q ⧸ I) L₀ := ((algebraMap P L₀).comp ρI).toAlgebra
  have : IsScalarTower (Q ⧸ I) P L₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Q (Q ⧸ I) L₀ := IsScalarTower.of_algebraMap_eq' rfl
  let τK : (L ⧸ K) →+* L₀ := Ideal.Quotient.lift K τ hτ
  let gD : D →ₐ[Q ⧸ I] L₀ :=
    { τK.comp g.toRingHom with
      commutes' := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change τK (g (algebraMap (Q ⧸ I) D (Ideal.Quotient.mk I x))) =
          algebraMap P L₀ (ρI (Ideal.Quotient.mk I x))
        change τK (g (algebraMap (Q ⧸ I) D (algebraMap Q (Q ⧸ I) x))) = _
        rw [← IsScalarTower.algebraMap_apply Q (Q ⧸ I) D, g.commutes]
        change τ (algebraMap Q L x) = algebraMap P L₀ (ρ x)
        exact RingHom.congr_fun hτQ x }
  let E := P ⊗[Q ⧸ I] D
  have hE : EssentiallySmooth P E := essentiallySmooth_baseChange hSmooth
  let gE : E →ₐ[P] L₀ := TensorProduct.lift (Algebra.ofId P L₀) gD
    (fun _ _ ↦ Commute.all _ _)
  have : IsScalarTower Q P E := inferInstance
  have : IsScalarTower Q (Q ⧸ I) E := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (Q ⧸ I) P E]
    rfl
  let dE : D →ₐ[Q] E :=
    (TensorProduct.includeRight (R := Q ⧸ I) (A := P)).restrictScalars Q
  let cE : C →+* E := dE.toRingHom.comp
    (f.toRingHom.comp (TensorProduct.includeRight (R := R) (A := Q)).toRingHom)
  have hcE (x : R) : cE (algebraMap R C x) =
      algebraMap P E (algebraMap R₀ P (Ideal.Quotient.mk J x)) := by
    change dE (f (TensorProduct.includeRight (algebraMap R C x))) = _
    rw [TensorProduct.includeRight.commutes]
    rw [IsScalarTower.algebraMap_apply R Q (Q ⊗[R] C), f.commutes, dE.commutes]
    change algebraMap P E (ρ (algebraMap R Q x)) = _
    dsimp only [ρ]
    rw [Localization.localRingHom_to_map]
  have hcKill : J.map (algebraMap R C) ≤ RingHom.ker cE := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change cE (algebraMap R C x) = 0
    rw [hcE, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero]
  have : IsScalarTower R₀ P E := inferInstance
  let c₀ : C₀ →ₐ[R₀] E :=
    { Ideal.Quotient.lift _ cE hcKill with
      commutes' := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact hcE x }
  let fE : (P ⊗[R₀] C₀) →ₐ[P] E :=
    TensorProduct.lift (Algebra.ofId P E) c₀ (fun _ _ ↦ Commute.all _ _)
  refine ⟨E, inferInstance, inferInstance, hE, fE, gE, ?_⟩
  apply AlgHom.ext
  intro z
  induction z using _root_.TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hc := AlgHom.congr_fun hfg (1 ⊗ₜ[R] c)
    simp only [AlgHom.comp_apply, TensorProduct.lift_tmul, map_one, one_mul] at hc
    change gE (fE (a ⊗ₜ[R₀] Ideal.Quotient.mk _ c)) = _
    have hfE : fE (a ⊗ₜ[R₀] Ideal.Quotient.mk _ c) =
        algebraMap P E a * dE (f (1 ⊗ₜ[R] c)) := rfl
    rw [hfE, map_mul, gE.commutes]
    have hgE : gE (dE (f (1 ⊗ₜ[R] c))) = τK (g (f (1 ⊗ₜ[R] c))) := by
      change algebraMap P L₀ 1 * τK (g (f (1 ⊗ₜ[R] c))) = _
      rw [map_one, one_mul]
    rw [hgE]
    rw [hc]
    change algebraMap P L₀ a * τ (algebraMap T L (γ c)) = _
    dsimp only [τ]
    rw [Localization.localRingHom_to_map]
    have hγc := RingHom.congr_fun hγ c
    change γ₀ (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (γ c) at hγc
    rw [← hγc]
    rfl

end Algebra
