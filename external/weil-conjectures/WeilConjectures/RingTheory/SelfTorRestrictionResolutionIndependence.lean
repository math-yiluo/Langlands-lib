/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorRestrictionCertificate
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Independence of self-Tor restriction certificates from resolutions

Source: Stacks Project, Tag 00LS (augmentation comparison).
(blueprint: new-q1-self-tor-restriction-resolution-independence). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

private theorem restrict_cycles_lift
    (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
    (L : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ)
    (z : (((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj L).cycles n) :
    ∃ w : L.cycles n, L.iCycles n w =
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj L).iCycles n z := by
  let F := ModuleCat.restrictScalars φ
  let e := (L.sc n).mapCyclesIso F
  refine ⟨e.hom z, ?_⟩
  have he := congrArg (fun f ↦ f z) ((L.sc n).mapCyclesIso_hom_iCycles F)
  exact he

private theorem resolution_lift_cycle_class
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (P R : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : P.complex ⟶ R.complex)
    (ha : a.f 0 ≫ R.π.f 0 = P.π.f 0 ≫ 𝟙 _)
    (z : (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
      (.down ℕ)).obj P.complex).cycles n) :
    (R.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj R.complex).homologyπ n
        (HomologicalComplex.cyclesMap
          (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)).map a) n z)) =
    (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj P.complex).homologyπ n z) := by
  let T := tensorRight (ModuleCat.of A (A ⧸ I))
  let F := T.mapHomologicalComplex (.down ℕ)
  have hπ := congrArg (fun f ↦ f z) (HomologicalComplex.homologyπ_naturality
    (F.map a) n)
  have hnat := ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 _) P R a ha T n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hnat
  have hn := congrArg (fun f ↦ f ((F.obj P.complex).homologyπ n z)) hnat
  change (P.isoLeftDerivedObj T n).inv ((F.obj P.complex).homologyπ n z) =
    (R.isoLeftDerivedObj T n).inv
      (HomologicalComplex.homologyMap (F.map a) n ((F.obj P.complex).homologyπ n z))
    at hn
  simp only [ConcreteCategory.comp_apply] at hπ
  change (R.isoLeftDerivedObj T n).inv
    ((F.obj R.complex).homologyπ n (HomologicalComplex.cyclesMap (F.map a) n z)) = _
  rw [← hπ]
  exact hn.symm

/-- A tensor comparison on one pair of projective quotient resolutions certifies
its Tor map on every pair of projective quotient resolutions.
Source: Stacks Project, Tag 00LS, augmentation comparison and homotopy uniqueness.
(blueprint: new-q1-self-tor-restriction-resolution-independence).

Proof: Given another pair P', Q', lift the quotient identity to u : P' → P
and v : Q → Q'. Compose the given augmented comparison with u and restriction
of v, and compose its quotient tensor map with the tensor maps of u and v.
The quotient ring map is unchanged; the pure tensor equation follows by applying
the three pure tensor equations in order. The augmentation equation follows
from the identity augmentation equations for u and v. To check the cycle
formula, transport a P' cycle through tensor u and the given comparison, then
through tensor v. Maps of complexes carry cycles to cycles. Naturality of
homologyπ gives the homology classes of these transported cycles. Naturality
of isoLeftDerivedObj for lifts of the identity identifies their Tor classes.
The hypothesis for P,Q therefore proves the required formula for P',Q'.
Injectivity of the Q' cycles inclusion identifies the transported target cycle
with any w occurring in the certificate. No flatness of the ring map is used:
restriction of scalars is exact, and u,v are same-ring resolution comparisons.
Zero quotients and degree zero use the same equations. -/
theorem selfTor_restriction_certificate_of_resolution
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (φ : A →+* B) (n : ℕ)
    (q : (((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) →
      (((Tor' (ModuleCat.{u} B) n).obj (ModuleCat.of B (B ⧸ J))).obj
        (ModuleCat.of B (B ⧸ J))))
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (Q : ProjectiveResolution (ModuleCat.of B (B ⧸ J)))
    (ψ : (A ⧸ I) →+* (B ⧸ J))
    (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj Q.complex)
    (k : ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
        (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
          (.down ℕ)).obj Q.complex))
    (hψ : ∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x))
    (ha : ∀ x : P.complex.X 0, Q.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x))
    (hk : ∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
      k.f j (x ⊗ₜ[A] y) = (show Q.complex.X j from a.f j x) ⊗ₜ[B] (ψ y))
    (hcycles : ∀
      (z : (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj P.complex).cycles n)
      (w : (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
        (.down ℕ)).obj Q.complex).cycles n),
      (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
          (.down ℕ)).obj Q.complex).iCycles n w =
        k.f n ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
          (.down ℕ)).obj P.complex).iCycles n z) →
      (Q.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).hom
        (q ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
          ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)).obj P.complex).homologyπ n z))) =
        (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
          (.down ℕ)).obj Q.complex).homologyπ n w) :
    IsSelfTorRestrictionMap A B I J φ n q  := by
  classical
  intro P' Q'
  let F := (ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)
  let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
  let a₁ := ProjectiveResolution.lift (𝟙 _) P' P
  let a₂ := ProjectiveResolution.lift (𝟙 _) Q Q'
  let a' := a₁ ≫ a ≫ F.map a₂
  let k' := TA.map a₁ ≫ k ≫ F.map (TB.map a₂)
  refine ⟨ψ, a', k', hψ, ?_, ?_, ?_⟩
  · intro x
    change Q'.π.f 0 (a₂.f 0 (a.f 0 (a₁.f 0 x))) = ψ (P'.π.f 0 x)
    have h₁ := congrArg (fun f ↦ f x)
      (ProjectiveResolution.lift_commutes_zero (𝟙 _) P' P)
    have h₂ := congrArg (fun f ↦ f (a.f 0 (a₁.f 0 x)))
      (ProjectiveResolution.lift_commutes_zero (𝟙 _) Q Q')
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    change P.π.f 0 (a₁.f 0 x) = P'.π.f 0 x at h₁
    change Q'.π.f 0 (a₂.f 0 (a.f 0 (a₁.f 0 x))) =
      Q.π.f 0 (a.f 0 (a₁.f 0 x)) at h₂
    rw [h₂, ha, h₁]
  · intro j x y
    change (TB.map a₂).f j (k.f j ((TA.map a₁).f j (x ⊗ₜ[A] y))) = _
    change (TB.map a₂).f j (k.f j ((a₁.f j x) ⊗ₜ[A] y)) = _
    rw [hk]
    rfl
  · intro z w hw
    let z₀ := HomologicalComplex.cyclesMap (TA.map a₁) n z
    let wF := HomologicalComplex.cyclesMap k n z₀
    obtain ⟨w₀, hw₀⟩ := restrict_cycles_lift A B φ (TB.obj Q.complex) n wF
    have hz₀ := congrArg (fun f ↦ f z) (HomologicalComplex.cyclesMap_i (TA.map a₁) n)
    have hwF := congrArg (fun f ↦ f z₀) (HomologicalComplex.cyclesMap_i k n)
    simp only [ConcreteCategory.comp_apply] at hz₀ hwF
    have hc := hcycles z₀ w₀ (hw₀.trans hwF)
    have hzclass := resolution_lift_cycle_class A I n P' P a₁
      (ProjectiveResolution.lift_commutes_zero (𝟙 _) P' P) z
    rw [hzclass] at hc
    let w₁ := HomologicalComplex.cyclesMap (TB.map a₂) n w₀
    have hw₁ := congrArg (fun f ↦ f w₀)
      (HomologicalComplex.cyclesMap_i (TB.map a₂) n)
    simp only [ConcreteCategory.comp_apply] at hw₁
    have hww : w₁ = w := by
      apply (ModuleCat.mono_iff_injective ((TB.obj Q'.complex).iCycles n)).mp
        inferInstance
      rw [hw₁, hw, hw₀, hwF, hz₀]
      rfl
    have hn := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _)
      Q Q' a₂ (ProjectiveResolution.lift_commutes_zero (𝟙 _) Q Q')
      (tensorRight (ModuleCat.of B (B ⧸ J))) n
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
    have hn' := congrArg (fun f ↦ f (q
      ((P'.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
        ((TA.obj P'.complex).homologyπ n z)))) hn
    change (Q'.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).hom
      (q ((P'.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
        ((TA.obj P'.complex).homologyπ n z))) =
      HomologicalComplex.homologyMap (TB.map a₂) n
        ((Q.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).hom
          (q ((P'.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
            ((TA.obj P'.complex).homologyπ n z)))) at hn'
    have hπ := congrArg (fun f ↦ f w₀)
      (HomologicalComplex.homologyπ_naturality (TB.map a₂) n)
    simp only [ConcreteCategory.comp_apply] at hπ
    rw [hn', hc, hπ, ← hww]

end AlgebraicGeometry
