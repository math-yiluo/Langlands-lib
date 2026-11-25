/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.DvrRootTensorFactorIntegralClosureFinite

/-! # Lifting a normalized tensor factor through a finite DVR extension

Source: Stacks Project, Tags 09EM and 032L, and lying over.
(blueprint: lem-sbc-dvr-normalized-tensor-factor-lift) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

private theorem tensor_quotient_lift_surjective
    {B A A₁ E F G : Type u}
    [CommRing B] [CommRing A] [CommRing A₁] [CommRing E] [CommRing F] [CommRing G]
    [Algebra B A] [Algebra B E] [Algebra A A₁] [Algebra B A₁]
    [Algebra A F] [Algebra E F] [Algebra F G] [Algebra A G] [Algebra A₁ G]
    [Algebra E G] [IsScalarTower A F G] [IsScalarTower A A₁ G] [IsScalarTower E F G]
    (q : E ⊗[B] A →+* F) (r : F ⊗[A] A₁ →+* G) (φ : E ⊗[B] A₁ →+* G)
    (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hq_tmul : ∀ e a, q (e ⊗ₜ[B] a) = algebraMap E F e * algebraMap A F a)
    (hr_tmul : ∀ z a, r (z ⊗ₜ[A] a) = algebraMap F G z * algebraMap A₁ G a)
    (hφ_tmul : ∀ e a, φ (e ⊗ₜ[B] a) = algebraMap E G e * algebraMap A₁ G a) :
    Function.Surjective φ := by
  intro x
  obtain ⟨x, rfl⟩ := hr x
  induction x using TensorProduct.inductionOn with
  | tmul f a =>
    obtain ⟨z, rfl⟩ := hq f
    induction z using TensorProduct.inductionOn with
    | tmul e b =>
      refine ⟨e ⊗ₜ[B] (algebraMap A A₁ b * a), ?_⟩
      rw [hφ_tmul, hr_tmul, hq_tmul, map_mul, map_mul,
        ← IsScalarTower.algebraMap_apply A A₁ G,
        ← IsScalarTower.algebraMap_apply E F G,
        ← IsScalarTower.algebraMap_apply A F G, mul_assoc]
    | add z w hz hw =>
      obtain ⟨z', hz'⟩ := hz
      obtain ⟨w', hw'⟩ := hw
      refine ⟨z' + w', ?_⟩
      rw [map_add, hz', hw', map_add, TensorProduct.add_tmul, map_add]
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

private theorem tensor_factor_baseChange_embedding
    {B A A₁ E F : Type u}
    [CommRing B] [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁]
    [CommRing E] [Field F] [Algebra B A] [Algebra B E]
    [Algebra A A₁] [Algebra B A₁] [IsScalarTower B A A₁]
    [Module.Finite A A₁] [FaithfulSMul A A₁]
    [Algebra A F] [Algebra B F] [Algebra E F]
    [IsScalarTower B A F] [IsScalarTower B E F]
    (q : E ⊗[B] A →+* F) (hq : Function.Surjective q)
    (hq_tmul : ∀ e a, q (e ⊗ₜ[B] a) = algebraMap E F e * algebraMap A F a)
    (hinj : Function.Injective (algebraMap A F)) :
    ∃ (P₁ : Ideal (E ⊗[B] A₁)) (hP₁ : P₁.IsMaximal),
    letI := hP₁
    let F₁ := (E ⊗[B] A₁) ⧸ P₁
    let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
      (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
    letI := alpha₁.toAlgebra
    letI : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
    Function.Injective alpha₁ ∧ Nonempty (F →ₐ[A] F₁) := by
  classical
  -- A maximal quotient of this nonzero tensor ring extends the chosen field factor.
  let C := F ⊗[A] A₁
  let : Nontrivial C :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain A F A₁
      hinj (FaithfulSMul.algebraMap_injective A A₁)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  let := hM
  let G := C ⧸ M
  let : Field G := Ideal.Quotient.field M
  let : Algebra F G := inferInstance
  let : Algebra A G := inferInstance
  let : Algebra B G := inferInstance
  let : Algebra E G := inferInstance
  let : IsScalarTower A F G := inferInstance
  let : IsScalarTower E F G := inferInstance
  let : IsScalarTower B F G := inferInstance
  let gamma : A₁ →+* G := (Ideal.Quotient.mk M).comp
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] C).toRingHom
  let : Algebra A₁ G := gamma.toAlgebra
  let : IsScalarTower A A₁ G := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact congrArg (Ideal.Quotient.mk M)
      ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] C).commutes a).symm
  have hgamma : Function.Injective gamma := by
    apply (RingHom.injective_iff_ker_eq_bot gamma).mpr
    apply Ideal.eq_bot_of_under_eq_bot (R := A)
    rw [Ideal.under_def, RingHom.comap_ker]
    change RingHom.ker ((algebraMap A₁ G).comp (algebraMap A A₁)) = ⊥
    rw [← IsScalarTower.algebraMap_eq A A₁ G]
    rw [IsScalarTower.algebraMap_eq A F G]
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      ((algebraMap F G).injective.comp hinj)
  let : IsScalarTower B A₁ G := IsScalarTower.to₁₃₄ B A A₁ G
  let : IsScalarTower B E G := IsScalarTower.to₁₂₄ B E F G
  let phi : E ⊗[B] A₁ →ₐ[B] G := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom B E G) (IsScalarTower.toAlgHom B A₁ G)
    (fun _ _ ↦ Commute.all _ _)
  -- Each double pure tensor comes from e ⊗ (b * a), so this is a field quotient.
  have hphi : Function.Surjective phi := by
    apply tensor_quotient_lift_surjective q (Ideal.Quotient.mk M) phi.toRingHom
      hq Ideal.Quotient.mk_surjective hq_tmul
    · intro z a
      change Ideal.Quotient.mk M (z ⊗ₜ[A] a) =
        Ideal.Quotient.mk M (z ⊗ₜ[A] 1) * Ideal.Quotient.mk M (1 ⊗ₜ[A] a)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · intro e a
      exact Algebra.TensorProduct.lift_tmul
        (IsScalarTower.toAlgHom B E G) (IsScalarTower.toAlgHom B A₁ G) _ e a
  let P₁ := RingHom.ker phi
  have hP₁ : P₁.IsMaximal := RingHom.ker_isMaximal_of_surjective phi hphi
  refine ⟨P₁, hP₁, ?_⟩
  let := hP₁
  let F₁ := (E ⊗[B] A₁) ⧸ P₁
  let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
  let := alpha₁.toAlgebra
  let : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
  let : IsScalarTower A A₁ F₁ := .of_algebraMap_eq' rfl
  let e : F₁ ≃+* G := phi.toRingHom.quotientKerEquivOfSurjective hphi
  have he (a : A₁) : e (alpha₁ a) = gamma a := by
    change phi.toRingHom.quotientKerEquivOfSurjective hphi
      (Ideal.Quotient.mk (RingHom.ker phi.toRingHom) (1 ⊗ₜ[B] a)) = gamma a
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    change phi (1 ⊗ₜ[B] a) = gamma a
    simp only [phi, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
      IsScalarTower.toAlgHom_apply]
    rfl
  have halpha₁ : Function.Injective alpha₁ := by
    intro a b h
    apply hgamma
    simpa only [he] using congrArg e h
  let e₁ : F₁ ≃ₐ[A₁] G := { e with commutes' := he }
  let f : F →ₐ[A] F₁ := (e₁.restrictScalars A).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom A F G)
  exact ⟨halpha₁, ⟨f⟩⟩

-- Preserve the existing, internally unused `hQ` binder in the public statement.
set_option linter.unusedVariables false in
/-- A closed prime of a normalized tensor factor lifts after finite DVR base change.

Source: Stacks Project, Tag 09EM (remark-setup), Tag 032L and lying over.
(blueprint: lem-sbc-dvr-normalized-tensor-factor-lift)

Proof: Invert B minus zero to regard F as a finite separable field factor of
E tensor Frac(A) over Frac(B). The finite faithful extension A₁/A embeds
Frac(A) in Frac(A₁). Take the finite product of fields obtained by tensoring
F with Frac(A₁) over Frac(A). Its factors are also factors of
E tensor Frac(A₁) over Frac(B), hence quotients by maximal ideals P₁ of
E tensor A₁ over B. Their right maps alpha₁ are injective. Normalize S in
this product. Since E/Frac(B) is separable the factors are finite separable
over Frac(A₁), and 032L makes their normalizations S₁ finite over A₁.
Integrality over A, A₁ and S agrees, by transitivity and normality, so these
are exactly the factors of that product normalization. The integral map
S -> product S₁ is injective. Lying over lifts Q to a prime in one factor,
giving Q₁ and the induced A-algebra map i. Its contraction to A₁ lies over
the maximal ideal of A. Since A₁/A is finite and A₁ is local, this
contraction is the maximal ideal of A₁. The ring S is a finite normal
one-dimensional domain, hence Dedekind. The inclusion into the chosen
factor is injective, so S₁ is torsion free over S and therefore flat.
This construction uses no tameness or ramification bound. -/
theorem dvr_normalized_tensor_factor_lift
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A]
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    ∀ (P : Ideal (E ⊗[B] A)) (hP : P.IsMaximal),
    letI := hP
    let F := (E ⊗[B] A) ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
    letI := alpha.toAlgebra
    Function.Injective alpha →
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
    ∀ (A₁ : Type u) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
      [Algebra A A₁] [Algebra B A₁] [IsScalarTower B A A₁]
      [Module.Finite A A₁] [FaithfulSMul A A₁],
    ∃ (P₁ : Ideal (E ⊗[B] A₁)) (hP₁ : P₁.IsMaximal),
    letI := hP₁
    let F₁ := (E ⊗[B] A₁) ⧸ P₁
    let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
      (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
    letI := alpha₁.toAlgebra
    letI : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
    letI : IsScalarTower A A₁ F₁ := .of_algebraMap_eq' rfl
    let S₁ := integralClosure A₁ F₁
    Function.Injective alpha₁ ∧ Module.Finite A₁ S₁ ∧
    ∃ (i : S →ₐ[A] S₁) (Q₁ : Ideal S₁),
      Q₁.IsPrime ∧ Q₁.comap i.toRingHom = Q ∧
      Q₁.comap (algebraMap A₁ S₁) = IsLocalRing.maximalIdeal A₁ ∧
      letI := i.toRingHom.toAlgebra
      Module.Flat S S₁ := by
  classical
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  intro P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let : Field F := Ideal.Quotient.field P
  let : Algebra E F := inferInstance
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  intro halpha hfinite Q hQ hclosed A₁ _ _ _ _ _ _ _ _
  let := hQ
  let : Module.Finite A (integralClosure A F) := hfinite
  let : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr halpha
  let : Algebra B F := inferInstanceAs (Algebra B ((E ⊗[B] A) ⧸ P))
  let : IsScalarTower B E F := inferInstance
  let : IsScalarTower B A F := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    exact congrArg (Ideal.Quotient.mk P)
      ((Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).commutes b).symm
  obtain ⟨P₁, hP₁, halpha₁, ⟨f⟩⟩ :=
    tensor_factor_baseChange_embedding (A₁ := A₁)
      (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective (fun e a ↦ by
        change Ideal.Quotient.mk P (e ⊗ₜ[B] a) =
          Ideal.Quotient.mk P (e ⊗ₜ[B] 1) * Ideal.Quotient.mk P (1 ⊗ₜ[B] a)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]) halpha
  refine ⟨P₁, hP₁, ?_⟩
  let := hP₁
  let F₁ := (E ⊗[B] A₁) ⧸ P₁
  let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
  let := alpha₁.toAlgebra
  let : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
  let : IsScalarTower A A₁ F₁ := .of_algebraMap_eq' rfl
  have hinjBF : Function.Injective (algebraMap B F) := by
    rw [IsScalarTower.algebraMap_eq B E F]
    exact (algebraMap E F).injective.comp
      ((algebraMap (FractionRing B) E).injective.comp
        (IsFractionRing.injective B (FractionRing B)))
  have hinjBA : Function.Injective (algebraMap B A) := by
    apply Function.Injective.of_comp (f := alpha)
    change Function.Injective ((algebraMap A F).comp (algebraMap B A))
    rw [← IsScalarTower.algebraMap_eq B A F]
    exact hinjBF
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinjBA
  let : FaithfulSMul B A₁ :=
    (faithfulSMul_iff_algebraMap_injective B A₁).mpr (by
      rw [IsScalarTower.algebraMap_eq B A A₁]
      exact (FaithfulSMul.algebraMap_injective A A₁).comp hinjBA)
  let : Module.Finite B A₁ := Module.Finite.trans A A₁
  have hfinite₁ : Module.Finite A₁ (integralClosure A₁ F₁) :=
    dvr_root_tensor_factor_integralClosure_finite B A₁ E hE P₁ hP₁
  refine ⟨halpha₁, hfinite₁, ?_⟩
  let S := integralClosure A F
  let S₁ := integralClosure A₁ F₁
  let : Module.Finite A₁ S₁ := hfinite₁
  -- Restrict the field embedding to integral elements.
  let i : S →ₐ[A] S₁ :=
    { toFun := fun x ↦ ⟨f x, x.2.map f |>.tower_top (A := A₁)⟩
      map_one' := by ext; exact map_one f
      map_zero' := by ext; exact map_zero f
      map_add' := by intro x y; ext; exact map_add f (x : F) (y : F)
      map_mul' := by intro x y; ext; exact map_mul f (x : F) (y : F)
      commutes' := by intro a; ext; exact f.commutes a }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (f.injective (congrArg Subtype.val h))
  let : Algebra S S₁ := i.toRingHom.toAlgebra
  let : IsScalarTower A S S₁ := .of_algebraMap_eq' i.comp_algebraMap.symm
  let : Module.Finite A S₁ := Module.Finite.trans A₁ S₁
  let : Algebra.IsIntegral S S₁ := Algebra.IsIntegral.tower_top (R := A)
  -- Integrality over A also implies integrality over the intermediate ring S.
  obtain ⟨Q₁, hQ₁, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S₁) Q (by
      change RingHom.ker i.toRingHom ≤ Q
      rw [(RingHom.injective_iff_ker_eq_bot i.toRingHom).mp hi]
      exact bot_le)
  rw [Ideal.under_def] at hcomap
  let := hQ₁
  have hclosed₁ : Q₁.comap (algebraMap A₁ S₁) = IsLocalRing.maximalIdeal A₁ := by
    have hclosedA : Q₁.comap (algebraMap A S₁) = IsLocalRing.maximalIdeal A := by
      rw [IsScalarTower.algebraMap_eq A S S₁, ← Ideal.comap_comap, hcomap]
      exact hclosed
    have hmax : (Q₁.comap (algebraMap A₁ S₁)).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
        (Q₁.comap (algebraMap A₁ S₁)) (by
          rw [Ideal.under_def, Ideal.comap_comap,
            ← IsScalarTower.algebraMap_eq A A₁ S₁, hclosedA]
          infer_instance)
    exact IsLocalRing.eq_maximalIdeal hmax
  -- A finite integral closure of a DVR is Dedekind; its domain extensions are flat.
  have : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  have : IsIntegrallyClosed S := IsIntegrallyClosed.of_isIntegrallyClosedIn S F
  have : IsDedekindDomain S := { }
  have : Module.IsTorsionFree S S₁ :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := S) (A := S₁)).mpr hi
  exact ⟨i, Q₁, hQ₁, hcomap, hclosed₁, inferInstance⟩

end RingTheory
