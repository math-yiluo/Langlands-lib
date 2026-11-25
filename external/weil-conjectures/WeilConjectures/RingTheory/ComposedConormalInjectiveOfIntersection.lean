/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Generators
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic

/-!
# Injectivity of a composed conormal map from an ideal intersection

Source: Stacks Project, More on Algebra, Tag 07D4, proof's tensor identification
(blueprint: lem-weil-pbc-composed-conormal-injective-of-intersection).
-/

@[expose] public section

universe u v w a b

open TensorProduct

namespace Algebra.Extension

set_option backward.isDefEq.respectTransparency false in
private theorem ideal_injective {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (E : Extension A C) (J : Ideal E.Ring) (hJK : J ≤ E.ker)
    (h : J ⊓ E.ker ^ 2 = J * E.ker) :
    Function.Injective ((Cotangent.mk (P := E) ∘ₗ Submodule.inclusion hJK).liftBaseChange C) := by
  let f := Cotangent.mk (P := E) ∘ₗ Submodule.inclusion hJK
  let N := E.ker • (⊤ : Submodule E.Ring J)
  have hN : N.map J.subtype = J * E.ker := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, Ideal.smul_eq_mul, mul_comm]
  have hf : f.ker = N := by
    apply (Submodule.map_injective_of_injective (Submodule.injective_subtype J)).eq_iff.mp
    rw [hN, ← h]
    ext x
    simp only [f, Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply,
      Submodule.inclusion_apply, Cotangent.mk_eq_zero_iff, Submodule.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right, Submodule.mem_inf, exists_prop]
  let k := N.liftQ f hf.ge
  have hk : Function.Injective k := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot N f hf.ge hf.le
  let e := Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId E.Ring C) E.algebraMap_surjective
  let t := (_root_.TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl E.Ring J)).trans
    (TensorProduct.quotTensorEquivQuotSMul J E.ker)
  have H : ((f.liftBaseChange C).restrictScalars E.Ring) = k ∘ₗ t.toLinearMap := by
    ext c x
    obtain ⟨r, rfl⟩ := E.algebraMap_surjective c
    change (algebraMap E.Ring C r) • f x = k (t ((algebraMap E.Ring C r) ⊗ₜ x))
    have he : e.symm (algebraMap E.Ring C r) = Ideal.Quotient.mk E.ker r := by
      apply e.injective
      rw [e.apply_symm_apply]
      rfl
    simp only [t, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      AlgEquiv.toLinearEquiv_apply, he,
      LinearEquiv.refl_apply]
    change _ = f (r • x)
    rw [map_smul, algebraMap_smul]
  rw [← LinearMap.coe_restrictScalars E.Ring, H, LinearMap.coe_comp]
  exact hk.comp t.injective

end Algebra.Extension

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
private theorem flat_ideal_bijective {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Flat R T] (I : Ideal R) :
    Function.Bijective ((Algebra.idealMap T I).liftBaseChange T) := by
  let l := (Algebra.idealMap T I).liftBaseChange T
  constructor
  · have H : (I.map (algebraMap R T)).subtype ∘ₗ l =
        (AlgebraTensorModule.rid R T T).toLinearMap ∘ₗ I.subtype.baseChange T := by
      ext t
      simp [l, Algebra.smul_def, mul_comm]
    have hi := Module.Flat.lTensor_preserves_injective_linearMap
      (M := T) I.subtype (Submodule.injective_subtype I)
    have hh := (AlgebraTensorModule.rid R T T).injective.comp hi
    apply Function.Injective.of_comp (f := (I.map (algebraMap R T)).subtype)
    change Function.Injective ((I.map (algebraMap R T)).subtype ∘ₗ l)
    rw [H]
    exact hh
  · rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange]
    apply (Submodule.map_injective_of_injective
      (Submodule.injective_subtype (I.map (algebraMap R T)))).eq_iff.mp
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span,
      LinearMap.coe_range, ← Set.range_comp]
    change Submodule.span T (Set.range (fun x : I ↦ algebraMap R T x.val)) =
      I.map (algebraMap R T)
    rw [Ideal.map]
    congr 1
    exact (Set.image_eq_range (algebraMap R T) (I : Set R)).symm

end Algebra

namespace Algebra.Generators

set_option backward.isDefEq.respectTransparency false in
/-- The ideal-intersection identity suffices for injectivity of the conormal map.
Source: Stacks Project, More on Algebra, Tag 07D4, proof's final tensor calculation
(blueprint: lem-weil-pbc-composed-conormal-injective-of-intersection).

Proof: Write `I = P.ker`, `T = (Q.comp P).Ring`, `J = ker (Q.ofComp P)` and
`K = (Q.comp P).ker`. The coefficient map is surjective and has kernel the
extension of `I` to `T`. The inclusion of the polynomial variables of `P` makes
`T` a free `P.Ring`-algebra. Coefficientwise multiplication therefore identifies
`T ⊗[P.Ring] I` with `J`. Right exactness of tensor, followed by cancellation
of scalars through `P.Ring → B → C`, identifies `C ⊗[B] (I/I²)` with `J/JK`:
`I²T` is contained in `JK`, and passage to `C = T/K` kills precisely `JK`.
Under this identification the displayed conormal map sends the class of
`j ∈ J` to its class in `K/K²`. A class maps to zero exactly when `j ∈ K²`.
Its kernel is thus `(J ∩ K²)/JK`, which vanishes by the assumed identity.
This proves injectivity on the whole conormal module, before taking homology. -/
theorem Cotangent.toComp_injective_of_intersection
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {ι : Type a} {σ : Type b} (Q : Generators B C ι) (P : Generators A B σ)
    (h : RingHom.ker (Q.ofComp P).toAlgHom.toRingHom ⊓ (Q.comp P).ker ^ 2 =
      RingHom.ker (Q.ofComp P).toAlgHom.toRingHom * (Q.comp P).ker) :
    Function.Injective
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C) := by
  classical
  let E := (Q.comp P).toExtension
  let i := (Q.toComp P).toExtensionHom
  let : Algebra P.toExtension.Ring C :=
    Algebra.compHom C (algebraMap P.toExtension.Ring B)
  have : IsScalarTower P.toExtension.Ring B C :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra P.toExtension.Ring E.Ring := i.toAlgHom.toAlgebra
  have htower : IsScalarTower P.toExtension.Ring E.Ring C :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ by
      change (algebraMap B C) ((algebraMap P.toExtension.Ring B) x) =
        (algebraMap E.Ring C) (i.toRingHom x)
      exact i.algebraMap_toRingHom x |>.symm)
  let ePoly : E.Ring ≃ₐ[P.toExtension.Ring] MvPolynomial ι P.toExtension.Ring :=
    { MvPolynomial.sumRingEquiv A ι σ with
      commutes' := fun x ↦ by
        change MvPolynomial.sumRingEquiv A ι σ ((Q.toComp P).toAlgHom x) =
          MvPolynomial.C x
        rw [Generators.toComp_toAlgHom]
        exact DFunLike.congr_fun (MvPolynomial.sumAlgEquiv_comp_rename_inr A ι σ) x }
  have : Module.Flat P.toExtension.Ring E.Ring :=
    Module.Flat.of_linearEquiv ePoly.toLinearEquiv
  let J := P.toExtension.ker.map (algebraMap P.toExtension.Ring E.Ring)
  have hJ : J = RingHom.ker (Q.ofComp P).toAlgHom.toRingHom :=
    Generators.map_toComp_ker Q P
  have hJK : J ≤ E.ker := by
    rw [hJ]
    intro x hx
    change algebraMap E.Ring C x = 0
    have H := (Q.ofComp P).toExtensionHom.algebraMap_toRingHom x
    rw [show (Q.ofComp P).toExtensionHom.toRingHom x = 0 from hx, map_zero] at H
    simpa only [algebraMap_self, RingHom.id_apply] using H.symm
  have hinter : J ⊓ E.ker ^ 2 = J * E.ker := by
    rw [hJ]
    exact h
  let eI : E.Ring ⊗[P.toExtension.Ring] P.toExtension.ker ≃ₗ[E.Ring] J :=
    LinearEquiv.ofBijective _ (Algebra.flat_ideal_bijective P.toExtension.ker)
  let e₁ := (P.toExtension.cotangentEquiv.baseChange (A := C)).symm.trans
    (AlgebraTensorModule.cancelBaseChange P.toExtension.Ring B C C P.toExtension.ker)
  let e₂ := (AlgebraTensorModule.cancelBaseChange
    P.toExtension.Ring E.Ring C C P.toExtension.ker).symm.trans (eI.baseChange (A := C))
  let k := (Extension.Cotangent.mk (P := E) ∘ₗ Submodule.inclusion hJK).liftBaseChange C
  have hk : Function.Injective k := Extension.ideal_injective E J hJK hinter
  have H : (Extension.Cotangent.map i).liftBaseChange C =
      k ∘ₗ (e₁.trans e₂).toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using _root_.TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul c x =>
      obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
      have hx : P.toExtension.cotangentEquiv.symm (Extension.Cotangent.mk x) =
          1 ⊗ₜ[P.toExtension.Ring] x := by
        apply P.toExtension.cotangentEquiv.injective
        simp
      change c • Extension.Cotangent.mk ⟨i.toAlgHom x.val, _⟩ =
        k (e₂ (e₁ (c ⊗ₜ[B] Extension.Cotangent.mk x)))
      simp only [e₁, e₂, LinearEquiv.trans_apply, LinearEquiv.baseChange_symm_tmul,
        LinearEquiv.baseChange_tmul, hx, AlgebraTensorModule.cancelBaseChange_tmul,
        one_smul, AlgebraTensorModule.cancelBaseChange_symm_tmul]
      change _ = c • Extension.Cotangent.mk
        (Submodule.inclusion hJK ((Algebra.idealMap E.Ring P.toExtension.ker).liftBaseChange
          E.Ring (1 ⊗ₜ[P.toExtension.Ring] x)))
      rw [LinearMap.liftBaseChange_one_tmul]
      rfl
  rw [H, LinearMap.coe_comp]
  exact hk.comp (e₁.trans e₂).injective

end Algebra.Generators
