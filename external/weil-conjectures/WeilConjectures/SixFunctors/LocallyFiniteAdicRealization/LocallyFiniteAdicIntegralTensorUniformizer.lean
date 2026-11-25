/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Module.NatInt

/-! # Inverting the integral uniformizer in native tensor extension

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
private instance homSMul (M N : ProEtale.AdicSheaf l X) :
    SMul (ULift.{u + 1} (PadicAlgCl l)) (M ⟶ N) :=
  ⟨fun c f ↦ ProEtale.AdicSheaf.smul c M ≫ f⟩
private theorem hom_smul {M N : ProEtale.AdicSheaf l X}
    (c : ULift.{u + 1} (PadicAlgCl l)) (f : M ⟶ N) :
    (c • f).hom = c • f.hom := by
  change (ProEtale.AdicSheaf.smul c M ≫ f).hom = _
  simp
private instance homModule (M N : ProEtale.AdicSheaf l X) :
    Module (ULift.{u + 1} (PadicAlgCl l)) (M ⟶ N) :=
  Function.Injective.module (ULift.{u + 1} (PadicAlgCl l))
    { toFun := fun f ↦ f.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ h ↦ Mod.hom_ext _ _ h) (hom_smul l X)
private instance adicLinear :
    Linear (ULift.{u + 1} (PadicAlgCl l)) (ProEtale.AdicSheaf l X) where
  smul_comp _ _ _ c f g := Mod.hom_ext _ _ (by simp [hom_smul])
  comp_smul _ _ _ f c g := Mod.hom_ext _ _ (by simp [hom_smul])

private theorem uniformizer_divides_l (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Padic.coefficientExtensionUniformizer l E ∣ (l : Padic.coefficientExtensionIntegers l E) := by
  let H := Padic.coefficientExtensionIntegers_dvr l E
  let O := Padic.coefficientExtensionIntegers l E
  let m := H.choose
  have HS := H.choose_spec
  rcases HS with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr,
    hpid, hm0, hprime, hfinite, hr, hgen, hassoc, hexists⟩
  have hl : (l : O) ∈ m := by
    apply (hm _).mpr
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l,
      spectralNorm_extends (K := ℚ_[l]) (L := E), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  change hgen.choose ∣ (l : O)
  exact Ideal.mem_span_singleton.mp (hgen.choose_spec.symm ▸ hl)

private theorem scalar_factor_isIso {R : Type*} [CommRing R] {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] [Linear R A]
    (F : A ⥤ B) [F.Additive] (K : A) (t b : R)
    (h : IsIso (F.map ((t * b) • 𝟙 K))) : IsIso (F.map (t • 𝟙 K)) := by
  let f : End (F.obj K) := .of (F.map (t • 𝟙 K))
  let g : End (F.obj K) := .of (F.map (b • 𝟙 K))
  have hc : Commute f g := by
    apply End.ext
    change F.map (b • 𝟙 K) ≫ F.map (t • 𝟙 K) =
      F.map (t • 𝟙 K) ≫ F.map (b • 𝟙 K)
    simp only [← F.map_comp, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, smul_smul, mul_comm]
  have hi : IsUnit (f * g) := by
    apply (CategoryTheory.isUnit_iff_isIso _).mpr
    simpa only [f, g, End.mul_asHom, ← F.map_comp, Linear.smul_comp,
      Linear.comp_smul, Category.id_comp, smul_smul, mul_comm] using h
  exact (CategoryTheory.isUnit_iff_isIso _).mp ((hc.isUnit_mul_iff).mp hi).1

variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

private theorem native_nsmul_isIso
    (Z : DerivedCategory (pbcModules X (ringSheaf l X))) : IsIso (l • 𝟙 Z) := by
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  haveI : (sections l X).IsEquivalence := by unfold sections; infer_instance
  let e : DerivedCategory (ProEtale.AdicSheaf l X) ≌
      DerivedCategory (pbcModules X (ringSheaf l X)) :=
    (sections l X).mapDerivedCategory.asEquivalence
  haveI : e.functor.Additive :=
    inferInstanceAs ((sections l X).mapDerivedCategory.Additive)
  haveI : e.inverse.Additive := Equivalence.inverse_additive e
  haveI : e.inverse.Full := Equivalence.full_inverse e
  haveI : e.inverse.Faithful := Equivalence.faithful_inverse e
  let R := ULift.{u + 1} (PadicAlgCl l)
  have h0 : (l : R) ≠ 0 := by
    intro he
    have he' : (l : PadicAlgCl l) = 0 := congrArg ULift.down he
    have he'' : (l : ℚ_[l]) = 0 :=
      (algebraMap ℚ_[l] (PadicAlgCl l)).injective (by simpa only [map_natCast, map_zero] using he')
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) he''

  haveI : IsIso ((l : R) • 𝟙 (e.inverse.obj Z)) := by
    refine ⟨⟨(l : R)⁻¹ • 𝟙 _, ?_, ?_⟩⟩ <;>
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        smul_smul, mul_inv_cancel₀ h0, inv_mul_cancel₀ h0, one_smul]
  haveI : IsIso (e.inverse.map (l • 𝟙 Z)) := by
    rw [e.inverse.map_nsmul, e.inverse.map_id, ← Nat.cast_smul_eq_nsmul R]
    infer_instance
  letI : e.inverse.ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_full_and_faithful e.inverse
  exact isIso_of_reflects_iso _ e.inverse

/-- Native tensor extension inverts the constant integral uniformizer.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-sf-native-integral-tensor-uniformizer).

Proof: the uniformizer generates the maximal ideal of the coefficient DVR, and
ℓ belongs to that ideal since its spectral norm is less than one. Hence the
uniformizer divides ℓ. Native adic sheaves and their derived category are linear
over the algebraic closure of the ℓ-adic field, so multiplication by ℓ is invertible.
The derived section equivalence transports this to the target of integral tensor
extension. Additivity identifies the image of multiplication by the natural number
ℓ with this invertible scalar endomorphism. The two scalar factors commute; a factor
of an invertible product of commuting endomorphisms is invertible.
-/
theorem integralTensor_uniformizer_isIso (C : CoefficientSystem l X)
    (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    IsIso ((integralTensor l X C E).map
      (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E) • 𝟙 K)) := by
  let A := Coefficient.{u} l (PadicAlgCl l) E
  let R := Padic.coefficientExtensionIntegers l A
  let F := integralTensor l X C E
  let t := Padic.coefficientExtensionUniformizer l A
  obtain ⟨b, hb⟩ := uniformizer_divides_l l A
  have he : F.map ((t * b) • 𝟙 K) = l • 𝟙 (F.obj K) := by
    rw [← hb, Nat.cast_smul_eq_nsmul, F.map_nsmul, F.map_id]
  have hi : IsIso (F.map ((t * b) • 𝟙 K)) := by
    rw [he]
    exact native_nsmul_isIso l X _
  exact scalar_factor_isIso F K t b hi

end WeilConjectures.LocallyFiniteAdicRealization
