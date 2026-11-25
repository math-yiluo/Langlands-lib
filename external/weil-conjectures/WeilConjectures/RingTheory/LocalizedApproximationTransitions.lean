/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.BaseChange

/-! # Base changes of localized approximation transitions

Source: Stacks Project, Algebra, Tag 00RC, first reduction paragraph, and Tag 00QX.
(blueprint: lem-weil-pbc-localized-approximation-transitions)
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace Algebra

/-- Localization of transition ring and module base changes at compatible primes.

Source: Stacks Project, Algebra, Tag 00RC, first reduction paragraph, and Tag 00QX.
(blueprint: lem-weil-pbc-localized-approximation-transitions)

Proof:
1. Fix i ≤ j. The supplied pure-tensor ring isomorphism identifies B_j with
   B_i tensor over A_i A_j. Localizing the two tensor factors at q_i and its
   contraction to A_j gives B_i localized at q_i tensor over localized A_i
   localized A_j. The commuting localization squares identify its map to localized
   B_j with the product map on pure tensors. All denominators already inverted
   avoid q_j, by compatibility of the primes. Inverting the complement of the
   inverse image of the maximal ideal of localized B_j gives exactly localized B_j:
   the original tensor isomorphism and the localization universal properties give
   inverse fraction maps. This supplies W and the IsLocalization witness.
2. Localize the supplied module base-change equivalence. Tensor-localization
   compatibility first localizes the earlier module and then extends scalars to
   localized B_j. Both the resulting module and D^l_j are localizations of
   B_j tensor over B_i D_i at q_j. The IsLocalizedModule witnesses give their
   unique linear equivalence. On a tensor with denominator-one module numerator,
   the original pure-tensor formula and the compatibility of ζ with the transition
   give b tensor ζ_i(x) mapped to b ζ_j(D(f)(x)). Clear denominators in x to extend
   this to every localized x; this yields the stated pure-tensor formula.
These arguments are pointwise in the transition and do not use colimits or finiteness. -/
theorem localized_approximation_transition_base_change
    {Λ : Type u} [Preorder Λ]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
    (D : Λ ⥤ AddCommGrpCat.{u}) [∀ i, Module (B.obj i) (D.obj i)]
    (q : ∀ i, Ideal (B.obj i)) [∀ i, (q i).IsPrime]
    (hq : ∀ (i j : Λ) (f : i ⟶ j), Ideal.comap (B.map f).hom (q j) = q i)
    (Aₗ Bₗ : Λ ⥤ CommRingCat.{u}) (Dₗ : Λ ⥤ AddCommGrpCat.{u})
    [∀ i, Module (Bₗ.obj i) (Dₗ.obj i)]
    (φ : ∀ i, Aₗ.obj i →+* Bₗ.obj i)
    (ρA : ∀ i, A.obj i →+* Aₗ.obj i) (ρB : ∀ i, B.obj i →+* Bₗ.obj i)
    (ζ : ∀ i, D.obj i →+ Dₗ.obj i)
    (hρA : ∀ i, letI := (ρA i).toAlgebra
      IsLocalization ((q i).comap (η.app i).hom).primeCompl (Aₗ.obj i))
    (hρB : ∀ i, letI := (ρB i).toAlgebra
      IsLocalization (q i).primeCompl (Bₗ.obj i))
    (hη : ∀ i, (ρB i).comp (η.app i).hom = (φ i).comp (ρA i))
    (hA : ∀ (i j : Λ) (f : i ⟶ j),
      (ρA j).comp (A.map f).hom = (Aₗ.map f).hom.comp (ρA i))
    (hB : ∀ (i j : Λ) (f : i ⟶ j),
      (ρB j).comp (B.map f).hom = (Bₗ.map f).hom.comp (ρB i))
    (hζ : ∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i),
      ζ j ((D.map f).hom x) = (Dₗ.map f).hom (ζ i x))
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : Bₗ.obj i) (x : Dₗ.obj i),
      (Dₗ.map f).hom (b • x) = (Bₗ.map f).hom b • (Dₗ.map f).hom x)
    (hℓ : ∀ i, letI := Module.compHom (Dₗ.obj i) (ρB i)
      ∃ ℓ : D.obj i →ₗ[B.obj i] Dₗ.obj i,
        (∀ x, ℓ x = ζ i x) ∧ IsLocalizedModule (q i).primeCompl ℓ)
    (htB : ∀ (i j : Λ) (h : i ≤ j),
      letI := (η.app i).hom.toAlgebra
      letI := (A.map (homOfLE h)).hom.toAlgebra
      ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
        ∀ (x : B.obj i) (y : A.obj j),
          e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y)
    (htD : ∀ (i j : Λ) (h : i ≤ j),
      letI := (B.map (homOfLE h)).hom.toAlgebra
      ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
        ∀ (y : B.obj j) (x : D.obj i),
          e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) :
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (Aₗ.map f).hom.toAlgebra
      ∃ (t : Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j →+* Bₗ.obj j)
        (W : Submonoid (Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j)),
        (∀ (b : Bₗ.obj i) (a : Aₗ.obj j),
          t (b ⊗ₜ[Aₗ.obj i] a) = (Bₗ.map f).hom b * φ j a) ∧
        (letI := t.toAlgebra; IsLocalization W (Bₗ.obj j))) ∧
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (Bₗ.map f).hom.toAlgebra
      ∃ e : Bₗ.obj j ⊗[Bₗ.obj i] Dₗ.obj i ≃ₗ[Bₗ.obj j] Dₗ.obj j,
        ∀ (b : Bₗ.obj j) (x : Dₗ.obj i),
          e (b ⊗ₜ[Bₗ.obj i] x) = b • (Dₗ.map f).hom x) := by
  -- below only needs the supplied commuting localization squares.
  have _ := hq
  constructor
  · intro i j f
    let := (ρA i).toAlgebra
    let := hρA i
    have hφ : (Bₗ.map f).hom.comp (φ i) = (φ j).comp (Aₗ.map f).hom := by
      apply IsLocalization.ringHom_ext
        ((q i).comap (η.app i).hom).primeCompl
      calc
        ((Bₗ.map f).hom.comp (φ i)).comp (ρA i) =
            (Bₗ.map f).hom.comp ((ρB i).comp (η.app i).hom) := by
          rw [RingHom.comp_assoc, ← hη i]
        _ = (ρB j).comp ((B.map f).hom.comp (η.app i).hom) := by
          rw [← RingHom.comp_assoc, ← hB, RingHom.comp_assoc]
        _ = (ρB j).comp ((η.app j).hom.comp (A.map f).hom) := by
          congr 1
          exact congrArg CommRingCat.Hom.hom (η.naturality f).symm
        _ = ((φ j).comp (Aₗ.map f).hom).comp (ρA i) := by
          rw [← RingHom.comp_assoc, hη, RingHom.comp_assoc, hA,
            ← RingHom.comp_assoc]
    let := (φ i).toAlgebra
    let := (Aₗ.map f).hom.toAlgebra
    let := ((φ j).comp (Aₗ.map f).hom).toAlgebra
    let β : Bₗ.obj i →ₐ[Aₗ.obj i] Bₗ.obj j :=
      { (Bₗ.map f).hom with commutes' := fun a ↦ RingHom.congr_fun hφ a }
    let γ : Aₗ.obj j →ₐ[Aₗ.obj i] Bₗ.obj j :=
      { φ j with commutes' := fun _ ↦ rfl }
    let t := (Algebra.TensorProduct.lift β γ (fun _ _ ↦ .all _ _)).toRingHom
    have ht (b : Bₗ.obj i) (a : Aₗ.obj j) :
        t (b ⊗ₜ[Aₗ.obj i] a) = (Bₗ.map f).hom b * φ j a := rfl
    let := (η.app i).hom.toAlgebra
    let := (A.map f).hom.toAlgebra
    obtain ⟨e, he⟩ := htB i j (leOfHom f)
    have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
    have he' (b : B.obj i) (a : A.obj j) :
        e (b ⊗ₜ[A.obj i] a) = (B.map f).hom b * (η.app j).hom a := by
      simpa only [hf] using he b a
    let k := Algebra.TensorProduct.mapRingHom (ρA i) (ρB i) (ρA j) (hη i) (hA i j f)
    let u := k.comp e.symm.toRingHom
    have htu : t.comp u = ρB j := by
      apply (RingHom.cancel_right (f := e.toRingHom) e.surjective).mp
      apply RingHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
      | tmul b a =>
        change t (k (e.symm (e (b ⊗ₜ[A.obj i] a)))) = ρB j (e (b ⊗ₜ[A.obj i] a))
        rw [e.symm_apply_apply, Algebra.TensorProduct.mapRingHom_tmul, ht, he', map_mul]
        congr 1
        · exact (RingHom.congr_fun (hB i j f) b).symm
        · exact (RingHom.congr_fun (hη j) a).symm
    let W := (IsUnit.submonoid (Bₗ.obj j)).comap t
    let L := Localization W
    let ψ := (algebraMap _ L).comp u
    let := (ρB j).toAlgebra
    let := hρB j
    have hψ (c : (q j).primeCompl) : IsUnit (ψ c) := by
      apply IsLocalization.map_units L
        (⟨u c, show u c ∈ W from ?_⟩ : W)
      change IsUnit (t (u c))
      rw [← RingHom.comp_apply, htu]
      exact IsLocalization.map_units (Bₗ.obj j) c
    let ψl : Bₗ.obj j →+* L := IsLocalization.lift hψ
    have hψl (c : B.obj j) : ψl (ρB j c) = ψ c := IsLocalization.lift_eq hψ c
    have huB (b : B.obj i) : u ((B.map f).hom b) =
        ρB i b ⊗ₜ[Aₗ.obj i] (1 : Aₗ.obj j) := by
      have hb : (B.map f).hom b = e (b ⊗ₜ[A.obj i] (1 : A.obj j)) := by
        rw [he', map_one, mul_one]
      rw [hb]
      change k (e.symm (e _)) = _
      rw [e.symm_apply_apply, Algebra.TensorProduct.mapRingHom_tmul, map_one]
    have huA (a : A.obj j) : u ((η.app j).hom a) =
        (1 : Bₗ.obj i) ⊗ₜ[Aₗ.obj i] ρA j a := by
      have ha : (η.app j).hom a = e ((1 : B.obj i) ⊗ₜ[A.obj i] a) := by
        rw [he', map_one, one_mul]
      rw [ha]
      change k (e.symm (e _)) = _
      rw [e.symm_apply_apply, Algebra.TensorProduct.mapRingHom_tmul, map_one]
    have hψlt : ψl.comp t = algebraMap _ L := by
      apply Algebra.TensorProduct.ringHom_ext
      · let := (ρB i).toAlgebra
        let := hρB i
        apply IsLocalization.ringHom_ext (q i).primeCompl
        ext b
        change ψl (t (ρB i b ⊗ₜ[Aₗ.obj i] (1 : Aₗ.obj j))) =
          algebraMap _ L (ρB i b ⊗ₜ[Aₗ.obj i] (1 : Aₗ.obj j))
        have hb := RingHom.congr_fun (hB i j f) b
        change ρB j ((B.map f).hom b) = (Bₗ.map f).hom (ρB i b) at hb
        rw [ht, map_one, mul_one, ← hb, hψl]
        change algebraMap _ L (u ((B.map f).hom b)) = _
        rw [huB]
      · let := (ρA j).toAlgebra
        let := hρA j
        apply IsLocalization.ringHom_ext ((q j).comap (η.app j).hom).primeCompl
        ext a
        change ψl (t ((1 : Bₗ.obj i) ⊗ₜ[Aₗ.obj i] ρA j a)) =
          algebraMap _ L ((1 : Bₗ.obj i) ⊗ₜ[Aₗ.obj i] ρA j a)
        have ha := RingHom.congr_fun (hη j) a
        change ρB j ((η.app j).hom a) = φ j (ρA j a) at ha
        rw [ht, map_one, one_mul, ← ha, hψl]
        change algebraMap _ L (u ((η.app j).hom a)) = _
        rw [huA]
    have hv (w : W) : IsUnit (t w) := w.property
    let v : L →+* Bₗ.obj j := IsLocalization.lift hv
    have hvl (x : Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j) :
        v (algebraMap _ L x) = t x := IsLocalization.lift_eq hv x
    have hvψ : v.comp ψl = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (q j).primeCompl
      ext c
      change v (ψl (ρB j c)) = ρB j c
      rw [hψl]
      change v (algebraMap _ L (u c)) = _
      rw [hvl]
      exact RingHom.congr_fun htu c
    have hψv : ψl.comp v = RingHom.id _ := by
      apply IsLocalization.ringHom_ext W
      apply RingHom.ext
      intro x
      change ψl (v (algebraMap _ L x)) = algebraMap _ L x
      rw [hvl]
      exact RingHom.congr_fun hψlt x
    let := t.toAlgebra
    let E : L ≃ₐ[Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j] Bₗ.obj j :=
      { v with
        invFun := ψl
        left_inv := fun x ↦ RingHom.congr_fun hψv x
        right_inv := fun x ↦ RingHom.congr_fun hvψ x
        commutes' := hvl }
    exact ⟨t, W, ht, IsLocalization.isLocalization_of_algEquiv W E⟩
  · intro i j f
    let := (B.map f).hom.toAlgebra
    let := (ρB i).toAlgebra
    let := (ρB j).toAlgebra
    let := (Bₗ.map f).hom.toAlgebra
    let := ((Bₗ.map f).hom.comp (ρB i)).toAlgebra
    have htower : IsScalarTower (B.obj i) (B.obj j) (Bₗ.obj j) := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (hB i j f).symm
    let := htower
    let : IsScalarTower (B.obj i) (Bₗ.obj i) (Bₗ.obj j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Module (B.obj i) (D.obj j) := Module.compHom _ (B.map f).hom
    let : IsScalarTower (B.obj i) (B.obj j) (D.obj j) :=
      IsScalarTower.of_compHom _ _ _
    let : Module (B.obj i) (Dₗ.obj i) := Module.compHom _ (ρB i)
    let : IsScalarTower (B.obj i) (Bₗ.obj i) (Dₗ.obj i) :=
      IsScalarTower.of_compHom _ _ _
    let : Module (B.obj j) (Dₗ.obj j) := Module.compHom _ (ρB j)
    let : IsScalarTower (B.obj j) (Bₗ.obj j) (Dₗ.obj j) :=
      IsScalarTower.of_compHom _ _ _
    let : Module (Bₗ.obj i) (Dₗ.obj j) := Module.compHom _ (Bₗ.map f).hom
    let : IsScalarTower (Bₗ.obj i) (Bₗ.obj j) (Dₗ.obj j) :=
      IsScalarTower.of_compHom _ _ _
    let : Module (B.obj i) (Dₗ.obj j) :=
      Module.compHom _ ((Bₗ.map f).hom.comp (ρB i))
    let : IsScalarTower (B.obj i) (Bₗ.obj j) (Dₗ.obj j) :=
      IsScalarTower.of_compHom _ _ _
    let : IsScalarTower (B.obj i) (B.obj j) (Dₗ.obj j) :=
      IsScalarTower.to₁₂₄ _ _ (Bₗ.obj j) _
    let : IsScalarTower (B.obj i) (Bₗ.obj i) (Dₗ.obj j) :=
      IsScalarTower.to₁₂₄ _ _ (Bₗ.obj j) _
    obtain ⟨ℓi, hℓi, hloc_i⟩ := hℓ i
    obtain ⟨ℓj, hℓj, hloc_j⟩ := hℓ j
    let := hloc_i
    let := hloc_j
    let := hρB i
    let := hρB j
    obtain ⟨e, he⟩ := htD i j (leOfHom f)
    have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
    let d : D.obj i →ₗ[B.obj i] D.obj j :=
      e.toLinearMap.restrictScalars (B.obj i) ∘ₗ TensorProduct.mk _ _ _ 1
    have hd (x : D.obj i) : d x = (D.map f).hom x := by
      simp only [d, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, TensorProduct.mk_apply, he, hf, one_smul]
    have hbase : IsBaseChange (B.obj j) d := by
      apply IsBaseChange.of_equiv e
      intro x
      rfl
    let dl : Dₗ.obj i →ₗ[Bₗ.obj i] Dₗ.obj j :=
      { toAddHom := (Dₗ.map f).hom
        map_smul' := fun b x ↦ hscalar i j f b x }
    have hi : IsBaseChange (Bₗ.obj i) ℓi :=
      IsLocalizedModule.isBaseChange (q i).primeCompl (Bₗ.obj i) ℓi
    have hj : IsBaseChange (Bₗ.obj j) ℓj :=
      IsLocalizedModule.isBaseChange (q j).primeCompl (Bₗ.obj j) ℓj
    have hcomm : (dl.restrictScalars (B.obj i)).comp ℓi =
        (ℓj.restrictScalars (B.obj i)).comp d := by
      ext x
      change (Dₗ.map f).hom (ℓi x) = ℓj (d x)
      rw [hℓi, hℓj, hd]
      exact (hζ i j f x).symm
    have hl : IsBaseChange (Bₗ.obj j) dl := by
      apply IsBaseChange.of_comp hi
      rw [hcomm]
      exact hbase.comp hj
    exact ⟨hl.equiv, fun b x ↦ hl.equiv_tmul b x⟩

end Algebra
