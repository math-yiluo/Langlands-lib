/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.FieldTheory.MakeSeparable
import WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent

/-!
# Perfect-closure criterion for geometric normality

Source: Stacks Project, Algebra, Tag 037Z (lemma-geometrically-normal), (4) iff (1),
and Tag 046W (lemma-perfection)
(blueprint: lem-weil-pbc-geometrically-normal-perfect-closure-criterion).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Algebra

private theorem normal_of_equiv {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap e.toRingHom
  have : p.IsPrime := Ideal.comap_isPrime e.toRingHom q
  obtain ⟨hd, hi⟩ := hR p
  have : IsDomain (Localization.AtPrime p) := hd
  have : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e' := Localization.localRingEquiv p q e rfl
  exact ⟨e'.symm.injective.isDomain e'.symm, IsIntegrallyClosed.of_equiv e'⟩

private theorem normal_tensor_descent
    (k : Type*) (A : Type*) (K : Type*) (L : Type*)
    [Field k] [CommRing A] [Algebra k A] [Field K] [Algebra k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (hL : ∀ (p : Ideal (L ⊗[k] A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (K ⊗[k] A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  apply normal_ring_of_normal_tensor_field K L (K ⊗[k] A)
  let e := (TensorProduct.comm K (K ⊗[k] A) L).toRingEquiv.trans
    (TensorProduct.cancelBaseChange k K L L A).toRingEquiv
  exact normal_of_equiv e.symm hL

private theorem normal_localization
    (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap (algebraMap R S)
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap R S) q
  obtain ⟨hd, hi⟩ := hR p
  have : IsDomain (Localization.AtPrime p) := hd
  have : IsIntegrallyClosed (Localization.AtPrime p) := hi
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Localization.AtPrime q)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_tensor_separable_fg
    (k : Type*) (A : Type*) (K : Type*)
    [Field k] [CommRing A] [Algebra k A] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) (hsep : IsSeparableExtension k K)
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (A ⊗[k] K)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨B, hB, hfrac⟩ := FieldTheory.exists_smooth_subalgebra_fraction_field hfg hsep
  have : Smooth k B := hB
  have : IsFractionRing B K := hfrac
  have hnormal := RingHom.Smooth.isNormalRing
    (RingHom.smooth_algebraMap.mpr (inferInstance : Smooth A (A ⊗[k] B))) hA
  have hC := normal_of_equiv (TensorProduct.comm k A B).toRingEquiv hnormal
  have : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[k] A)
      (nonZeroDivisors B)) ((B ⊗[k] A) ⊗[B] K) :=
    IsLocalization.tensor K (nonZeroDivisors B)
  have hloc := normal_localization (B ⊗[k] A) ((B ⊗[k] A) ⊗[B] K)
    (Algebra.algebraMapSubmonoid (B ⊗[k] A) (nonZeroDivisors B)) hC
  let e := (TensorProduct.comm B (B ⊗[k] A) K).toRingEquiv.trans
    ((TensorProduct.cancelBaseChange k B K K A).toRingEquiv.trans
      (TensorProduct.comm k K A).toRingEquiv)
  exact normal_of_equiv e hloc

private theorem normal_tensor_fg_of_perfect
    (k : Type*) (A : Type*) (P : Type*)
    [Field k] [CommRing A] [Algebra k A] [Field P] [Algebra k P] [PerfectField P]
    (hP : ∀ (p : Ideal (P ⊗[k] A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (K : Type*) [Field K] [Algebra k K] (hfg : (⊤ : IntermediateField k K).FG) :
    ∀ (q : Ideal (K ⊗[k] A)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  obtain ⟨k', K', hk', hK', akk', akK', ak'K', aKK', ht1, ht2,
    hfin1, hpi1, hfin2, hpi2, hsep⟩ :=
    exists_finite_purelyInseparable_separable_extension k K hfg
  let : Field k' := hk'
  let : Field K' := hK'
  let : Algebra k k' := akk'
  let : Algebra k K' := akK'
  let : Algebra k' K' := ak'K'
  let : Algebra K K' := aKK'
  have : IsScalarTower k k' K' := ht1
  have : IsScalarTower k K K' := ht2
  have : Module.Finite k k' := hfin1
  have : IsPurelyInseparable k k' := hpi1
  have : Module.Finite K K' := hfin2
  have : IsPurelyInseparable K K' := hpi2
  let f : k' →ₐ[k] P := Classical.choice inferInstance
  let : Algebra k' P := f.toRingHom.toAlgebra
  have : IsScalarTower k k' P := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hk'A := normal_tensor_descent k A k' P hP
  have : EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  have : EssFiniteType k K' := EssFiniteType.comp k K K'
  have : EssFiniteType k' K' := EssFiniteType.of_comp k k' K'
  have hfg' := IntermediateField.fg_top k' K'
  have hsm := normal_tensor_separable_fg k' (k' ⊗[k] A) K' hfg' hsep hk'A
  let e := (TensorProduct.comm k' (k' ⊗[k] A) K').toRingEquiv.trans
    (TensorProduct.cancelBaseChange k k' K' K' A).toRingEquiv
  exact normal_tensor_descent k A K K' (normal_of_equiv e hsm)

open CategoryTheory CategoryTheory.Limits in
private theorem normal_tensor_of_fg
    (k : Type u) (A : Type v) (E : Type (max u v w))
    [Field k] [CommRing A] [Algebra k A] [Field E] [Algebra k E]
    (hfg : ∀ (K : Type (max u v w)) [Field K] [Algebra k K],
      (⊤ : IntermediateField k K).FG →
      ∀ (p : Ideal (K ⊗[k] A)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (E ⊗[k] A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  let K (s : Finset E) := IntermediateField.adjoin k (s : Set E)
  let inc {s t : Finset E} (h : s ≤ t) : K s →ₐ[k] K t :=
    IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _ (Finset.coe_subset.mpr h))
  let F : Finset E ⥤ CommRingCat.{max u v w} :=
    { obj s := .of (K s ⊗[k] A)
      map f := CommRingCat.ofHom (TensorProduct.map (inc (leOfHom f)) (.id k A)).toRingHom
      map_id s := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        induction x using _root_.TensorProduct.inductionOn with
        | tmul a b => rfl
        | add x y hx hy => simp_all
      map_comp f g := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        induction x using _root_.TensorProduct.inductionOn with
        | tmul a b => rfl
        | add x y hx hy => simp_all }
  let c : Cocone F :=
    { pt := .of (E ⊗[k] A)
      ι :=
        { app s := CommRingCat.ofHom (TensorProduct.map (K s).val (.id k A)).toRingHom
          naturality s t f := by
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro x
            induction x using _root_.TensorProduct.inductionOn with
            | tmul a b => rfl
            | add x y hx hy => simp_all } }
  have hsurj (x : E ⊗[k] A) : ∃ s y, (c.ι.app s).hom y = x := by
    induction x using _root_.TensorProduct.inductionOn with
    | tmul a b =>
      refine ⟨{a}, (⟨a, IntermediateField.subset_adjoin k _ (by simp)⟩ : K {a}) ⊗ₜ b, ?_⟩
      rfl
    | add x y hx hy =>
      obtain ⟨s, x', hx'⟩ := hx
      obtain ⟨t, y', hy'⟩ := hy
      refine ⟨s ∪ t, (F.map (homOfLE Finset.subset_union_left)).hom x' +
        (F.map (homOfLE Finset.subset_union_right)).hom y', ?_⟩
      rw [map_add]
      have h₁ := ConcreteCategory.congr_hom
        (c.w (homOfLE (show s ≤ s ∪ t from Finset.subset_union_left))) x'
      have h₂ := ConcreteCategory.congr_hom
        (c.w (homOfLE (show t ≤ s ∪ t from Finset.subset_union_right))) y'
      exact congrArg₂ (· + ·) (h₁.trans hx') (h₂.trans hy')
  have hinj (s : Finset E) : Function.Injective (c.ι.app s).hom := by
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := A)
      (K s).val.toLinearMap (K s).val.injective
  have hc : IsColimit c := by
    let U := forget CommRingCat.{max u v w}
    have ht : IsColimit (U.mapCocone c) := by
      apply Types.FilteredColimit.isColimitOf'
      · intro x
        obtain ⟨s, y, hy⟩ := hsurj x
        exact ⟨s, y, hy.symm⟩
      · intro s x y hxy
        exact ⟨s, 𝟙 s, congrArg (F.map (𝟙 s)).hom (hinj s hxy)⟩
    let : ReflectsColimit F U := reflectsColimit_of_reflectsIsomorphisms F U
    exact isColimitOfReflects U ht
  have hnormal := CommRingCat.isNormal_of_filtered_colimit F (fun s ↦ by
    have : EssFiniteType k (K s) :=
      IntermediateField.essFiniteType_iff.mpr ⟨s, rfl⟩
    exact hfg (K s) (IntermediateField.fg_top k (K s)))
  let e := ((colimit.isColimit F).coconePointUniqueUpToIso hc).commRingCatIsoToRingEquiv
  exact normal_of_equiv e hnormal

/-- Normality after extension to a perfect closure is equivalent to normality after every
field extension, with no finiteness or nonzero assumption on the algebra.

Source: Stacks Project, Algebra, Tag 037Z (lemma-geometrically-normal), (4) iff (1),
and Tag 046W (lemma-perfection).
(blueprint: lem-weil-pbc-geometrically-normal-perfect-closure-criterion).

Proof:
1. The reverse implication specializes to the perfect closure. In characteristic zero the
   power condition identifies P with k; in positive characteristic Frobenius on P is bijective.
2. Each finite purely inseparable extension k₁/k embeds in P by sending an element to its unique
   iterated Frobenius root. Uniqueness makes this a field homomorphism. Tensor associativity
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) and normality descent
   (lem-weil-pbc-normal-ring-field-extension-descent) give normality of k₁ ⊗[k] A.
3. For a finitely generated K/k, lem-weil-pbc-make-separable supplies k₁ and K₁ with finite
   purely inseparable horizontal extensions and K₁/k₁ separable. It is still finitely generated,
   so lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra gives a smooth
   k₁-subalgebra B with fraction field K₁.
4. Smooth base change (lem-weil-pbc-smooth-ring-map-base-change-composition) and smooth ascent
   (lem-weil-pbc-smooth-over-normal-ring-normal) make (k₁ ⊗[k] A) ⊗[k₁] B normal.
5. Localize B at its nonzero elements. By lem-weil-pbc-localization-base-change this localizes
   the tensor algebra; its prime localizations agree with those before localization and are
   normal domains. Tensor associativity identifies the resulting ring with K₁ ⊗[k] A.
6. Tensor associativity and normality descent along K₁/K give normality of K ⊗[k] A.
7. Every extension E/k is the directed union of its finitely generated intermediate fields.
   Tensoring commutes with this colimit by the tensor pushout universal property: compatible
   maps glue on each element in a common finitely generated subfield.
8. Apply lem-weil-pbc-filtered-colimit-normal-ring. For A = 0 all prime-localization conditions
   are vacuous. Universe lifts allow specialization to fields in smaller universes. -/
theorem normal_tensor_perfectClosure_iff
    (k : Type u) (A : Type v) (P : Type w)
    [Field k] [CommRing A] [Algebra k A] [Field P] [Algebra k P] [PerfectField P]
    (hpower : ∀ x : P, ∃ n : ℕ, ∃ a : k, algebraMap k P a = x ^ (ringExpChar k ^ n)) :
    (∀ (p : Ideal (P ⊗[k] A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
    ∀ (E : Type (max u v w t)) [Field E] [Algebra k E],
      ∀ (p : Ideal (E ⊗[k] A)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  have _hpower := hpower
  constructor
  · intro hP E _ _
    exact normal_tensor_of_fg.{u, v, max w t} k A E (fun K _ _ hfg ↦
      normal_tensor_fg_of_perfect k A P hP K hfg)
  · intro h
    let e : ULift.{max u v w t} P ≃ₐ[k] P := ULift.algEquiv
    have hP := h (ULift.{max u v w t} P)
    exact normal_of_equiv
      (TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv hP

end Algebra
