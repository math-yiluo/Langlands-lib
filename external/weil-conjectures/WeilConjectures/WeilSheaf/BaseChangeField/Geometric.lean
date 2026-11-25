/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Geometric fibers under a finite extension of the base field

Let `k₀ ⊆ k₀'` be finite fields, `#k₀' = q ^ r`, and let `Y'` be the base change to `k₀'` of a
`k₀`-scheme `Y`, encoded by a cartesian square `g : Y' ⟶ Y` over `Spec k₀' ⟶ Spec k₀`. A
`k₀`-isomorphism `τ : k̄' ≅ k̄` of the algebraic closures
(`AlgebraicGeometry.algebraicClosureAlgEquiv`) identifies the geometric fibers,
`θ : Y ×_{k₀} k̄ ≅ Y' ×_{k₀'} k̄'` (`AlgebraicGeometry.Scheme.Hom.geometricFiberBaseChangeIso`),
and under this identification the geometric Galois Frobenius of `Y'` relative to `k₀'` is the
`r`-th power of that of `Y` relative to `k₀`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius`):
the geometric Frobenius of `k̄'` over `k₀'` is the inverse of `x ↦ x ^ (q ^ r)`, which `τ`
carries to the inverse of `y ↦ y ^ (q ^ r)`, the `r`-th power of the geometric Frobenius of `k̄`
over `k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀] (k₀' : Type u) [Field k₀'] [Algebra k₀ k₀']

/-- A `k₀`-isomorphism `k̄' ≅ k̄` between the algebraic closure of an algebraic extension `k₀'` of
`k₀` and that of `k₀`: both are algebraic closures of `k₀`. -/
def algebraicClosureAlgEquiv [Algebra.IsAlgebraic k₀ k₀'] :
    AlgebraicClosure k₀' ≃ₐ[k₀] AlgebraicClosure k₀ :=
  haveI : Algebra.IsAlgebraic k₀ (AlgebraicClosure k₀') :=
    Algebra.IsAlgebraic.trans k₀ k₀' (AlgebraicClosure k₀')
  haveI : IsAlgClosure k₀ (AlgebraicClosure k₀') := ⟨inferInstance, inferInstance⟩
  IsAlgClosure.equiv k₀ _ _

variable {k₀ k₀'}

/-- `Spec` of a composite of ring homomorphisms given pointwise. -/
lemma spec_map_comp_spec_map_eq {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (a : R →+* S) (b : S →+* T) (c : R →+* T) (h : ∀ x, b (a x) = c x) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom c) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact h x

omit [Algebra k₀ k₀'] in
/-- A ring isomorphism between algebraic closures of finite fields with `#k₀ ^ r` and `#k₀'`
elements intertwines the geometric Frobenius of `k̄'` over `k₀'` with the `r`-th power of that of
`k̄` over `k₀`: both are the inverse of `x ↦ x ^ #k₀'`. -/
lemma algEquiv_geometricFrobenius_apply [Fintype k₀] [Fintype k₀'] (r : ℕ)
    (hr : Fintype.card k₀' = Fintype.card k₀ ^ r)
    (τ : AlgebraicClosure k₀' ≃+* AlgebraicClosure k₀) (x : AlgebraicClosure k₀') :
    τ (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀' (AlgebraicClosure k₀') x) =
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀) ^ r) (τ x) := by
  let σ' := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀' (AlgebraicClosure k₀')
  let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)
  have key (y : AlgebraicClosure k₀) : (σ ^ r)⁻¹ y = y ^ Fintype.card k₀' := by
    rw [show σ = _ from FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv _ _, inv_pow,
      inv_inv,
      AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hr]
  have key' (y : AlgebraicClosure k₀') : σ'⁻¹ y = y ^ Fintype.card k₀' := by
    rw [show σ' = _ from FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv _ _, inv_inv]
    rfl
  apply (σ ^ r)⁻¹.injective
  rw [key, ← map_pow, ← key', AlgEquiv.aut_inv, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]

namespace Scheme.Hom

variable [Algebra.IsAlgebraic k₀ k₀'] {Y Y' : Scheme.{u}} {f : Y ⟶ Spec (.of k₀)}
  {f' : Y' ⟶ Spec (.of k₀')} {g : Y' ⟶ Y}
  (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))))

/-- The `k₀`-embedding `k₀' ⟶ k̄' ≅ k̄`. -/
abbrev algebraicClosureEmbedding : k₀' →+* AlgebraicClosure k₀ :=
  (algebraicClosureAlgEquiv k₀ k₀').toRingHom.comp (algebraMap k₀' (AlgebraicClosure k₀'))

lemma algebraicClosureEmbedding_algebraMap (x : k₀) :
    algebraicClosureEmbedding (k₀ := k₀) (k₀' := k₀') (algebraMap k₀ k₀' x) =
      algebraMap k₀ (AlgebraicClosure k₀) x := by
  simp [← IsScalarTower.algebraMap_apply]

include hg in
/-- The point `Y ×_{k₀} k̄ ⟶ Y'` of the base change through `k₀' ⟶ k̄' ≅ k̄`. -/
def geometricFiberToBaseChange : f.geometricFiber ⟶ Y' :=
  hg.lift f.geometricFiberProj (f.geometricFiberToAlgebraicClosure ≫
    Spec.map (CommRingCat.ofHom algebraicClosureEmbedding)) (by
    rw [geometricFiber_condition, Category.assoc]
    exact congrArg (_ ≫ ·) (spec_map_comp_spec_map_eq _ _ _
      algebraicClosureEmbedding_algebraMap).symm)

@[reassoc (attr := simp)]
lemma geometricFiberToBaseChange_comp_fst : geometricFiberToBaseChange hg ≫ g =
    f.geometricFiberProj :=
  hg.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma geometricFiberToBaseChange_comp_snd : geometricFiberToBaseChange hg ≫ f' =
    f.geometricFiberToAlgebraicClosure ≫ Spec.map (CommRingCat.ofHom algebraicClosureEmbedding) :=
  hg.lift_snd _ _ _

/-- The comparison `Y ×_{k₀} k̄ ⟶ Y' ×_{k₀'} k̄'` of geometric fibers, through `τ : k̄' ≅ k̄`. -/
def geometricFiberBaseChangeHom : f.geometricFiber ⟶ f'.geometricFiber :=
  pullback.lift (geometricFiberToBaseChange hg) (f.geometricFiberToAlgebraicClosure ≫
    Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₀').toRingHom)) (by
    rw [geometricFiberToBaseChange_comp_snd, Category.assoc]
    exact congrArg (_ ≫ ·) (spec_map_comp_spec_map_eq _ _ _ fun _ ↦ rfl).symm)

/-- The inverse comparison `Y' ×_{k₀'} k̄' ⟶ Y ×_{k₀} k̄`. -/
def geometricFiberBaseChangeInv : f'.geometricFiber ⟶ f.geometricFiber :=
  pullback.lift (f'.geometricFiberProj ≫ g) (f'.geometricFiberToAlgebraicClosure ≫
    Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₀').symm.toRingHom)) (by
    rw [Category.assoc, hg.w, geometricFiber_condition_assoc, Category.assoc]
    refine congrArg (_ ≫ ·) ((spec_map_comp_spec_map_eq _ _ (algebraMap k₀ _) fun x ↦ ?_).trans
      (spec_map_comp_spec_map_eq _ _ _ fun x ↦ ?_).symm)
    · exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
    · simp)

@[reassoc (attr := simp)]
lemma geometricFiberBaseChangeHom_comp_geometricFiberProj :
    geometricFiberBaseChangeHom hg ≫ f'.geometricFiberProj = geometricFiberToBaseChange hg :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma geometricFiberBaseChangeHom_comp_geometricFiberToAlgebraicClosure :
    geometricFiberBaseChangeHom hg ≫ f'.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₀').toRingHom) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma geometricFiberBaseChangeInv_comp_geometricFiberProj :
    geometricFiberBaseChangeInv hg ≫ f.geometricFiberProj = f'.geometricFiberProj ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma geometricFiberBaseChangeInv_comp_geometricFiberToAlgebraicClosure :
    geometricFiberBaseChangeInv hg ≫ f.geometricFiberToAlgebraicClosure =
      f'.geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₀').symm.toRingHom) :=
  pullback.lift_snd _ _ _

/-- The identification `θ : Y ×_{k₀} k̄ ≅ Y' ×_{k₀'} k̄'` of the geometric fibers of a
`k₀`-scheme `Y` and of its base change `Y'` to `k₀'`, through `τ : k̄' ≅ k̄`. -/
def geometricFiberBaseChangeIso : f.geometricFiber ≅ f'.geometricFiber where
  hom := geometricFiberBaseChangeHom hg
  inv := geometricFiberBaseChangeInv hg
  hom_inv_id := by
    ext
    · simp
    · rw [Category.assoc, geometricFiberBaseChangeInv_comp_geometricFiberToAlgebraicClosure,
        geometricFiberBaseChangeHom_comp_geometricFiberToAlgebraicClosure_assoc,
        spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp), Category.id_comp,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  inv_hom_id := by
    ext
    · refine hg.hom_ext ?_ ?_
      · simp
      · rw [Category.assoc, Category.assoc,
          geometricFiberBaseChangeHom_comp_geometricFiberProj_assoc,
          geometricFiberToBaseChange_comp_snd,
          geometricFiberBaseChangeInv_comp_geometricFiberToAlgebraicClosure_assoc,
          spec_map_comp_spec_map_eq _ _ (algebraMap k₀' (AlgebraicClosure k₀')) (fun x ↦ by simp),
          Category.id_comp,
          geometricFiber_condition]
        rfl
    · rw [Category.assoc, geometricFiberBaseChangeHom_comp_geometricFiberToAlgebraicClosure,
        geometricFiberBaseChangeInv_comp_geometricFiberToAlgebraicClosure_assoc,
        spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp), Category.id_comp,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

section Frobenius

variable [Finite k₀] [Finite k₀']

omit [Algebra.IsAlgebraic k₀ k₀'] in
/-- The geometric Frobenius of `k̄'` over `k₀'` corresponds under `τ : k̄' ≅ k̄` to the `r`-th
power of that of `k̄` over `k₀`, as automorphisms of spectra: `Spec τ ≫ σ' = σʳ ≫ Spec τ`. -/
lemma spec_algebraicClosureAlgEquiv_comp_specGeometricFrobenius [Algebra.IsAlgebraic k₀ k₀']
    (r : ℕ) (hr : Nat.card k₀' = Nat.card k₀ ^ r) :
    Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₀').toRingHom) ≫
        (specGeometricFrobenius k₀').asIso.hom =
      (specGeometricFrobenius k₀ ^ r).asIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₀').toRingHom) := by
  let := Fintype.ofFinite k₀
  let := Fintype.ofFinite k₀'
  rw [specGeometricFrobenius_hom, specGeometricFrobenius_pow_hom, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext x
  exact algEquiv_geometricFrobenius_apply r
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hr])
    (algebraicClosureAlgEquiv k₀ k₀').toRingEquiv x

include hg in
/-- The point `Y ×_{k₀} k̄ ⟶ Y'` is invariant under the `r`-th power of the geometric Galois
Frobenius, `k₀'` having `#k₀ ^ r` elements. -/
lemma geometricGaloisFrobenius_pow_hom_comp_geometricFiberToBaseChange (r : ℕ)
    (hr : Nat.card k₀' = Nat.card k₀ ^ r) :
    (f.geometricGaloisFrobenius ^ r).asIso.hom ≫ geometricFiberToBaseChange hg =
      geometricFiberToBaseChange hg := by
  refine hg.hom_ext ?_ ?_
  · simp
  · simp only [Category.assoc, geometricFiberToBaseChange_comp_snd,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure_assoc]
    rw [specGeometricFrobenius_pow_hom_comp_spec_map_of_card_eq k₀ r hr]

include hg in
/-- Under the identification `θ : Y ×_{k₀} k̄ ≅ Y' ×_{k₀'} k̄'`, the geometric Galois Frobenius of
`Y'` relative to `k₀'` is the `r`-th power of that of `Y` relative to `k₀`:
`θ ≫ Fr' = Frʳ ≫ θ`. -/
lemma geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius (r : ℕ)
    (hr : Nat.card k₀' = Nat.card k₀ ^ r) :
    (geometricFiberBaseChangeIso hg).hom ≫ f'.geometricGaloisFrobenius.asIso.hom =
      (f.geometricGaloisFrobenius ^ r).asIso.hom ≫ (geometricFiberBaseChangeIso hg).hom := by
  ext
  · simp [geometricFiberBaseChangeIso,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberToBaseChange hg r hr]
  · simp only [geometricFiberBaseChangeIso, Category.assoc,
      geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure,
      geometricFiberBaseChangeHom_comp_geometricFiberToAlgebraicClosure_assoc,
      geometricFiberBaseChangeHom_comp_geometricFiberToAlgebraicClosure,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure_assoc]
    rw [spec_algebraicClosureAlgEquiv_comp_specGeometricFrobenius r hr]

end Frobenius

section Map

variable {B B' : Scheme.{u}} {fB : B ⟶ Spec (.of k₀)} {fB' : B' ⟶ Spec (.of k₀')}
  {gB : B' ⟶ B} (hgB : IsPullback gB fB' fB (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))))
  {φ : Y ⟶ B} (hφ : φ ≫ fB = f) {φ' : Y' ⟶ B'} (hφ' : φ' ≫ fB' = f') (hgφ : φ' ≫ gB = g ≫ φ)

include hgφ in
/-- The identifications of the geometric fibers of `Y` and `B` with those of their base changes
are compatible with the base change `φ̄` of a morphism `φ : Y ⟶ B` and that of its base change
`φ' : Y' ⟶ B'`. -/
lemma geometricFiberBaseChangeIso_hom_comp_geometricFiberMap :
    (geometricFiberBaseChangeIso hg).hom ≫ geometricFiberMap φ' hφ' =
      geometricFiberMap φ hφ ≫ (geometricFiberBaseChangeIso hgB).hom := by
  ext
  · simp only [geometricFiberBaseChangeIso, Category.assoc,
      geometricFiberMap_comp_geometricFiberProj,
      geometricFiberBaseChangeHom_comp_geometricFiberProj_assoc,
      geometricFiberBaseChangeHom_comp_geometricFiberProj]
    refine hgB.hom_ext ?_ ?_
    · simp [hgφ]
    · simp [hφ']
  · simp [geometricFiberBaseChangeIso]

end Map

end Scheme.Hom

end AlgebraicGeometry
