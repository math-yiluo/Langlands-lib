/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Expand
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# The power map `t ↦ t^m` of the trait

For `m ≥ 1`, the substitution `t ↦ t^m` is a finite ring map `k'⟦t⟧ ⟶ k'⟦t⟧`
(`PowerSeries.expand`): every power series is `∑_{r < m} t^r g_r(t^m)`
(`PowerSeries.eq_sum_X_pow_mul_expand`). On the trait `S = Spec k'⟦t⟧` it is a morphism
`σ : S ⟶ S` over `Spec k` (`AlgebraicGeometry.traitPowMap`). The induced map of fraction fields
makes `Frac k'⟦t⟧` algebraic over its image, so it extends to an automorphism of the algebraic
closure `Ω` (`AlgebraicGeometry.traitGenericFieldPowEquiv`), compatible with `σ` through the
geometric generic point (`AlgebraicGeometry.traitGenericPoint_traitPowMap`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] (m : ℕ) (hm : m ≠ 0)

/-- The map `Frac k'⟦t⟧ ⟶ Frac k'⟦t⟧` induced by `t ↦ t^m`. -/
noncomputable def traitFractionPowMap :
    FractionRing (PowerSeries k') →+* FractionRing (PowerSeries k') :=
  IsFractionRing.lift (A := PowerSeries k')
    (g := (algebraMap (PowerSeries k') (FractionRing (PowerSeries k'))).comp
      (PowerSeries.expand m hm).toRingHom)
    ((IsFractionRing.injective (PowerSeries k') (FractionRing (PowerSeries k'))).comp
      (PowerSeries.expand_injective m hm))

lemma traitFractionPowMap_algebraMap (f : PowerSeries k') :
    traitFractionPowMap k' m hm (algebraMap _ _ f) = algebraMap _ _ (PowerSeries.expand m hm f) :=
  IsFractionRing.lift_algebraMap _ _

/-- The algebraic closure `Ω` of `Frac k'⟦t⟧`, as an algebra over `Frac k'⟦t⟧` through
`t ↦ t^m`. -/
def TraitGenericFieldPow (m : ℕ) (_hm : m ≠ 0) : Type u :=
  traitGenericField k'

namespace TraitGenericFieldPow

noncomputable instance : Field (TraitGenericFieldPow k' m hm) :=
  inferInstanceAs (Field (traitGenericField k'))

instance : IsAlgClosed (TraitGenericFieldPow k' m hm) :=
  inferInstanceAs (IsAlgClosed (traitGenericField k'))

noncomputable instance : Algebra (FractionRing (PowerSeries k')) (TraitGenericFieldPow k' m hm) :=
  ((algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')).comp
    (traitFractionPowMap k' m hm)).toAlgebra

lemma algebraMap_eq : algebraMap (FractionRing (PowerSeries k')) (TraitGenericFieldPow k' m hm) =
    (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')).comp
      (traitFractionPowMap k' m hm) :=
  rfl

/-- The identity of `Ω`, as a ring map from the standard structure to the twisted one. -/
noncomputable def ofField : traitGenericField k' →+* TraitGenericFieldPow k' m hm :=
  RingHom.id _

/-- The image of `t ↦ t^m` of a power series is in the base. -/
lemma algebraMap_expand (f : PowerSeries k') :
    ofField k' m hm (algebraMap (PowerSeries k') (traitGenericField k')
      (PowerSeries.expand m hm f)) =
      algebraMap (FractionRing (PowerSeries k')) (TraitGenericFieldPow k' m hm)
        (algebraMap _ _ f) := by
  change algebraMap (PowerSeries k') (traitGenericField k') (PowerSeries.expand m hm f) =
    algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')
      (traitFractionPowMap k' m hm (algebraMap _ _ f))
  rw [traitFractionPowMap_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- `t` is integral over `Frac k'⟦t⟧` acting through `t ↦ t^m`. -/
lemma isIntegral_X :
    _root_.IsIntegral (FractionRing (PowerSeries k'))
      (ofField k' m hm (algebraMap (PowerSeries k') (traitGenericField k') PowerSeries.X)) := by
  refine ⟨Polynomial.X ^ m - Polynomial.C (algebraMap (PowerSeries k') _ PowerSeries.X),
    Polynomial.monic_X_pow_sub_C _ hm, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ← algebraMap_expand,
    PowerSeries.expand_X, map_pow, map_pow, sub_self]


/-- Every element of `Frac k'⟦t⟧` is integral over `Frac k'⟦t⟧` acting through `t ↦ t^m`. -/
lemma isIntegral_algebraMap (a : FractionRing (PowerSeries k')) :
    _root_.IsIntegral (FractionRing (PowerSeries k'))
      (ofField k' m hm (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k') a)) := by
  have hA (f : PowerSeries k') : _root_.IsIntegral (FractionRing (PowerSeries k'))
      (ofField k' m hm (algebraMap (PowerSeries k') (traitGenericField k') f)) := by
    rw [PowerSeries.eq_sum_X_pow_mul_expand m hm f, map_sum, map_sum]
    refine IsIntegral.sum _ fun r _ ↦ ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    exact ((isIntegral_X k' m hm).pow r).mul
      (algebraMap_expand k' m hm _ ▸ _root_.isIntegral_algebraMap)
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries k') a
  rw [map_div₀, map_div₀, div_eq_mul_inv]
  have e (f : PowerSeries k') : ofField k' m hm
      (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k') (algebraMap _ _ f)) =
      ofField k' m hm (algebraMap (PowerSeries k') (traitGenericField k') f) := by
    rw [← IsScalarTower.algebraMap_apply]
  rw [e, e]
  exact (hA f).mul (hA g).inv

noncomputable instance :
    Algebra.IsIntegral (FractionRing (PowerSeries k')) (TraitGenericFieldPow k' m hm) := by
  let E : Subalgebra (FractionRing (PowerSeries k')) (TraitGenericFieldPow k' m hm) :=
    integralClosure _ _
  let ψ : FractionRing (PowerSeries k') →+* E :=
    ((ofField k' m hm).comp (algebraMap _ (traitGenericField k'))).codRestrict E.toSubring
      fun a ↦ isIntegral_algebraMap k' m hm a
  refine ⟨fun y ↦ isIntegral_trans (A := E) y ?_⟩
  obtain ⟨p, hp, hpy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := FractionRing (PowerSeries k'))
    (A := traitGenericField k') y).isIntegral
  refine ⟨p.map ψ, hp.map ψ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpy


instance : IsAlgClosure (FractionRing (PowerSeries k')) (TraitGenericFieldPow k' m hm) where
  isAlgClosed := inferInstance
  isAlgebraic := inferInstance

end TraitGenericFieldPow

/-- The automorphism `ω` of `Ω = (Frac k'⟦t⟧)^alg` extending `t ↦ t^m`. -/
noncomputable def traitGenericFieldPowEquiv : traitGenericField k' ≃+* traitGenericField k' :=
  (IsAlgClosure.equiv (FractionRing (PowerSeries k')) (traitGenericField k')
    (TraitGenericFieldPow k' m hm)).toRingEquiv

lemma traitGenericFieldPowEquiv_algebraMap (f : PowerSeries k') :
    traitGenericFieldPowEquiv k' m hm (algebraMap (PowerSeries k') (traitGenericField k') f) =
      algebraMap (PowerSeries k') (traitGenericField k') (PowerSeries.expand m hm f) := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))]
  have := (IsAlgClosure.equiv (FractionRing (PowerSeries k')) (traitGenericField k')
    (TraitGenericFieldPow k' m hm)).commutes (algebraMap _ _ f)
  exact this.trans (TraitGenericFieldPow.algebraMap_expand k' m hm f).symm

variable (k : Type u) [Field k] [Algebra k k']

/-- The power map `σ : S ⟶ S`, `t ↦ t^m`, of the trait `S = Spec k'⟦t⟧`. -/
noncomputable def traitPowMap : trait k' ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (PowerSeries.expand m hm).toRingHom)

/-- The automorphism of the geometric generic point `Spec Ω` lying over `σ`. -/
noncomputable def traitGenericPointPowMap :
    Spec (.of (traitGenericField k')) ⟶ Spec (.of (traitGenericField k')) :=
  Spec.map (CommRingCat.ofHom (traitGenericFieldPowEquiv k' m hm).toRingHom)

instance : IsIso (traitGenericPointPowMap k' m hm) := by
  have : IsIso (CommRingCat.ofHom (traitGenericFieldPowEquiv k' m hm).toRingHom) :=
    inferInstanceAs (IsIso (traitGenericFieldPowEquiv k' m hm).toCommRingCatIso.hom)
  unfold traitGenericPointPowMap
  infer_instance

@[reassoc]
lemma traitGenericPointPowMap_traitGenericPoint :
    traitGenericPointPowMap k' m hm ≫ traitGenericPoint k' =
      traitGenericPoint k' ≫ traitPowMap k' m hm := by
  rw [traitGenericPointPowMap, traitGenericPoint, traitPowMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext f
  exact traitGenericFieldPowEquiv_algebraMap k' m hm f

@[reassoc (attr := simp)]
lemma traitPowMap_traitToBase : traitPowMap k' m hm ≫ traitToBase k k' = traitToBase k k' := by
  rw [traitPowMap, traitToBase, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change PowerSeries.expand m hm (algebraMap k (PowerSeries k') a) = _
  rw [IsScalarTower.algebraMap_apply k k' (PowerSeries k'), PowerSeries.algebraMap_eq,
    PowerSeries.expand_C]
  change _ = algebraMap k (PowerSeries k') a
  rw [IsScalarTower.algebraMap_apply k k' (PowerSeries k'), PowerSeries.algebraMap_eq]

/-- The power map fixes the closed point of the trait. -/
@[reassoc (attr := simp)]
lemma traitClosedPoint_traitPowMap :
    traitClosedPoint k' ≫ traitPowMap k' m hm = traitClosedPoint k' := by
  rw [traitClosedPoint, traitPowMap, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun f ↦ ?_)
  exact PowerSeries.constantCoeff_expand m hm f

/-- A point of the trait is the closed point if and only if `t` vanishes at it. -/
lemma mem_range_traitClosedPoint_iff (z : trait k') :
    z ∈ Set.range (traitClosedPoint k') ↔ PowerSeries.X ∈ z.asIdeal := by
  rw [traitClosedPoint, Spec.map_base]
  change z ∈ Set.range (PrimeSpectrum.comap PowerSeries.constantCoeff) ↔ _
  have h := range_comap_of_surjective k' PowerSeries.constantCoeff
    (fun a ↦ ⟨PowerSeries.C a, by simp⟩)
  refine (Set.ext_iff.1 h z).trans ?_
  rw [PrimeSpectrum.mem_zeroLocus]
  refine ⟨fun h ↦ h (by simp), fun h f hf ↦ ?_⟩
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.2 (RingHom.mem_ker.1 hf)
  exact z.asIdeal.mul_mem_right g h

/-- The power map of the trait is the identity on the closed point and maps the generic point
to the generic point: the preimage of the closed point is the closed point. -/
lemma mem_range_traitClosedPoint_of_traitPowMap (z : trait k')
    (hz : traitPowMap k' m hm z ∈ Set.range (traitClosedPoint k')) :
    z ∈ Set.range (traitClosedPoint k') := by
  rw [mem_range_traitClosedPoint_iff] at hz ⊢
  rw [traitPowMap, Spec.map_base] at hz
  change PowerSeries.X ∈ Ideal.comap (PowerSeries.expand m hm).toRingHom z.asIdeal at hz
  rw [Ideal.mem_comap] at hz
  change PowerSeries.expand m hm PowerSeries.X ∈ z.asIdeal at hz
  rw [PowerSeries.expand_X] at hz
  exact z.isPrime.mem_of_pow_mem m hz

end AlgebraicGeometry
