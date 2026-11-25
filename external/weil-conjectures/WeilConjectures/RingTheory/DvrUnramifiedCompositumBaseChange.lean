/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Further base change of an unramified DVR compositum

Source: Stacks Project, Tag 09EQ, tensor and local-factor argument.
(blueprint: lem-sbc-dvr-unramified-compositum-base-change) -/

@[expose] public section
universe u
namespace RingTheory
open scoped TensorProduct

private theorem dvr_map_injective
    (S T : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] (g : S →+* T) (p : S) (hp : Irreducible p)
    (hgp : g p ≠ 0) : Function.Injective g := by
  intro x z hxz
  by_contra hne
  have hn : x - z ≠ 0 := sub_ne_zero.mpr hne
  have hz : g (x - z) = 0 := by rw [map_sub, hxz, sub_self]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hn hp
  obtain ⟨w, hw⟩ := hn.symm
  have hnot : g (p ^ n * (w : S)) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero n hgp) (w.isUnit.map g).ne_zero
  exact hnot (by rw [hw]; exact hz)

/-- An essentially unramified DVR extension stays so in a local field compositum.

Source: Stacks Project, Tag 09EQ, proof; Tags 09E7 and 02FM.
(blueprint: lem-sbc-dvr-unramified-compositum-base-change)

Proof: Faithfulness makes V torsion-free and hence flat over the DVR R.
Form D=A tensor_R V and map it to T using the two compatible maps. Let Q
be the inverse image of the maximal ideal of T and S=D_Q. The map S -> T
is local, and its composite with A -> S is the given local map A -> T.
Essential finite type, flatness and formal unramifiedness survive this
base change and localization. The local unramified criterion gives
m(A)S=m(S). Regularity therefore ascends from A to S. Flatness keeps a
uniformizer p of A nonzero in S, where it generates m(S); consequently S
is a DVR. A base uniformizer of R stays nonzero in T, by compatibility
with iV and faithfulness of R -> V. Since its image in A is a multiple
of p, the image of p in T is nonzero. Uniformizer factorization in S
therefore makes S -> T injective. Extend it to Frac(S) -> F. The map
V -> S also extends to Frac(V) -> Frac(S), and the two composites to F
agree on V, hence on Frac(V). Thus the range of Frac(S) -> F contains
A and iV(Frac(V)); generation makes that field map surjective, proving
that F is the fraction field of S. Maximality of valuation rings under
local inclusions in a common fraction field makes S -> T surjective.
Transfer essential finite type and formal unramifiedness along this
surjective A-algebra map. No finiteness assumption on A/R is used. -/
theorem dvr_unramified_compositum_base_change
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Algebra R V] [IsLocalHom (algebraMap R V)] [FaithfulSMul R V]
    [Algebra.EssFiniteType R V] [Algebra.FormallyUnramified R V]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    (k : V →+* T)
    (hR : ∀ r : R, k (algebraMap R V r) = algebraMap A T (algebraMap R A r))
    (F : Type u) [Field F] [Algebra A F] [Algebra T F]
    [IsFractionRing T F] [IsScalarTower A T F]
    (iV : FractionRing V →+* F)
    (hiV : ∀ v : V, iV (algebraMap V (FractionRing V) v) = algebraMap T F (k v))
    (hgen : Algebra.adjoin A (Set.range iV) = ⊤) :
    Algebra.EssFiniteType A T ∧ Algebra.FormallyUnramified A T := by
  classical
  let : Algebra R T := ((algebraMap A T).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
  let ka : V →ₐ[R] T := { toRingHom := k, commutes' := hR }
  let D := A ⊗[R] V
  let phi : D →ₐ[A] T := Algebra.TensorProduct.lift
    (Algebra.ofId A T) ka (fun _ _ ↦ Commute.all _ _)
  let Q : Ideal D := (IsLocalRing.maximalIdeal T).comap phi.toRingHom
  let : Q.IsPrime := Ideal.IsPrime.comap phi.toRingHom
  let S := Localization.AtPrime Q
  let g : S →+* T := IsLocalization.lift (fun s : Q.primeCompl ↦
    show IsUnit (phi s) from by
      have hs := s.2
      change ¬ ¬ IsUnit (phi (s : D)) at hs
      exact not_not.mp hs)
  have hg (d : D) : g (algebraMap D S d) = phi d := IsLocalization.lift_eq _ _
  have hgalg : ∀ a : A, g (algebraMap A S a) = algebraMap A T a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A D S, hg]
    exact phi.commutes a
  have hglocal : IsLocalHom g := by
    constructor
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl z
    apply (IsLocalization.AtPrime.isUnit_mk'_iff S Q x s).mpr
    intro hx
    have hxunit : IsUnit (phi x) := by
      rw [← hg]
      rw [← IsLocalization.mk'_spec S x s, map_mul]
      exact hz.mul (g.isUnit_map (IsLocalization.map_units S s))
    exact hx hxunit
  have hASlocal : IsLocalHom (algebraMap A S) := by
    have : IsLocalHom (g.comp (algebraMap A S)) := by
      have heq : g.comp (algebraMap A S) = algebraMap A T := RingHom.ext hgalg
      rw [heq]
      infer_instance
    exact isLocalHom_of_comp _ g
  let := hASlocal
  let : Module.Flat R V := inferInstance
  let : Module.Flat A D := inferInstance
  let : Module.Flat A S := Module.Flat.trans A D S
  let : Algebra.EssFiniteType A D := inferInstance
  let : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A D S
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing A S
  let : Algebra.FormallyUnramified A D := inferInstance
  let : Algebra.FormallyUnramified A S := Algebra.FormallyUnramified.comp A D S
  have hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A S) =
      IsLocalRing.maximalIdeal S := Algebra.FormallyUnramified.map_maximalIdeal
  let : IsRegularLocalRing A := IsRegularLocalRing.of_isIntegrallyClosed A (by
    exact Ring.krullDimLE_iff.mp inferInstance)
  let : IsRegularLocalRing S := IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq hmax
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hpS : algebraMap A S p ≠ 0 := by
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A S)).mpr hp.ne_zero
  let : IsDiscreteValuationRing S := IsDiscreteValuationRing.of_maximalIdeal_eq_span_singleton
    hpS (by rw [← hmax, hp.maximalIdeal_eq, Ideal.map_span, Set.image_singleton])
  have hpT : algebraMap A T p ≠ 0 := by
    obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hrV : algebraMap R V r ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R V)).mpr hr.ne_zero
    have hrT : k (algebraMap R V r) ≠ 0 := by
      intro hz
      have heq := hiV (algebraMap R V r)
      rw [hz, map_zero] at heq
      exact (map_ne_zero_iff _ iV.injective).mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hrV) heq
    have hrA : algebraMap R A r ∈ IsLocalRing.maximalIdeal A :=
      map_nonunit _ r (by
        rw [hr.maximalIdeal_eq]
        exact Ideal.mem_span_singleton_self r)
    rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hrA
    obtain ⟨z, hz⟩ := hrA
    intro hp0
    apply hrT
    rw [hR, hz, map_mul, hp0, zero_mul]
  have hmaxp : IsLocalRing.maximalIdeal S = Ideal.span {algebraMap A S p} := by
    rw [← hmax, hp.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hps : Irreducible (algebraMap A S p) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hpS hmaxp
  have hginj : Function.Injective g :=
    dvr_map_injective S T g _ hps (by rw [hgalg]; exact hpT)
  let gF : S →+* F := (algebraMap T F).comp g
  have hgFinj : Function.Injective gF := (IsFractionRing.injective T F).comp hginj
  let : Algebra S F := gF.toAlgebra
  have : IsScalarTower A S F := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    change algebraMap A F a = algebraMap T F (g (algebraMap A S a))
    rw [hgalg, IsScalarTower.algebraMap_apply A T F])
  let L := FractionRing S
  let iS : L →+* F := IsFractionRing.lift hgFinj
  have hiS (s : S) : iS (algebraMap S L s) = gF s := IsFractionRing.lift_algebraMap _ _
  let vS : V →+* S := (algebraMap D S).comp
    (Algebra.TensorProduct.includeRight : V →ₐ[R] D).toRingHom
  have hgv (v : V) : g (vS v) = k v := by
    rw [show g (vS v) = phi ((Algebra.TensorProduct.includeRight : V →ₐ[R] D) v)
      from hg _]
    exact (Algebra.TensorProduct.lift_tmul (Algebra.ofId A T) ka
      (fun _ _ ↦ Commute.all _ _) 1 v).trans (by simp [ka])
  have hvSinj : Function.Injective vS := by
    intro x y hxy
    apply (IsFractionRing.injective V (FractionRing V))
    apply iV.injective
    rw [hiV, hiV, ← hgv, ← hgv, hxy]
  let vL : V →+* L := (algebraMap S L).comp vS
  have hvLinj : Function.Injective vL := (IsFractionRing.injective S L).comp hvSinj
  let iVS : FractionRing V →+* L := IsFractionRing.lift hvLinj
  have hiVS (v : V) : iVS (algebraMap V (FractionRing V) v) = algebraMap S L (vS v) :=
    IsFractionRing.lift_algebraMap _ _
  have hcomp : iS.comp iVS = iV := by
    apply IsFractionRing.ringHom_ext (A := V)
    intro v
    rw [RingHom.comp_apply, hiVS, hiS]
    exact (congrArg (algebraMap T F) (hgv v)).trans (hiV v).symm
  let fS : L →ₐ[A] F :=
    { toRingHom := iS
      commutes' := fun a ↦ by
        change iS (algebraMap A L a) = algebraMap A F a
        rw [IsScalarTower.algebraMap_apply A S L, hiS]
        change algebraMap T F (g (algebraMap A S a)) = algebraMap A F a
        rw [hgalg, ← IsScalarTower.algebraMap_apply A T F] }
  have hrange : Algebra.adjoin A (Set.range iV) ≤ fS.range := by
    apply Algebra.adjoin_le
    rintro _ ⟨v, rfl⟩
    exact ⟨iVS v, RingHom.congr_fun hcomp v⟩
  have hsurj : Function.Surjective iS := by
    intro x
    exact hrange (hgen ▸ (show x ∈ (⊤ : Subalgebra A F) from trivial))
  let e : L ≃ₐ[S] F := AlgEquiv.ofBijective
    { toRingHom := iS, commutes' := hiS } ⟨iS.injective, hsurj⟩
  let : IsFractionRing S F := IsFractionRing.of_algEquiv e
  let := hglocal
  have hbij : Function.Bijective ((algebraMap T F).rangeRestrict.comp g) :=
    bijective_rangeRestrict_comp_of_valuationRing g (algebraMap T F) rfl
  have hgsurj : Function.Surjective g := by
    intro t
    obtain ⟨s, hs⟩ := hbij.2 ((algebraMap T F).rangeRestrict t)
    exact ⟨s, (IsFractionRing.injective T F) (congrArg Subtype.val hs)⟩
  let gA : S →ₐ[A] T := { toRingHom := g, commutes' := hgalg }
  exact ⟨Algebra.EssFiniteType.of_surjective gA hgsurj,
    Algebra.FormallyUnramified.of_surjective gA hgsurj⟩

end RingTheory
