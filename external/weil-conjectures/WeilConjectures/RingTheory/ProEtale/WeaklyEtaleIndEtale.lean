/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndBijectiveOnStalks
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
public import WeilConjectures.Mathlib.RingTheory.Etale.Weakly

/-!
# Weakly étale algebras are ind-étale locally ind-étale

In this file we prove Stacks 097Z (blueprint `thm:weakly-etale-ind-etale`):
if `R → S` is weakly étale, there exists a faithfully flat ind-étale `S → T`
such that `R → T` is ind-étale.

The proof follows the Stacks project:
1. Let `C = WStrictLocalization R` be a w-strictly local, faithfully flat, ind-étale
   `R`-algebra (Stacks 0980) and let `J ⊆ C` be the ideal cutting out the closed points
   of `Spec C`.
2. Base change to `D' = C ⊗[R] S`, which is weakly étale over `C` and faithfully flat
   ind-étale over `S`.
3. w-localize along `J`: the ring `D = (J·D')-WLocalization` is w-local, ind-Zariski over
   `D'` and the closed points of `Spec D` lie over closed points of `Spec C`
   (Stacks 097A).
4. By Olivier's theorem (`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`),
   the weakly étale map `C → D` is bijective on stalks, hence ind-Zariski by
   Stacks 097F (`Algebra.BijectiveOnStalks.indZariski_of_isWLocal`).
5. Thus `T = D` works: `S → D` is faithfully flat ind-étale and `R → C → D` is ind-étale.

The ring `D` is `Algebra.WeaklyEtale.refinement R S` (blueprint
`theorem-pro-etale-refinements-weakly-etale`), and its properties are
`Algebra.WeaklyEtale.indEtale_faithfullyFlat_refinement`
(blueprint `theorem-pro-etale-refinements-weakly-etale--1`).
-/

@[expose] public section

universe u

open PrimeSpectrum TensorProduct

section ResidueField

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A weakly étale ring map induces separable residue field extensions: if `q` is a prime
of `B` lying over the prime `m` of `A`, then `κ(q)` is separable over `κ(m)`.
This is a non-finite-type version of `Algebra.FormallyUnramified`'s residue separability,
proved via the fiber ring `κ(m) ⊗[A] B` which is ind-étale over `κ(m)` by Olivier's
results on weakly étale algebras over fields. -/
theorem Algebra.WeaklyEtale.isSeparable_residueField [Algebra.WeaklyEtale A B]
    (m : Ideal A) (q : Ideal B) [m.IsPrime] [q.IsPrime] [q.LiesOver m]
    [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
    [IsScalarTower A (Localization.AtPrime m) (Localization.AtPrime q)] :
    Algebra.IsSeparable m.ResidueField q.ResidueField := by
  have : Algebra.IndEtale m.ResidueField (m.Fiber B) :=
    Algebra.WeaklyEtale.indEtale_field m.ResidueField (m.Fiber B)
  -- The `κ(m)`-algebra map `κ(m) ⊗[A] B → κ(q)`.
  let χ : m.Fiber B →ₐ[m.ResidueField] q.ResidueField :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom A B q.ResidueField) fun _ _ ↦ Commute.all _ _
  have key (b : B) : IsSeparable m.ResidueField (algebraMap B q.ResidueField b) := by
    have h := Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing
      m.ResidueField q.ResidueField χ ((1 : m.ResidueField) ⊗ₜ[A] b)
    simpa [χ, Algebra.TensorProduct.lift_tmul] using h
  refine ⟨fun y ↦ ?_⟩
  rw [← mem_separableClosure_iff (F := m.ResidueField) (E := q.ResidueField)]
  obtain ⟨x', s', -, hxs⟩ := IsFractionRing.div_surjective (A := B ⧸ q) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  rw [← hxs, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  exact div_mem (mem_separableClosure_iff.mpr (key x))
    (mem_separableClosure_iff.mpr (key s))


/-- A weakly étale ring map induces algebraic residue field extensions. This is the shape
of hypothesis required by the w-localization lemmas (Stacks 097A). -/
theorem Algebra.WeaklyEtale.isAlgebraic_residueField_of_liesOver [Algebra.WeaklyEtale A B]
    (m : Ideal A) (q : Ideal B) [m.IsPrime] [q.IsPrime] [q.LiesOver m]
    [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
    [IsScalarTower A (Localization.AtPrime m) (Localization.AtPrime q)] :
    Algebra.IsAlgebraic m.ResidueField q.ResidueField :=
  have : Algebra.IsSeparable m.ResidueField q.ResidueField :=
    Algebra.WeaklyEtale.isSeparable_residueField m q
  inferInstance

end ResidueField

section BaseChangeSurjective

-- The faithful flatness of `κ(q)` over `κ(p)` goes through the residue field algebra
-- instances on localizations, which makes the instance search exceed the default limit.
/-- If `Spec A → Spec R` is surjective, so is any base change `Spec (S ⊗[R] A) → Spec S`.
(Surjectivity on spectra is stable under base change.) -/
lemma PrimeSpectrum.comap_surjective_tensorProduct_left {R A : Type u} (S : Type u)
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap R A))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap S (S ⊗[R] A))) := by
  intro q
  rw [← Set.mem_range, ← PrimeSpectrum.nontrivial_iff_mem_rangeComap]
  set p : Ideal R := q.asIdeal.comap (algebraMap R S) with hp
  have : p.IsPrime := Ideal.IsPrime.comap _
  have : q.asIdeal.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  -- `κ(p) ⊗[R] A` is nontrivial since `p` is in the image of `Spec A`.
  have h1 : Nontrivial (p.ResidueField ⊗[R] A) := by
    rw [PrimeSpectrum.nontrivial_iff_mem_rangeComap ⟨p, inferInstance⟩]
    exact h ⟨p, inferInstance⟩
  -- `κ(q)` is faithfully flat over `κ(p)`.
  have : Module.Free p.ResidueField q.asIdeal.ResidueField :=
    Module.Free.of_divisionRing _ _
  have : Module.FaithfullyFlat p.ResidueField q.asIdeal.ResidueField := inferInstance
  -- Chain of identifications: `κ(q) ⊗[S] (S ⊗[R] A) ≃ κ(q) ⊗[R] A ≃ κ(q) ⊗[κ(p)] (κ(p) ⊗[R] A)`.
  let e1 : q.asIdeal.ResidueField ⊗[S] (S ⊗[R] A) ≃ₐ[S] q.asIdeal.ResidueField ⊗[R] A :=
    Algebra.TensorProduct.cancelBaseChange R S S q.asIdeal.ResidueField A
  let e2 : q.asIdeal.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] A) ≃ₐ[p.ResidueField]
      q.asIdeal.ResidueField ⊗[R] A :=
    Algebra.TensorProduct.cancelBaseChange R p.ResidueField p.ResidueField
      q.asIdeal.ResidueField A
  have : Nontrivial (q.asIdeal.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] A)) :=
    Module.FaithfullyFlat.lTensor_nontrivial p.ResidueField q.asIdeal.ResidueField
      (p.ResidueField ⊗[R] A)
  have : Nontrivial (q.asIdeal.ResidueField ⊗[R] A) := e2.toEquiv.symm.nontrivial
  exact e1.toEquiv.nontrivial

end BaseChangeSurjective

section ClosedPointsSurjective

variable (R : Type u) [CommRing R]

open WStrictLocalization in
/-- Every prime of `R` is the image of a closed point of `Spec (WStrictLocalization R)`,
i.e. of a point of the zero locus of the ideal cutting out the closed points.
This is property (7) of Stacks 097X. -/
lemma WStrictLocalization.exists_mem_zeroLocus_comap_eq (p : PrimeSpectrum R) :
    ∃ x ∈ zeroLocus ((closedIdeal R).map
        (algebraMap (WLocalization R) (WStrictLocalization R)) : Set (WStrictLocalization R)),
      PrimeSpectrum.comap (algebraMap R (WStrictLocalization R)) x = p := by
  set W := WLocalization R
  set T₀ := IndEtaleContraction W
  -- A closed point `w` of `Spec W` over `p`.
  obtain ⟨w, hw_mem, hw⟩ :=
    (WLocalization.bijOn_algebraMap_specComap_zeroLocus_ideal R).surjOn (Set.mem_univ p)
  have hw_closed : w ∈ zeroLocus (closedIdeal R : Set W) := by
    rwa [zeroLocus_closedIdeal, ← WLocalization.zeroLocus_ideal_eq]
  -- A prime `u` of the ind-étale contraction over `w`; it lies in `V(contractionIdeal R)`.
  obtain ⟨u, hu⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := T₀) w
  have hu_comap : u.asIdeal.comap (algebraMap W T₀) = w.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hu
  have hu_mem : u ∈ zeroLocus (contractionIdeal R : Set T₀) := by
    rw [mem_zeroLocus, contractionIdeal, SetLike.coe_subset_coe,
      Ideal.map_le_iff_le_comap, hu_comap]
    exact (mem_zeroLocus _ _).mp hw_closed
  -- `V(contractionIdeal R)` consists of closed points of `Spec T₀`.
  have hI_sub : zeroLocus (contractionIdeal R : Set T₀) ⊆
      closedPoints (PrimeSpectrum T₀) := by
    rw [contractionIdeal]
    refine zeroLocus_map_algebraMap_subset_closedPoints (fun m' q' _ _ _ _ _ ↦ ?_)
      (zeroLocus_closedIdeal R).le
    have : Algebra.IsSeparable m'.ResidueField q'.ResidueField :=
      Algebra.IndEtale.isSeparable_residueField (R := W) (S := T₀) m' q'
    infer_instance
  -- A point of `V(J)` in the w-strict localization over `u`.
  obtain ⟨x, hx_mem, hx⟩ :=
    (Ideal.WLocalization.bijOn_zeroLocus_map (contractionIdeal R) hI_sub).surjOn hu_mem
  have hmap : (contractionIdeal R).map (algebraMap T₀ (WStrictLocalization R)) =
      (closedIdeal R).map (algebraMap W (WStrictLocalization R)) := by
    rw [contractionIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine ⟨x, by rwa [← hmap], ?_⟩
  have h1 : PrimeSpectrum.comap (algebraMap T₀ (WStrictLocalization R)) x = u := hx
  have h2 : PrimeSpectrum.comap (algebraMap W (WStrictLocalization R)) x =
      PrimeSpectrum.comap (algebraMap W T₀)
        (PrimeSpectrum.comap (algebraMap T₀ (WStrictLocalization R)) x) := by
    rw [← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq W T₀ (WStrictLocalization R)]
  have h3 : PrimeSpectrum.comap (algebraMap R (WStrictLocalization R)) x =
      PrimeSpectrum.comap (algebraMap R W)
        (PrimeSpectrum.comap (algebraMap W (WStrictLocalization R)) x) := by
    rw [← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq R W (WStrictLocalization R)]
  rw [h3, h2, h1, hu, hw]

end ClosedPointsSurjective

section Refinement

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra.WeaklyEtale

open WStrictLocalization

/-- The ideal `J · (C ⊗[R] S)` of the base change `C ⊗[R] S`, where
`C = WStrictLocalization R` and `J ⊆ C` is the ideal cutting out the closed points of
`Spec C`. -/
noncomputable def refinementIdeal : Ideal (WStrictLocalization R ⊗[R] S) :=
  ((closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R))).map
    (algebraMap (WStrictLocalization R) (WStrictLocalization R ⊗[R] S))

/-- The canonical refinement of an `R`-algebra `S` (blueprint
`theorem-pro-etale-refinements-weakly-etale`): the w-localization of `C ⊗[R] S` along
`J · (C ⊗[R] S)`, where `C = WStrictLocalization R` and `J ⊆ C` cuts out the closed points of
`Spec C`. If `S` is weakly étale over `R`, it is faithfully flat and ind-étale over `S`, and
ind-étale over `R` (`Algebra.WeaklyEtale.indEtale_faithfullyFlat_refinement`). -/
noncomputable def refinement : Type u :=
  (refinementIdeal R S).WLocalization

noncomputable instance : CommRing (refinement R S) :=
  inferInstanceAs <| CommRing (refinementIdeal R S).WLocalization

noncomputable instance algebraTensorProduct :
    Algebra (WStrictLocalization R ⊗[R] S) (refinement R S) :=
  inferInstanceAs <| Algebra _ (refinementIdeal R S).WLocalization

noncomputable instance algebraWStrictLocalization :
    Algebra (WStrictLocalization R) (refinement R S) :=
  inferInstanceAs <| Algebra (WStrictLocalization R)
    (((closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R))).map
      (algebraMap (WStrictLocalization R) (WStrictLocalization R ⊗[R] S))).WLocalization

instance : IsScalarTower (WStrictLocalization R) (WStrictLocalization R ⊗[R] S)
    (refinement R S) :=
  inferInstanceAs <| IsScalarTower (WStrictLocalization R) _
    (((closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R))).map
      (algebraMap (WStrictLocalization R) (WStrictLocalization R ⊗[R] S))).WLocalization

instance isWLocalRing : IsWLocalRing (refinement R S) :=
  inferInstanceAs <| IsWLocalRing (refinementIdeal R S).WLocalization

instance indZariski : Algebra.IndZariski (WStrictLocalization R ⊗[R] S) (refinement R S) :=
  inferInstanceAs <| Algebra.IndZariski _ (refinementIdeal R S).WLocalization

noncomputable instance algebraRight : Algebra S (refinement R S) :=
  Algebra.compHom _ (Algebra.TensorProduct.includeRight.toRingHom :
    S →+* WStrictLocalization R ⊗[R] S)

noncomputable instance : Algebra R (refinement R S) :=
  Algebra.compHom _ (algebraMap R (WStrictLocalization R))

instance : IsScalarTower R (WStrictLocalization R) (refinement R S) :=
  .of_algebraMap_eq' rfl

instance : IsScalarTower R S (refinement R S) := IsScalarTower.of_algebraMap_eq fun r ↦ by
  change algebraMap (WStrictLocalization R ⊗[R] S) (refinement R S)
      (algebraMap R (WStrictLocalization R) r ⊗ₜ[R] 1) =
    algebraMap (WStrictLocalization R ⊗[R] S) (refinement R S) (1 ⊗ₜ[R] algebraMap R S r)
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsScalarTower S (WStrictLocalization R ⊗[R] S) (refinement R S) :=
  .of_algebraMap_eq' rfl

end Algebra.WeaklyEtale

end Refinement

section Main

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

open WStrictLocalization in
/-- **Stacks 097Z** (blueprint `theorem-pro-etale-refinements-weakly-etale--1`): if `S` is a weakly
étale `R`-algebra, its canonical refinement `Algebra.WeaklyEtale.refinement R S` is ind-étale and
faithfully flat over `S`, and ind-étale over `R`. -/
theorem Algebra.WeaklyEtale.indEtale_faithfullyFlat_refinement [Algebra.WeaklyEtale R S] :
    Algebra.IndEtale S (refinement R S) ∧ Module.FaithfullyFlat S (refinement R S) ∧
      Algebra.IndEtale R (refinement R S) := by
  classical
  -- Step 1: the w-strictly local cover `C` of `R` and the ideal `J` of closed points.
  set C := WStrictLocalization R with hC
  set J : Ideal C := (closedIdeal R).map (algebraMap (WLocalization R) C) with hJdef
  have hJ : zeroLocus (J : Set C) = closedPoints (PrimeSpectrum C) :=
    zeroLocus_map_eq_closedPoints R
  -- Step 2: the base change `D' = C ⊗[R] S`.
  set D' := C ⊗[R] S with hD'
  -- Step 3: the w-localization `D` of `D'` along `J`.
  set K : Ideal D' := J.map (algebraMap C D') with hKdef
  set D := refinement R S with hDdef
  -- `C → D'` is weakly étale (base change) and induces algebraic residue field extensions.
  have : Algebra.WeaklyEtale C D' := inferInstance
  have hres : ∀ (m : Ideal C) (q' : Ideal D') [q'.LiesOver m] [m.IsMaximal] [q'.IsPrime]
      [Algebra (Localization.AtPrime m) (Localization.AtPrime q')]
      [IsScalarTower C (Localization.AtPrime m) (Localization.AtPrime q')],
      Algebra.IsAlgebraic m.ResidueField q'.ResidueField := by
    intro m q' _ hm _ _ _
    have : m.IsPrime := hm.isPrime
    exact Algebra.WeaklyEtale.isAlgebraic_residueField_of_liesOver m q'
  -- Stacks 097A: closed points of `Spec D` are the preimage of those of `Spec C`.
  have hDclosed : zeroLocus ((J.map (algebraMap C D) : Ideal D) : Set D) =
      closedPoints (PrimeSpectrum D) :=
    Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq hJ hres
  -- `C → D` is weakly étale.
  have : Algebra.WeaklyEtale D' D := inferInstance
  have : Algebra.WeaklyEtale C D := Algebra.WeaklyEtale.trans C D' D
  -- Every maximal ideal of `D` lies over a maximal ideal of `C`.
  have hmaxC : ∀ (n : Ideal D) [n.IsMaximal], (n.comap (algebraMap C D)).IsMaximal := by
    intro n hn
    have hn_mem : (⟨n, hn.isPrime⟩ : PrimeSpectrum D) ∈ closedPoints (PrimeSpectrum D) :=
      mem_closedPoints_iff.mpr ((isClosed_singleton_iff_isMaximal _).mpr hn)
    rw [← hDclosed] at hn_mem
    have hJle : J ≤ n.comap (algebraMap C D) := by
      rw [← Ideal.map_le_iff_le_comap]
      exact (mem_zeroLocus _ _).mp hn_mem
    have : (n.comap (algebraMap C D)).IsPrime := Ideal.IsPrime.comap _
    have hmem : (⟨n.comap (algebraMap C D), inferInstance⟩ : PrimeSpectrum C) ∈
        closedPoints (PrimeSpectrum C) := by
      rw [← hJ]
      exact (mem_zeroLocus _ _).mpr hJle
    exact (isClosed_singleton_iff_isMaximal _).mp (mem_closedPoints_iff.mp hmem)
  -- `C → D` is bijective on stalks, by Olivier's theorem.
  have : Algebra.BijectiveOnStalks C D := by
    apply Algebra.WeaklyEtale.bijectiveOnStalks
    intro q hq
    obtain ⟨n, hn_max, hqn⟩ := q.exists_le_maximal hq.ne_top
    refine ⟨n, hn_max.isPrime, hqn, ?_⟩
    have := hn_max
    have : (n.comap (algebraMap C D)).IsMaximal := hmaxC n
    exact IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization _
  -- `Spec D → Spec C` is w-local.
  have hwloc : (algebraMap C D).IsWLocal := by
    rw [RingHom.isWLocal_iff_isMaximal_of_isMaximal]
    intro n hn
    exact hmaxC n
  -- Stacks 097F: `C → D` is ind-Zariski, hence `R → D` is ind-étale.
  have : Algebra.IndZariski C D := Algebra.BijectiveOnStalks.indZariski_of_isWLocal C D hwloc
  have : Algebra.IndEtale R D := Algebra.IndEtale.trans R (S := C) D
  -- `S → D'` is faithfully flat and ind-étale (base change of `R → C`).
  have hSD'_ind : (algebraMap S D').IndEtale :=
    RingHom.IndEtale.isStableUnderBaseChange R C S D'
      ((RingHom.IndEtale.algebraMap_iff R C).mpr inferInstance)
  have hSD'_ff : (algebraMap S D').FaithfullyFlat :=
    RingHom.FaithfullyFlat.isStableUnderBaseChange R C S D'
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Algebra.IndEtale S D' := (RingHom.IndEtale.algebraMap_iff S D').mp hSD'_ind
  have : Module.FaithfullyFlat S D' := RingHom.faithfullyFlat_algebraMap_iff.mp hSD'_ff
  -- The `S`-algebra structure on `D`.
  have : Algebra.IndEtale S D := Algebra.IndEtale.trans S (S := D') D
  -- `S → D` is faithfully flat: flatness is clear, surjectivity on spectra is the content.
  have : Module.Flat S D := Module.Flat.trans S D' D
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap S D)) := by
    -- `Spec (C ⧸ J) → Spec R` is surjective by `exists_mem_zeroLocus_comap_eq`.
    have hC₀ : Function.Surjective (PrimeSpectrum.comap (algebraMap R (C ⧸ J))) := by
      intro p
      obtain ⟨x, hx_mem, hx⟩ := WStrictLocalization.exists_mem_zeroLocus_comap_eq R p
      have hker : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
        exact hx_mem
      obtain ⟨x', hx'⟩ := hker
      refine ⟨x', ?_⟩
      have : PrimeSpectrum.comap (algebraMap R (C ⧸ J)) x' =
          PrimeSpectrum.comap (algebraMap R C)
            (PrimeSpectrum.comap (algebraMap C (C ⧸ J)) x') := by
        rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R C (C ⧸ J)]
      rw [this, show algebraMap C (C ⧸ J) = Ideal.Quotient.mk J from rfl, hx', hx]
    -- base change: `Spec (S ⊗[R] (C ⧸ J)) → Spec S` is surjective.
    have hSC₀ := PrimeSpectrum.comap_surjective_tensorProduct_left S hC₀
    intro q
    obtain ⟨Q₀, hQ₀⟩ := hSC₀ q
    -- transport `Q₀` to a prime of `D'` containing `K` and lying over `q`.
    let π : D' →ₐ[R] (S ⊗[R] (C ⧸ J)) :=
      (Algebra.TensorProduct.comm R (C ⧸ J) S).toAlgHom.comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R S))
    set Q : PrimeSpectrum D' := PrimeSpectrum.comap π.toRingHom Q₀ with hQdef
    have hQK : Q ∈ zeroLocus (K : Set D') := by
      rw [mem_zeroLocus, hKdef, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
      intro j hj
      change π (algebraMap C D' j) ∈ Q₀.asIdeal
      have hπj : π (algebraMap C D' j) = 0 := by
        change (Algebra.TensorProduct.comm R (C ⧸ J) S)
            ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R S))
              ((j : C) ⊗ₜ[R] (1 : S))) = 0
        rw [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.mpr hj, TensorProduct.zero_tmul, map_zero]
      rw [hπj]
      exact zero_mem _
    have hQq : PrimeSpectrum.comap (algebraMap S D') Q = q := by
      have hcomp : π.toRingHom.comp (algebraMap S D') = algebraMap S (S ⊗[R] (C ⧸ J)) := by
        refine RingHom.ext fun s ↦ ?_
        change (Algebra.TensorProduct.comm R (C ⧸ J) S)
            ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R S))
              ((1 : C) ⊗ₜ[R] s)) = s ⊗ₜ[R] (1 : C ⧸ J)
        rw [Algebra.TensorProduct.map_tmul, map_one]
        simp [Algebra.TensorProduct.comm_tmul]
      rw [hQdef, ← PrimeSpectrum.comap_comp_apply, hcomp, hQ₀]
    -- pull `Q` back along the w-localization `D' → D`.
    have hK_sub : zeroLocus (K : Set D') ⊆ closedPoints (PrimeSpectrum D') := by
      rw [hKdef]
      exact zeroLocus_map_algebraMap_subset_closedPoints hres hJ.le
    obtain ⟨P, hP_mem, hP⟩ := (Ideal.WLocalization.bijOn_zeroLocus_map K hK_sub).surjOn hQK
    refine ⟨P, ?_⟩
    have hP' : PrimeSpectrum.comap (algebraMap D' D) P = Q := hP
    rw [IsScalarTower.algebraMap_eq S D' D, PrimeSpectrum.comap_comp_apply, hP', hQq]
  have : Module.FaithfullyFlat S D := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact ⟨inferInstance, inferInstance, inferInstance⟩

open WStrictLocalization in
/-- **Stacks 097Z** (blueprint `thm:weakly-etale-ind-etale`): if `S` is a weakly étale
`R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T` such that `T` is an
ind-étale `R`-algebra. -/
theorem Algebra.WeaklyEtale.exists_indEtale [Algebra.WeaklyEtale R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra S T) (_ : IsScalarTower R S T),
      Algebra.IndEtale S T ∧ Module.FaithfullyFlat S T ∧ Algebra.IndEtale R T :=
  ⟨refinement R S, inferInstance, inferInstance, inferInstance, inferInstance,
    indEtale_faithfullyFlat_refinement R S⟩

end Main

/-- If `S` is a weakly étale `R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T`
such that `T` is an ind-étale `R`-algebra. -/
theorem RingHom.WeaklyEtale.exists_indEtale_comp {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.WeaklyEtale) :
    ∃ (T : Type u) (_ : CommRing T) (g : S →+* T),
      g.IndEtale ∧ g.FaithfullyFlat ∧ (g.comp f).IndEtale := by
  algebraize [f]
  obtain ⟨T, _, _, _, _, h₁, h₂, h₃⟩ := Algebra.WeaklyEtale.exists_indEtale R S
  refine ⟨T, inferInstance, algebraMap S T, ?_, ?_, ?_⟩
  · rwa [IndEtale.algebraMap_iff]
  · rwa [faithfullyFlat_algebraMap_iff]
  · rwa [← RingHom.algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq, IndEtale.algebraMap_iff]
