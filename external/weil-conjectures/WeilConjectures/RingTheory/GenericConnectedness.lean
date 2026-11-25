/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.RingTheory.GenericIrreducibility
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Generic connectedness of fibres

Let `A` be a noetherian domain with fraction field `K` and `C` a finite type `A`-algebra with an
`A`-valued point whose generic fibre is connected. Then the fibres of `Spec C → Spec A` over a
dense open subset of `Spec A` are connected (Stacks `055G`, ring-theoretic form).

## Main statements

- `exists_ne_zero_forall_connectedSpace_fiber`: generic connectedness of fibres.

## References

- Stacks Project, Tag `055G`, <https://stacks.math.columbia.edu/tag/055G>
-/

@[expose] public section

universe u

open TensorProduct

namespace GenericConnectedness

/-- In a preconnected space covered by finitely many nonempty closed sets `W i`, for every
nontrivial partition of the index set, two of the sets from different parts meet. -/
lemma exists_inter_nonempty_of_preconnectedSpace {X ι : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Finite ι] {W : ι → Set X} (hW : ∀ i, IsClosed (W i))
    (hne : ∀ i, (W i).Nonempty) (hcov : ⋃ i, W i = Set.univ) {U : Set ι}
    (hU : U.Nonempty) (hU' : Uᶜ.Nonempty) : ∃ i ∈ U, ∃ j ∉ U, (W i ∩ W j).Nonempty := by
  by_contra! h
  have hY : ⋃ i ∈ U, W i = (⋃ j ∈ Uᶜ, W j)ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff, exists_prop, not_exists, not_and]
    refine ⟨fun ⟨i, hi, hx⟩ j hj hx' ↦ (h i hi j hj).subset ⟨hx, hx'⟩, fun H ↦ ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
    by_cases hkU : k ∈ U
    · exact ⟨k, hkU, hk⟩
    · exact absurd hk (H k hkU)
  have hc : IsClopen (⋃ i ∈ U, W i) := by
    refine ⟨(Set.toFinite U).isClosed_biUnion fun i _ ↦ hW i, ?_⟩
    rw [hY, isOpen_compl_iff]
    exact (Set.toFinite _).isClosed_biUnion fun i _ ↦ hW i
  obtain ⟨i, hi⟩ := hU
  obtain ⟨j, hj⟩ := hU'
  rcases isClopen_iff.mp hc with h0 | h0
  · obtain ⟨x, hx⟩ := hne i
    exact (h0 ▸ Set.mem_biUnion hi hx : x ∈ (∅ : Set X))
  · obtain ⟨x, hx⟩ := hne j
    have hx' : x ∈ ⋃ i ∈ U, W i := h0 ▸ Set.mem_univ x
    rw [hY] at hx'
    exact hx' (Set.mem_biUnion hj hx)

/-- A space covered by preconnected sets `W i` is preconnected if for every nontrivial partition
of the index set, two of the sets from different parts meet. -/
lemma preconnectedSpace_of_iUnion_eq_univ {X ι : Type*} [TopologicalSpace X] {W : ι → Set X}
    (hW : ∀ i, IsPreconnected (W i)) (hcov : ⋃ i, W i = Set.univ)
    (hU : ∀ U : Set ι, U.Nonempty → Uᶜ.Nonempty → ∃ i ∈ U, ∃ j ∉ U, (W i ∩ W j).Nonempty) :
    PreconnectedSpace X := by
  rw [preconnectedSpace_iff_clopen]
  intro V hV
  have hsub (i : ι) (h : (W i ∩ V).Nonempty) : W i ⊆ V := (hW i).subset_isClopen hV h
  have hmem (x : X) : ∃ i, x ∈ W i := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
  by_cases h1 : {i | W i ⊆ V}.Nonempty
  · by_cases h2 : {i | W i ⊆ V}ᶜ.Nonempty
    · obtain ⟨i, hi, j, hj, x, hxi, hxj⟩ := hU _ h1 h2
      exact absurd (hsub j ⟨x, hxj, hi hxi⟩) hj
    · refine Or.inr (Set.eq_univ_of_forall fun x ↦ ?_)
      obtain ⟨i, hi⟩ := hmem x
      by_contra hx
      exact h2 ⟨i, fun h ↦ hx (h hi)⟩
  · refine Or.inl (Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_)
    obtain ⟨i, hi⟩ := hmem x
    exact h1 ⟨i, hsub i ⟨x, hi, hx⟩⟩

open AlgebraicGeometry CategoryTheory Limits in
/-- Ring-theoretic form of Stacks `04KV`: if `C` is an `A`-algebra with an `A`-valued point and
`Spec (K ⊗[A] C)` is connected for a field `K` over `A`, then so is `Spec (L ⊗[A] C)` for every
field extension `L` of `K`. -/
theorem connectedSpace_tensor_of_section {A C K L : Type u} [CommRing A] [CommRing C]
    [Algebra A C] [Field K] [Algebra A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] (s : C →ₐ[A] A) (hC : ConnectedSpace (PrimeSpectrum (K ⊗[A] C))) :
    ConnectedSpace (PrimeSpectrum (L ⊗[A] C)) := by
  let σ : K ⊗[A] C →ₐ[K] K := Algebra.TensorProduct.lift (Algebra.ofId K K)
    ((Algebra.ofId A K).comp s) fun _ _ ↦ .all _ _
  let f := Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[A] C)))
  have : ConnectedSpace (Spec (.of (K ⊗[A] C))) := hC
  have hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  have hgc := GeometricallyConnected.of_connectedSpace_of_section f _ hs
  have : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
    hgc.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)
  have : ConnectedSpace (PrimeSpectrum ((K ⊗[A] C) ⊗[K] L)) :=
    (pullbackSpecIso K (K ⊗[A] C) L).hom.homeomorph.connectedSpace_iff.mp this
  exact (PrimeSpectrum.homeomorphOfRingEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange A K L L C).toRingEquiv)).connectedSpace_iff.mp this

/-- Let `S` be a finite type algebra over a noetherian domain `R` and `J` an ideal of `S` contained
in a prime of `S` lying over `0`. Then every prime of `R` outside some `V(c)`, `c ≠ 0`, is the
contraction of a prime of `S` containing `J`. -/
lemma exists_ne_zero_forall_exists_comap_eq {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (J : Ideal S)
    (hJ : ∃ P : PrimeSpectrum S, J ≤ P.asIdeal ∧ P.asIdeal.comap (algebraMap R S) = ⊥) :
    ∃ c : R, c ≠ 0 ∧ ∀ t : PrimeSpectrum R, c ∉ t.asIdeal →
      ∃ P : PrimeSpectrum S, J ≤ P.asIdeal ∧ PrimeSpectrum.comap (algebraMap R S) P = t := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  set Z := PrimeSpectrum.comap (algebraMap R S) '' PrimeSpectrum.zeroLocus (J : Set S)
  have hJc : Topology.IsConstructible (PrimeSpectrum.zeroLocus (J : Set S)) :=
    Topology.isConstructible_compl.mp ((PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg
      (IsNoetherian.noetherian J)).isConstructible
        (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl)
  have hZ : Topology.IsConstructible Z := PrimeSpectrum.isConstructible_comap_image
    (RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)) hJc
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∉ Zᶜ := by
    obtain ⟨P, hJP, hP⟩ := hJ
    rw [Set.notMem_compl_iff]
    exact ⟨P, hJP, PrimeSpectrum.ext hP⟩
  obtain ⟨c, hc, hZc⟩ := BertiniNoether.exists_ne_zero_forall_mem_of_isConstructible hZ.compl hgen
  refine ⟨c, hc, fun t ht ↦ ?_⟩
  obtain ⟨P, hP, rfl⟩ : t ∈ Z := by
    by_contra h
    exact ht (hZc t h)
  exact ⟨P, hP, rfl⟩

set_option backward.isDefEq.respectTransparency false in
-- the tensor product with a quotient carries two semiring structures
/-- **Generic connectedness, split case.** Let `A'` be a noetherian domain contained in an
algebraically closed field `L` and `C` an algebra over a ring `A` below `A'`, with
`S = A' ⊗[A] C` of finite type over `A'`. Suppose that ideals `I i` of `S` cut out closed subsets
whose geometric generic fibres are irreducible, cover the geometric generic fibre (`∏ I i`
becomes nilpotent in `L ⊗[A] C`), and form a connected configuration over the generic point.
Then the fibres of `Spec S → Spec A'` over a dense open subset are preconnected. -/
theorem exists_ne_zero_forall_preconnectedSpace_of_cover {A A' C : Type*} [CommRing A]
    [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [CommRing C] [Algebra A C]
    [Algebra A A'] [Algebra.FiniteType A' (A' ⊗[A] C)] (L : Type*) [Field L] [IsAlgClosed L]
    [Algebra A' L] [Algebra A L] [IsScalarTower A A' L]
    (hA'L : Function.Injective (algebraMap A' L)) {ι : Type*} [Fintype ι]
    (I : ι → Ideal (A' ⊗[A] C))
    (hirr : ∀ i, IrreducibleSpace (PrimeSpectrum (L ⊗[A'] ((A' ⊗[A] C) ⧸ I i))))
    (hnil : ∀ x ∈ ∏ i, I i, IsNilpotent
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L) (AlgHom.id A C) x))
    (hU : ∀ U : Set ι, U.Nonempty → Uᶜ.Nonempty → ∃ i ∈ U, ∃ j ∉ U,
      ∃ P : PrimeSpectrum (A' ⊗[A] C),
        I i ⊔ I j ≤ P.asIdeal ∧ P.asIdeal.comap (algebraMap A' (A' ⊗[A] C)) = ⊥) :
    ∃ a : A', a ≠ 0 ∧ ∀ t : PrimeSpectrum A', a ∉ t.asIdeal →
      PreconnectedSpace (PrimeSpectrum (t.asIdeal.ResidueField ⊗[A'] (A' ⊗[A] C))) := by
  classical
  have : IsNoetherianRing (A' ⊗[A] C) := Algebra.FiniteType.isNoetherianRing A' (A' ⊗[A] C)
  let K' := FractionRing A'
  let : Algebra K' L := (IsFractionRing.lift hA'L).toAlgebra
  have : IsScalarTower A' K' L := .of_algebraMap_eq fun a ↦
    (IsFractionRing.lift_algebraMap hA'L a).symm
  -- generic irreducibility of the pieces
  choose a ha0 ha using fun i ↦
    exists_ne_zero_forall_isIrreducible_fiber (A := A') (C := (A' ⊗[A] C) ⧸ I i) K' L (hirr i)
  -- the pieces cover the fibres generically
  obtain ⟨T', hT'⟩ := (IsNoetherian.noetherian (∏ i, I i) : (∏ i, I i).FG)
  have hTk (x : A' ⊗[A] C) (hx : x ∈ T') : x ∈ ∏ i, I i := hT' ▸ Submodule.subset_span hx
  have hkill (x : A' ⊗[A] C) (hx : x ∈ T') : ∃ b : A', b ≠ 0 ∧ ∃ m : ℕ, b • x ^ m = 0 := by
    obtain ⟨m, hm⟩ := hnil x (hTk x hx)
    rw [← map_pow] at hm
    obtain ⟨b, hb, hbm⟩ := GenericIrreducibility.exists_smul_eq_zero_of_map_eq_zero hA'L _ hm
    exact ⟨b, hb, m, hbm⟩
  choose! b hb0 m hbm using hkill
  -- the pieces meet generically
  have hmeet (i j : ι) : ∃ c : A', c ≠ 0 ∧ ∀ t : PrimeSpectrum A', c ∉ t.asIdeal →
      (∃ P : PrimeSpectrum (A' ⊗[A] C), I i ⊔ I j ≤ P.asIdeal ∧
        P.asIdeal.comap (algebraMap A' (A' ⊗[A] C)) = ⊥) →
      ∃ P : PrimeSpectrum (A' ⊗[A] C), I i ⊔ I j ≤ P.asIdeal ∧
        PrimeSpectrum.comap (algebraMap A' (A' ⊗[A] C)) P = t := by
    by_cases h : ∃ P : PrimeSpectrum (A' ⊗[A] C), I i ⊔ I j ≤ P.asIdeal ∧
        P.asIdeal.comap (algebraMap A' (A' ⊗[A] C)) = ⊥
    · obtain ⟨c, hc, H⟩ := exists_ne_zero_forall_exists_comap_eq _ h
      exact ⟨c, hc, fun t ht _ ↦ H t ht⟩
    · exact ⟨1, one_ne_zero, fun _ _ h' ↦ absurd h' h⟩
  choose c hc0 hc using hmeet
  refine ⟨(∏ i, a i) * (∏ x ∈ T', b x) * ∏ p : ι × ι, c p.1 p.2, ?_, fun t ht ↦ ?_⟩
  · refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ha0 i)
      (Finset.prod_ne_zero_iff.mpr fun x hx ↦ hb0 x hx))
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦ hc0 p.1 p.2)
  simp only [t.2.mul_mem_iff_mem_or_mem, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and,
    not_or, not_exists, Prod.forall] at ht
  obtain ⟨⟨hta, htb⟩, htc⟩ := ht
  set k := t.asIdeal.ResidueField
  let W (i : ι) : Set (PrimeSpectrum (k ⊗[A'] (A' ⊗[A] C))) :=
    PrimeSpectrum.zeroLocus ((I i).map
      (Algebra.TensorProduct.includeRight : (A' ⊗[A] C) →ₐ[A'] k ⊗[A'] (A' ⊗[A] C)))
  refine preconnectedSpace_of_iUnion_eq_univ (W := W) (fun i ↦ ?_) ?_ fun U hU₁ hU₂ ↦ ?_
  · -- each piece is irreducible
    have := ha i t (hta i)
    let φ := Algebra.TensorProduct.map (AlgHom.id A' k) (Ideal.Quotient.mkₐ A' (I i))
    have hφ : Function.Surjective φ := Algebra.TensorProduct.map_surjective _ _
      Function.surjective_id (Ideal.Quotient.mkₐ_surjective A' (I i))
    have hW : Set.range
        (PrimeSpectrum.comap (S := k ⊗[A'] ((A' ⊗[A] C) ⧸ I i)) φ.toRingHom) = W i := by
      refine (range_comap_of_surjective (S := k ⊗[A'] ((A' ⊗[A] C) ⧸ I i)) φ.toRingHom
        hφ).trans ?_
      have hk : RingHom.ker φ.toRingHom = RingHom.ker φ := rfl
      have hk' : RingHom.ker (Ideal.Quotient.mkₐ A' (I i)) = I i := Ideal.Quotient.mkₐ_ker A' _
      rw [hk, Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective A' (I i)), hk']
    rw [← hW, ← Set.image_univ]
    exact IsPreirreducible.isPreconnected ((IrreducibleSpace.isIrreducible_univ _).image _
      (PrimeSpectrum.continuous_comap _).continuousOn).2
  · -- the pieces cover the fibre
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    set P₀ := x.asIdeal.comap
      (Algebra.TensorProduct.includeRight : (A' ⊗[A] C) →ₐ[A'] k ⊗[A'] (A' ⊗[A] C))
    have hP₀ : P₀.IsPrime := Ideal.comap_isPrime _ _
    have hbP (x' : A' ⊗[A] C) (hx' : x' ∈ T') : algebraMap A' (A' ⊗[A] C) (b x') ∉ P₀ := by
      rw [Ideal.mem_comap, AlgHom.commutes, IsScalarTower.algebraMap_apply A' k]
      refine fun h ↦ x.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        ((isUnit_iff_ne_zero.mpr ?_).map _))
      rw [Ne, Ideal.algebraMap_residueField_eq_zero]
      exact fun h ↦ htb x' ⟨hx', h⟩
    have hle : ∏ i, I i ≤ P₀ := by
      rw [← hT', Ideal.span_le]
      intro x' hx'
      have h0 : algebraMap A' (A' ⊗[A] C) (b x') * x' ^ m x' ∈ P₀ := by
        rw [← Algebra.smul_def, hbm x' hx']
        exact P₀.zero_mem
      exact hP₀.mem_of_pow_mem _ ((hP₀.mem_or_mem h0).resolve_left (hbP x' hx'))
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_le hP₀).mp hle
    exact ⟨i, (PrimeSpectrum.mem_zeroLocus _ _).mpr (Ideal.map_le_iff_le_comap.mpr hi)⟩
  · -- the pieces meet
    obtain ⟨i, hi, j, hj, hP⟩ := hU U hU₁ hU₂
    obtain ⟨P, hP, hPt⟩ := hc i j t (htc i j) hP
    set x := PrimeSpectrum.preimageEquivFiber A' (A' ⊗[A] C) t ⟨P, hPt⟩
    have hx : x.asIdeal.comap
        (Algebra.TensorProduct.includeRight : (A' ⊗[A] C) →ₐ[A'] k ⊗[A'] (A' ⊗[A] C)) =
        P.asIdeal := congrArg (fun y ↦ y.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber A' (A' ⊗[A] C) t).left_inv ⟨P, hPt⟩)
    have hxW (l : ι) (hl : I l ≤ P.asIdeal) : x ∈ W l :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr (Ideal.map_le_iff_le_comap.mpr (hx ▸ hl))
    exact ⟨i, hi, j, hj, x, hxW i (le_sup_left.trans hP), hxW j (le_sup_right.trans hP)⟩

set_option backward.isDefEq.respectTransparency false in
-- the tensor product with a quotient carries two semiring structures
/-- Let `A'` be an `A`-algebra mapping to a field `L` and `I` an ideal of `A' ⊗[A] C` whose
extension to `L ⊗[A] C` is prime. Then `Spec (L ⊗[A'] ((A' ⊗[A] C) ⧸ I))` is irreducible. -/
lemma irreducibleSpace_tensor_quotient {A A' C L : Type*} [CommRing A] [CommRing A']
    [CommRing C] [Field L] [Algebra A A'] [Algebra A C] [Algebra A' L] [Algebra A L]
    [IsScalarTower A A' L] (I : Ideal (A' ⊗[A] C))
    (hI : (I.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L)
      (AlgHom.id A C))).IsPrime) :
    IrreducibleSpace (PrimeSpectrum (L ⊗[A'] ((A' ⊗[A] C) ⧸ I))) := by
  set ι' := Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L) (AlgHom.id A C)
  let e := Algebra.TensorProduct.cancelBaseChange A A' L L C
  let φ := Algebra.TensorProduct.map (AlgHom.id A' L) (Ideal.Quotient.mkₐ A' I)
  have hφ : Function.Surjective φ := Algebra.TensorProduct.map_surjective _ _
    Function.surjective_id (Ideal.Quotient.mkₐ_surjective A' I)
  have hk : RingHom.ker φ.toRingHom = RingHom.ker φ := rfl
  have hk' : RingHom.ker (Ideal.Quotient.mkₐ A' I) = I := Ideal.Quotient.mkₐ_ker A' _
  have hcomp : (e.toRingEquiv : L ⊗[A'] (A' ⊗[A] C) →+* L ⊗[A] C).comp
      (Algebra.TensorProduct.includeRight : (A' ⊗[A] C) →ₐ[A'] L ⊗[A'] (A' ⊗[A] C)).toRingHom =
      ι'.toRingHom := by
    refine RingHom.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul a c => simp [e, ι', Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hmap : I.map ι' = (RingHom.ker φ.toRingHom).map
      (e.toRingEquiv : L ⊗[A'] (A' ⊗[A] C) →+* L ⊗[A] C) := by
    rw [hk, Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective A' I), hk']
    have : I.map ι' = I.map ι'.toRingHom := rfl
    rw [this, ← hcomp, ← Ideal.map_map]
    rfl
  let f := (RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ).symm.trans
    (Ideal.quotientEquiv _ (I.map ι') e.toRingEquiv hmap)
  refine GenericIrreducibility.irreducibleSpace_of_comap_surjective
    (R := L ⊗[A'] ((A' ⊗[A] C) ⧸ I)) (S := (L ⊗[A] C) ⧸ I.map ι') f.toRingHom fun x ↦
      ⟨PrimeSpectrum.comap f.symm.toRingHom x, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  ext y
  simp

/-- Preconnectedness of the spectrum descends along ring maps that are surjective on spectra. -/
lemma preconnectedSpace_of_comap_surjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective (PrimeSpectrum.comap f))
    [PreconnectedSpace (PrimeSpectrum S)] : PreconnectedSpace (PrimeSpectrum R) :=
  ⟨hf.range_eq ▸ isPreconnected_range (PrimeSpectrum.continuous_comap f)⟩

/-- Let `A ⊆ A'` be a finite type extension of domains with `A` noetherian. If the fibres of
`Spec (A' ⊗[A] C) → Spec A'` are preconnected over `D(a')`, `a' ≠ 0`, then the fibres of
`Spec C → Spec A` are preconnected over some `D(a)`, `a ≠ 0`. -/
lemma exists_ne_zero_forall_preconnectedSpace_of_injective {A A' C : Type*} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [CommRing A'] [IsDomain A'] [Algebra A A']
    [Algebra.FiniteType A A'] (hA : Function.Injective (algebraMap A A')) [CommRing C]
    [Algebra A C] {a' : A'} (ha' : a' ≠ 0)
    (h : ∀ t : PrimeSpectrum A', a' ∉ t.asIdeal →
      PreconnectedSpace (PrimeSpectrum (t.asIdeal.ResidueField ⊗[A'] (A' ⊗[A] C)))) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      PreconnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  set Z := PrimeSpectrum.comap (algebraMap A A') ''
    (PrimeSpectrum.basicOpen a' : Set (PrimeSpectrum A'))
  have hZ : Topology.IsConstructible Z := PrimeSpectrum.isConstructible_comap_image
    (RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance))
    PrimeSpectrum.isConstructible_basicOpen
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ Zᶜ := by
    rw [Set.notMem_compl_iff]
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hA)⟩
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    exact ha'
  obtain ⟨a, ha, hZa⟩ := BertiniNoether.exists_ne_zero_forall_mem_of_isConstructible hZ.compl hgen
  refine ⟨a, ha, fun p hp ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ : p ∈ Z := by
    by_contra h'
    exact hp (hZa p h')
  have := h t ht
  have : PreconnectedSpace (PrimeSpectrum (t.asIdeal.ResidueField ⊗[A] C)) :=
    preconnectedSpace_of_comap_surjective (Algebra.TensorProduct.cancelBaseChange A A'
      t.asIdeal.ResidueField t.asIdeal.ResidueField C).symm.toRingHom
      (PrimeSpectrum.comapEquiv _).surjective
  let : Algebra (PrimeSpectrum.comap (algebraMap A A') t).asIdeal.ResidueField
      t.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ t.asIdeal (algebraMap A A') rfl).toAlgebra
  have : IsScalarTower A (PrimeSpectrum.comap (algebraMap A A') t).asIdeal.ResidueField
      t.asIdeal.ResidueField := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply A A' t.asIdeal.ResidueField x).trans
      (Ideal.ResidueField.map_algebraMap _ t.asIdeal (algebraMap A A') rfl x).symm
  exact preconnectedSpace_of_comap_surjective _
    (GenericIrreducibility.comap_surjective_map_tensor_of_field (k' := t.asIdeal.ResidueField))

/-- **Generic preconnectedness of fibres.** Let `A` be a noetherian domain with fraction field
`K`, `L` an algebraically closed extension of `K` and `C` a finite type `A`-algebra such that
`Spec (L ⊗[A] C)` is preconnected. Then there is `a ≠ 0` in `A` such that the fibres
`Spec (κ(p) ⊗[A] C)` over all primes `p ∌ a` are preconnected. -/
theorem exists_ne_zero_forall_preconnectedSpace_fiber {A C : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C] (K L : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [IsAlgClosed L] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] (hC : PreconnectedSpace (PrimeSpectrum (L ⊗[A] C))) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      PreconnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  classical
  have : IsNoetherianRing (L ⊗[A] C) := Algebra.FiniteType.isNoetherianRing L _
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let ι := minimalPrimes (L ⊗[A] C)
  have : Fintype ι := (minimalPrimes.finite_of_isNoetherianRing _).fintype
  have hprime (Q : ι) : Q.1.IsPrime := Q.2.isPrime
  have hcover (P : PrimeSpectrum (L ⊗[A] C)) : ∃ Q : ι, Q.1 ≤ P.asIdeal := by
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ P.asIdeal)
    exact ⟨⟨Q, hQ⟩, hle⟩
  -- a finitely generated `A`-subalgebra of `L` over which the minimal primes are defined
  choose G hG using fun Q : ι ↦ (IsNoetherian.noetherian Q.1 : Q.1.FG)
  choose Sexp hSexp using fun y : L ⊗[A] C ↦ TensorProduct.exists_finset y
  let T : Finset L := Finset.univ.biUnion fun Q ↦ (G Q).biUnion fun y ↦ (Sexp y).image Prod.fst
  obtain ⟨A', hA'⟩ : ∃ A' : Subalgebra A L, A' = Algebra.adjoin A (T : Set L) := ⟨_, rfl⟩
  have hTA' : (T : Set L) ⊆ A' := hA' ▸ Algebra.subset_adjoin
  have : Algebra.FiniteType A A' :=
    (Subalgebra.fg_iff_finiteType _).mp (hA' ▸ Subalgebra.fg_adjoin_finset T)
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  have hA'L : Function.Injective (algebraMap A' L) := Subtype.val_injective
  set ι' := Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L) (AlgHom.id A C)
  have hlift (Q : ι) (y : L ⊗[A] C) (hy : y ∈ G Q) : ∃ y' : A' ⊗[A] C, ι' y' = y := by
    have hyT : (Sexp y).image Prod.fst ⊆ T := fun l hl ↦ Finset.mem_biUnion.mpr
      ⟨Q, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨y, hy, hl⟩⟩
    refine ⟨∑ i ∈ (Sexp y).attach,
      (⟨i.1.1, hTA' (hyT (Finset.mem_image_of_mem _ i.2))⟩ : A') ⊗ₜ i.1.2, ?_⟩
    calc _ = ∑ i ∈ (Sexp y).attach, i.1.1 ⊗ₜ[A] i.1.2 := by
          rw [map_sum]
          rfl
      _ = ∑ i ∈ Sexp y, i.1 ⊗ₜ[A] i.2 :=
        Finset.sum_attach _ (fun i : L × C ↦ i.1 ⊗ₜ[A] i.2)
      _ = y := (hSexp y).symm
  choose! y' hy' using hlift
  let I (Q : ι) : Ideal (A' ⊗[A] C) := Ideal.span (y' Q '' G Q)
  have hmap (Q : ι) : (I Q).map ι' = Q.1 := by
    rw [Ideal.map_span, Set.image_image, Set.image_congr (hy' Q), Set.image_id', ← hG Q]
  have hA : Function.Injective (algebraMap A A') := fun x y h ↦ hAL (by
    rw [IsScalarTower.algebraMap_apply A A' L x, h, ← IsScalarTower.algebraMap_apply])
  -- the minimal primes cover `Spec (L ⊗[A] C)`
  have hnil (x : A' ⊗[A] C) (hx : x ∈ ∏ Q, I Q) : IsNilpotent (ι' x) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    obtain ⟨Q, hQ⟩ := hcover ⟨J, hJ⟩
    have hxQ : x ∈ I Q := (Finset.inf_le (f := I) (Finset.mem_univ Q)) (Ideal.prod_le_inf hx)
    exact hQ (hmap Q ▸ Ideal.mem_map_of_mem ι' hxQ)
  -- the minimal primes form a connected configuration
  have hU (U : Set ι) (hU₁ : U.Nonempty) (hU₂ : Uᶜ.Nonempty) : ∃ i ∈ U, ∃ j ∉ U,
      ∃ P : PrimeSpectrum (A' ⊗[A] C),
        I i ⊔ I j ≤ P.asIdeal ∧ P.asIdeal.comap (algebraMap A' (A' ⊗[A] C)) = ⊥ := by
    obtain ⟨Q₁, hQ₁, Q₂, hQ₂, P, hP₁, hP₂⟩ := exists_inter_nonempty_of_preconnectedSpace
      (W := fun Q : ι ↦ PrimeSpectrum.zeroLocus (Q.1 : Set (L ⊗[A] C)))
      (fun Q ↦ PrimeSpectrum.isClosed_zeroLocus _) (fun Q ↦ ⟨⟨Q.1, hprime Q⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr subset_rfl⟩)
      (Set.eq_univ_of_forall fun P ↦ Set.mem_iUnion.mpr ((hcover P).imp fun Q hQ ↦
        (PrimeSpectrum.mem_zeroLocus _ _).mpr hQ)) hU₁ hU₂
    refine ⟨Q₁, hQ₁, Q₂, hQ₂, PrimeSpectrum.comap ι'.toRingHom P,
      sup_le (Ideal.map_le_iff_le_comap.mp ((hmap Q₁).le.trans hP₁))
        (Ideal.map_le_iff_le_comap.mp ((hmap Q₂).le.trans hP₂)), ?_⟩
    ext x
    have hx : ι' (algebraMap A' (A' ⊗[A] C) x) =
        algebraMap L (L ⊗[A] C) (algebraMap A' L x) := by
      simp [ι', Algebra.TensorProduct.algebraMap_apply]
    rw [Ideal.mem_comap, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hx, Ideal.mem_bot]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_contra hx0
      exact P.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        ((isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hA'L).mpr hx0)).map _))
    · rw [h, map_zero, map_zero]
      exact zero_mem _
  obtain ⟨a', ha', H⟩ := exists_ne_zero_forall_preconnectedSpace_of_cover (A := A) (A' := A')
    (C := C) L hA'L I (fun Q ↦ irreducibleSpace_tensor_quotient _ (by
      rw [hmap Q]
      exact hprime Q)) hnil hU
  exact exists_ne_zero_forall_preconnectedSpace_of_injective hA ha' H

end GenericConnectedness

open GenericConnectedness in
/-- **Generic connectedness of fibres** (ring-theoretic form of Stacks `055G`). Let `A` be a
noetherian domain with fraction field `K` and `C` a finite type `A`-algebra with an `A`-valued
point `s` such that the generic fibre `Spec (K ⊗[A] C)` is connected. Then there is `a ≠ 0` in
`A` such that the fibres `Spec (κ(p) ⊗[A] C)` over all primes `p ∌ a` are connected. -/
@[stacks 055G]
theorem exists_ne_zero_forall_connectedSpace_fiber {A C : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C] (K : Type u)
    [Field K] [Algebra A K] [IsFractionRing A K] (s : C →ₐ[A] A)
    (hC : ConnectedSpace (PrimeSpectrum (K ⊗[A] C))) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  have hL := connectedSpace_tensor_of_section (L := AlgebraicClosure K) s hC
  obtain ⟨a, ha, H⟩ := exists_ne_zero_forall_preconnectedSpace_fiber K (AlgebraicClosure K)
    hL.toPreconnectedSpace
  refine ⟨a, ha, fun p hp ↦ ?_⟩
  have := H p hp
  let σ : p.asIdeal.ResidueField ⊗[A] C →ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ((Algebra.ofId A _).comp s) fun _ _ ↦ .all _ _
  have : Nontrivial (p.asIdeal.ResidueField ⊗[A] C) := RingHom.domain_nontrivial σ.toRingHom
  exact ConnectedSpace.mk inferInstance
