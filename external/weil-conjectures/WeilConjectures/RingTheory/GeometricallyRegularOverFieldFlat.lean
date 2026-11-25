/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.FlatOverRegular
import WeilConjectures.RingTheory.DifferentialCoordinatesCotangentIndependent
import WeilConjectures.RingTheory.GeometricallyRegularH1Injective
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.Mathlib.Algebra.Module.SpanRankOperations

/-!
# Flatness over a polynomial localization from a differential basis

Source: Stacks Project, More on Algebra, Lemma 07E6 and its proof
(blueprint: lem-weil-pbc-geometrically-regular-over-field-flat).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem extend_parameters_of_cotangent_independence
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (ψ : R →+* S) [IsLocalHom ψ]
    (hpres : ∀ s : Set (IsLocalRing.maximalIdeal R),
      LinearIndepOn (IsLocalRing.ResidueField R)
        (IsLocalRing.maximalIdeal R).toCotangent s →
      LinearIndepOn (IsLocalRing.ResidueField S)
        (fun x : IsLocalRing.maximalIdeal R ↦ (IsLocalRing.maximalIdeal S).toCotangent
          ⟨ψ x, map_nonunit ψ x x.2⟩) s) :
    ∃ (x : List R) (y : List S),
      IsLocalRing.IsRegularSystemOfParameters x ∧
      IsLocalRing.IsRegularSystemOfParameters (x.map ψ ++ y) := by
  classical
  let mR := IsLocalRing.maximalIdeal R
  let mS := IsLocalRing.maximalIdeal S
  obtain ⟨s, -, -, hs_span, hs⟩ := exists_linearIndepOn_extension
    (v := mR.toCotangent) (linearIndepOn_empty (IsLocalRing.ResidueField R) _)
    (Set.empty_subset (Set.univ : Set mR))
  have hspanR : Submodule.span (IsLocalRing.ResidueField R) (mR.toCotangent '' s) = ⊤ := by
    apply top_unique
    rintro v -
    obtain ⟨z, rfl⟩ := mR.toCotangent_surjective v
    exact hs_span ⟨z, trivial, rfl⟩
  have : Finite s := LinearIndependent.finite_of_isNoetherian hs
  have hsfin : s.Finite := Set.toFinite s
  have hRcard : (s.ncard : WithBot ℕ∞) = ringKrullDim R := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_ncard hsfin hs hspanR]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal
  have hgenR : Ideal.span (Subtype.val '' s) = mR := by
    have ht : Submodule.span R s = ⊤ :=
      IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hspanR
    change Submodule.span R (mR.subtype '' s) = mR
    rw [Submodule.span_image, ht, Submodule.map_top, Submodule.range_subtype]
  let f : mR → mS := fun z ↦ ⟨ψ z, map_nonunit ψ z z.2⟩
  have hsS : LinearIndepOn (IsLocalRing.ResidueField S) (mS.toCotangent ∘ f) s :=
    hpres s hs
  have hf : Set.InjOn f s := by
    intro z hz w hw hzw
    exact hsS.injOn hz hw (congrArg mS.toCotangent hzw)
  let t := f '' s
  have ht : LinearIndepOn (IsLocalRing.ResidueField S) mS.toCotangent t :=
    (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s hf) rfl).mp hsS
  obtain ⟨b, -, htb, hb_span, hb⟩ :=
    exists_linearIndepOn_extension ht (Set.subset_univ t)
  have hspanS : Submodule.span (IsLocalRing.ResidueField S) (mS.toCotangent '' b) = ⊤ := by
    apply top_unique
    rintro v -
    obtain ⟨z, rfl⟩ := mS.toCotangent_surjective v
    exact hb_span ⟨z, trivial, rfl⟩
  have : Finite b := LinearIndependent.finite_of_isNoetherian hb
  have hbfin : b.Finite := Set.toFinite b
  have hbcard : (b.ncard : WithBot ℕ∞) = ringKrullDim S := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_ncard hbfin hb hspanS]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal
  have hgenS : Ideal.span (Subtype.val '' b) = mS := by
    have ht : Submodule.span S b = ⊤ :=
      IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hspanS
    change Submodule.span S (mS.subtype '' b) = mS
    rw [Submodule.span_image, ht, Submodule.map_top, Submodule.range_subtype]
  let x : List R := hsfin.toFinset.toList.map Subtype.val
  let y : List S := (hbfin.sdiff (t := t)).toFinset.toList.map Subtype.val
  have hxmem : {z | z ∈ x} = Subtype.val '' s := by
    ext z
    simp only [x, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, Set.mem_image]
  have hymem : {z | z ∈ y} = Subtype.val '' (b \ t) := by
    ext z
    simp only [y, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, Set.mem_image]
  have hfirst : {z | z ∈ x.map ψ} = Subtype.val '' t := by
    ext z
    simp only [x, List.map_map, List.mem_map, Finset.mem_toList,
      Set.Finite.mem_toFinset, Set.mem_ofPred_eq, t, Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨f w, ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
  have hmem : {z | z ∈ x.map ψ ++ y} = Subtype.val '' b := by
    calc
      {z | z ∈ x.map ψ ++ y} = {z | z ∈ x.map ψ} ∪ {z | z ∈ y} := by
        ext z
        simp only [Set.mem_ofPred_eq, List.mem_append, Set.mem_union]
      _ = Subtype.val '' (t ∪ (b \ t)) := by rw [hfirst, hymem, Set.image_union]
      _ = Subtype.val '' b := by
        congr 1
        ext z
        simp only [Set.mem_union, Set.mem_sdiff]
        exact ⟨fun h ↦ h.elim (fun hz ↦ htb hz) And.left,
          fun hz ↦ (em (z ∈ t)).elim Or.inl (fun ht ↦ Or.inr ⟨hz, ht⟩)⟩
  have htcard : t.ncard = s.ncard := hf.ncard_image
  have hlenR : x.length = s.ncard := by
    simp only [x, List.length_map, Finset.length_toList, ← Set.ncard_eq_toFinset_card s hsfin]
  have hlenS : (x.map ψ ++ y).length = b.ncard := by
    simp only [List.length_append, List.length_map, hlenR, y, Finset.length_toList]
    rw [← Set.ncard_eq_toFinset_card (b \ t) hbfin.sdiff, ← htcard, Nat.add_comm,
      Set.ncard_sdiff_add_ncard_of_subset htb hbfin]
  exact ⟨x, y, ⟨hxmem ▸ hgenR, by rw [hlenR]; exact hRcard⟩,
    ⟨hmem ▸ hgenS, by rw [hlenS]; exact hbcard⟩⟩

/-- A differential basis in a finitely generated residue subfield gives a flat polynomial
localization map and a regular local closed fibre. Source: Stacks Project, More on Algebra,
Lemma 07E6 (blueprint: lem-weil-pbc-geometrically-regular-over-field-flat).

Proof: Construct the local map from the polynomial localization with `IsLocalization.lift`.
The unit criterion for fractions proves that it is local. Mathlib's polynomial regular-ring
instance and the proved localization instance give regularity of the source; Proposition
07E5 gives regularity of `A` (lem-weil-pbc-geometrically-regular-h1-injective).
The differential comparison and the commutative H₁/cotangent square are isolated in
`linearIndepOn_of_residue_differential_basis`
(lem-weil-pbc-differential-coordinates-cotangent-independent).
The proved private helper `extend_parameters_of_cotangent_independence` lifts a finite
cotangent basis in the source, extends its independent image to a cotangent basis in `A`,
and applies Nakayama to obtain parameter lists `x` and `x.map ψ ++ y`. Regularity identifies
their lengths with the respective Krull dimensions. Lemma 00NQ supplies regularity of the
image prefix and of its quotient (lem-weil-pbc-regular-local-generators-regular-sequence).
Lemma 07DY then gives flatness (lem-weil-pbc-flat-over-regular). Finally, the restriction
equation for the localization lift identifies `p.map φ` with the ideal generated by the
image prefix, so its quotient is exactly the regular local quotient already proved. -/
theorem exists_flat_polynomialLocalization_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (pchar : ℕ) [Fact pchar.Prime] [CharP k pchar]
    (hreg : IsGeometricallyRegular k A)
    (F : IntermediateField k (IsLocalRing.ResidueField A)) (hF : F.FG)
    (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] A)
    (a : Fin m → F)
    (ha : ∀ i : Fin m, (a i : IsLocalRing.ResidueField A) =
      IsLocalRing.residue A (φ (MvPolynomial.X i)))
    (b : Module.Basis (Fin m) F (KaehlerDifferential k F))
    (hb : ∀ i : Fin m, b i = KaehlerDifferential.D k F (a i)) :
    let p := (IsLocalRing.maximalIdeal A).comap φ.toRingHom
    ∃ ψ : Localization.AtPrime p →+* A,
      ψ.comp (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime p)) = φ.toRingHom ∧
      ψ.Flat ∧ IsRegularLocalRing (A ⧸ p.map φ.toRingHom) := by
  let p := (IsLocalRing.maximalIdeal A).comap φ.toRingHom
  let R₀ := Localization.AtPrime p
  have hu : ∀ s : p.primeCompl, IsUnit (φ.toRingHom s) := by
    intro s
    exact not_not.mp s.2
  let ψ : R₀ →+* A := IsLocalization.lift (S := R₀) hu
  have hψ : ψ.comp (algebraMap (MvPolynomial (Fin m) k) R₀) = φ.toRingHom :=
    IsLocalization.lift_comp hu
  have hlocal : IsLocalHom ψ := by
    constructor
    intro z hz
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    have hr : IsUnit (φ.toRingHom r) := by
      have he := IsLocalization.mk'_spec R₀ r s
      have hm := congrArg ψ he
      rw [map_mul] at hm
      have heq : ψ (algebraMap (MvPolynomial (Fin m) k) R₀ r) = φ.toRingHom r :=
        DFunLike.congr_fun hψ r
      rw [heq] at hm
      exact hm ▸ (hz.mul (ψ.isUnit_map (IsLocalization.map_units R₀ s)))
    exact (IsLocalization.AtPrime.isUnit_mk'_iff R₀ p r s).mpr (fun hn ↦ hn hr)
  let := hlocal
  let : IsRegularLocalRing R₀ := inferInstance
  let : IsRegularLocalRing A :=
    (isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular
      k A pchar hreg).1
  have hpres :=
    linearIndepOn_of_residue_differential_basis k A pchar hreg F hF m φ a ha b hb ψ hψ
  obtain ⟨x, y, hx, hxy⟩ := extend_parameters_of_cotangent_independence ψ hpres
  have hdim₀ : ringKrullDim R₀ = (x.length : WithBot ℕ∞) := hx.2.symm
  have hdim : ringKrullDim A = ((x.map ψ ++ y).length : WithBot ℕ∞) := hxy.2.symm
  have hseq := IsRegularLocalRing.isRegular_and_quotients_of_generators
    A (x.map ψ ++ y).length hdim (x.map ψ ++ y) hxy
  have hweak : RingTheory.Sequence.IsWeaklyRegular A (x.map ψ) :=
    ((RingTheory.Sequence.isWeaklyRegular_append_iff A (x.map ψ) y).mp
      hseq.1.toIsWeaklyRegular).1
  have hregular : RingTheory.Sequence.IsRegular A (x.map ψ) :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A
      (fun r hr ↦ hxy.1 ▸ Ideal.subset_span (List.mem_append_left y hr)) hweak
  have hflat : ψ.Flat :=
    RingHom.flat_of_regular_parameters ψ x.length x hdim₀ rfl hx.1 hregular
  have hquot := (hseq.2.1 x.length (by simp)).1
  have hideal : p.map φ.toRingHom = Ideal.ofList ((x.map ψ ++ y).take x.length) := by
    calc
      p.map φ.toRingHom = p.map (ψ.comp (algebraMap (MvPolynomial (Fin m) k) R₀)) :=
        congrArg (fun f ↦ p.map f) hψ.symm
      _ = (IsLocalRing.maximalIdeal R₀).map ψ := by
        rw [← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
      _ = Ideal.ofList (x.map ψ) := by rw [← hx.1, Ideal.map_ofList]
      _ = Ideal.ofList ((x.map ψ ++ y).take x.length) := by
        rw [← List.length_map (f := ψ) (as := x), List.take_left]
  refine ⟨ψ, hψ, hflat, ?_⟩
  rwa [← hideal] at hquot

end Algebra
