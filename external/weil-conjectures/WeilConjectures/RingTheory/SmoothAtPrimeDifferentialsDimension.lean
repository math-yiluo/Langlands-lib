/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Dimension of differentials at a smooth point over a field

Source: Stacks Project, Algebra, Lemma 00TT, implication (1) implies (3)
(blueprint: lem-weil-pbc-smooth-over-field-dimension-differentials).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Open embeddings preserve local dimension: inverse images give neighbourhoods in the
source, and open images give neighbourhoods in the target with the same dimension. -/
private theorem dimAt_openEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  apply le_antisymm
  · refine le_iInf₂ fun U hU ↦ ?_
    let V : TopologicalSpace.Opens X :=
      ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩
    refine (iInf₂_le V hU).trans ?_
    let g : V → U := fun z ↦ ⟨f z, z.2⟩
    have hg : Topology.IsInducing g :=
      .of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val
        (hf.toIsEmbedding.toIsInducing.comp Topology.IsInducing.subtypeVal)
    exact hg.topologicalKrullDim_le
  · refine le_iInf₂ fun U hU ↦ ?_
    let V : TopologicalSpace.Opens Y := ⟨f '' U, hf.isOpenMap _ U.isOpen⟩
    refine (iInf₂_le V ⟨x, hU, rfl⟩).trans ?_
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (hf.toIsEmbedding.homeomorphImage (U : Set X)).symm.isHomeomorph).le

/-- Reindex the variables of a submersive presentation with its Jacobian variables first.
The remaining variables are the complement of the injective relation-variable map. -/
private theorem normalized_presentation {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsStandardSmooth R B] :
    ∃ (n c : ℕ) (hnc : c ≤ n) (P : SubmersivePresentation R B (Fin n) (Fin c)),
      P.map = Fin.castLE hnc := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := IsStandardSmooth.out (R := R) (S := B)
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  let τ := ((Set.range P.map)ᶜ : Set ι)
  let f := (Fintype.equivFin σ).symm
  let e : Fin (Fintype.card σ + Fintype.card τ) ≃ ι :=
    finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (f.trans (Equiv.ofInjective P.map P.map_inj))
        (Fintype.equivFin τ).symm).trans (Equiv.Set.sumCompl (Set.range P.map)))
  let hnc : Fintype.card σ ≤ Fintype.card σ + Fintype.card τ := Nat.le_add_right _ _
  refine ⟨_, _, hnc, P.reindex e f, ?_⟩
  funext i
  change e.symm (P.map (f i)) = Fin.castLE hnc i
  apply e.injective
  rw [e.apply_symm_apply]
  have hc : Fin.castLE hnc i = Fin.castAdd (Fintype.card τ) i := rfl
  rw [hc]
  simp [e]
  rfl

/-- At a smooth prime of a finite type algebra over a field, the fibre of the module of
Kähler differentials is finite-dimensional, with dimension equal to the topological
Krull dimension at that point. Scalar extension places the residue field on the left;
the tensor-product commutor identifies this with `Ω[S⁄k] ⊗[S] κ(q)`.
Source: Stacks Project, Algebra, Lemma 00TT, implication (1) implies (3)
(blueprint: lem-weil-pbc-smooth-over-field-dimension-differentials).

Proof:
1. A finite type algebra over a field is finitely presented. The smooth principal
   neighbourhood in `IsSmoothAtPrime` puts `q` in Mathlib's smooth locus. Apply
   `IsSmoothAt.exists_notMem_isStandardSmooth` to obtain `f ∉ q` and a standard smooth
   presentation of `B = S_f`. Reindex its variables as the disjoint union of the
   Jacobian variables and their complement, obtaining `Fin n`, `Fin c` and the map
   `Fin.castLE hnc` required by the standard smooth dimension theorem.
2. Write `K = κ(q)`. Since the image of `f` in `K` is nonzero, the residue map extends
   to `B`. Let `Q` be the inverse image of the zero prime of `K`. The scalar-tower
   identity and the kernel of the original residue map show that `Q` maps to `q`.
   The spectrum map for a principal localization is an open embedding, hence preserves
   dimension at a point. The standard smooth dimension theorem gives `dim_q Spec S = n-c`.
3. Localization is formally étale, so Mathlib's differential base-change equivalence
   identifies `Ω[B⁄k]` with `B ⊗[S] Ω[S⁄k]`. Extend this equivalence to `K` and cancel
   the intermediate base change to identify the two differential fibres. Base change
   the basis `P.basisKaehler` to `K` and carry it across this equivalence.
4. The resulting basis of `K ⊗[S] Ω[S⁄k]` has finite index type, giving finite
   dimensionality. Its cardinality is the number of variables minus the cardinality
   of the range of the injective relation-variable map, namely `n-c`. Comparing this
   finrank with step 2 proves the required equality. -/
theorem finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S) (h : IsSmoothAtPrime k q) :
    FiniteDimensional q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) ∧
    (Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) : WithBot ℕ∞) =
        topologicalKrullDimAt q := by
  classical
  have : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨u, hu, hsm⟩ := h
  have hloc : PrimeSpectrum.basicOpen u ≤ smoothLocus k S :=
    (basicOpen_subset_smoothLocus_iff_smooth (R := k) (f := u)).mpr hsm
  have : IsSmoothAt k q.asIdeal := hloc hu
  obtain ⟨f, hf, hstd⟩ := IsSmoothAt.exists_notMem_isStandardSmooth k q.asIdeal
  have := hstd
  obtain ⟨n, c, hnc, P, hmap⟩ := normalized_presentation (R := k)
    (B := Localization.Away f)
  let B := Localization.Away f
  let K := q.asIdeal.ResidueField
  have hunit : IsUnit (algebraMap S K f) := by
    apply isUnit_iff_ne_zero.mpr
    exact fun hz ↦ hf ((Ideal.algebraMap_residueField_eq_zero (I := q.asIdeal)).mp hz)
  let φ : B →ₐ[S] K := IsLocalization.Away.liftAlgHom f
    (f := Algebra.ofId S K) hunit
  let : Algebra B K := φ.toRingHom.toAlgebra
  have : IsScalarTower S B K := IsScalarTower.of_algebraMap_eq'
    φ.comp_algebraMap.symm
  let Q : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B K)
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hQ : PrimeSpectrum.comap (algebraMap S B) Q = q := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap S B)
      (Ideal.comap (algebraMap B K) ⊥) = q.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq S B K]
    exact Ideal.ker_algebraMap_residueField q.asIdeal
  have hdim : topologicalKrullDimAt q = (n - c : ℕ) := by
    rw [← hQ, ← dimAt_openEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding B f) Q]
    exact P.topologicalKrullDimAt_spec_eq hnc hmap Q
  have : FormallyEtale S B := FormallyEtale.of_isLocalization (.powers f)
  let e : (K ⊗[B] KaehlerDifferential k B) ≃ₗ[K]
      (K ⊗[S] KaehlerDifferential k S) :=
    LinearEquiv.baseChange B K _ _
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S B).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange S B K K _
  let b := (P.basisKaehler.baseChange K).map e
  have hfin : FiniteDimensional K (K ⊗[S] KaehlerDifferential k S) :=
    Module.Finite.of_basis b
  refine ⟨hfin, ?_⟩
  rw [hdim]
  change (Module.finrank K (K ⊗[S] KaehlerDifferential k S) : WithBot ℕ∞) = _
  congr 1
  rw [Module.finrank_eq_card_basis b, Fintype.card_compl_set,
    Set.card_range_of_injective P.map_inj]
  simp

end Algebra
