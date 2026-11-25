/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeFiniteCover

/-!
# Lattices of lisse `E`-sheaves on regular schemes

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `S`
a connected regular Noetherian scheme. Every lisse (locally free) `E_S`-module `L` has a lattice:
there is a locally free `𝒪_{E,S}`-module `L₀` with `E_S ⊗_{𝒪_{E,S}} L₀ ≅ L`
(`AlgebraicGeometry.ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso`, blueprint
`lemma-lattices-after-finite-stratification`, first stage).

The proof:

* `L` is trivialised on a finite pro-étale cover by affine schemes
  (`ProEtale.CondensedRing.exists_finite_affine_cover_isFree_upperStar`), with a single rank, `S`
  being connected (`AlgebraicGeometry.ProEtale.rank_eq_of_comp_eq`);
* the values of the transition matrices of the trivialisations form a continuous `GL_n(E)`-valued
  cocycle (`AlgebraicGeometry.ProEtale.exists_transitionValues`);
* on the regular scheme `S`, the cocycle is conjugate to a `GL_n(𝒪_E)`-valued one by a lattice-
  valued twisted section (`AlgebraicGeometry.exists_integral_conj_of_transitionValues`, from the
  lattice theorem `AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice`);
* the trivialisations changed accordingly have integral transition matrices, so the lattices
  spanned by the bases glue to `L₀`
  (`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- Every module object over a ring object on the pro-étale site of an empty scheme is zero: the
sections of a sheaf over every object, an empty scheme, are terminal. -/
lemma isZero_mod_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    {R : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) : IsZero M := by
  have hX : IsZero M.X := by
    refine (IsZero.iff_id_eq_zero _).2 (Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_)))
    have : IsEmpty T.unop.left := ⟨fun x ↦ isEmptyElim (α := X) (T.unop.hom.base x)⟩
    exact (ProEt.isTerminalSectionsOfIsEmpty M.X T.unop).hom_ext _ _
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext : 1
  exact hX.eq_of_src _ _

/-- **Lisse `E`-sheaves on connected regular Noetherian schemes have lattices** (blueprint
`lemma-lattices-after-finite-stratification`, first stage). See the module docstring. -/
theorem exists_isLocallyFree_padicIntegers_extendScalars_iso {S : Scheme.{u}} [IsNoetherian S]
    [IsRegular S] [ConnectedSpace S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) S))
    (hL : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E.1) S) L) :
    ∃ L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S) L₀ ∧
        Nonempty ((Mod.extendScalars (padicIntegersToPadicSubfield S ℓ E)).obj L₀ ≅ L) := by
  classical
  obtain ⟨𝒰, h𝒰, haff, hfree⟩ := CondensedRing.exists_finite_affine_cover_isFree_upperStar hL
  choose n e using hfree
  let e' (k : 𝒰.I₀) := (e k).some.symm
  have hsurj : ∀ s : S, ∃ k v, (𝒰.f k).base v = s :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ 𝒰.mem₀)).1
  -- the ranks agree at points with the same image
  have hn (j k : 𝒰.I₀) (v : 𝒰.X j) (v' : 𝒰.X k) (hvv' : (𝒰.f j).base v = (𝒰.f k).base v') :
      n j = n k := by
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f j) (g := 𝒰.f k) v v'
      hvv'
    exact rank_eq_of_comp_eq (e' j) (e' k) (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition w
  -- the rank is constant, `S` being connected
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨k₀, v₀, -⟩ := hsurj s₀
  let A (m : ℕ) : Set S := {s | ∃ k, ∃ v : 𝒰.X k, (𝒰.f k).base v = s ∧ n k = m}
  have hpre (m : ℕ) (j : 𝒰.I₀) : (𝒰.f j).base ⁻¹' A m = if n j = m then Set.univ else ∅ := by
    ext v
    simp only [Set.mem_preimage, A, Set.mem_ofPred_eq]
    split_ifs with h
    · exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨j, v, rfl, h⟩⟩
    · exact ⟨fun ⟨i, v', hv', hi⟩ ↦ h ((hn j i v v' hv'.symm).trans hi), fun h ↦ h.elim⟩
  have hopen (m : ℕ) : IsOpen (A m) :=
    Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage 𝒰.f 𝒰.mem₀ _ fun j ↦ by
      rw [hpre]
      split_ifs <;> simp
  have hA : A (n k₀) = Set.univ := by
    refine IsClopen.eq_univ ⟨?_, hopen _⟩ ⟨(𝒰.f k₀).base v₀, k₀, v₀, rfl, rfl⟩
    have : (A (n k₀))ᶜ = ⋃ m ∈ ({n k₀}ᶜ : Set ℕ), A m := by
      ext s
      obtain ⟨i, v, rfl⟩ := hsurj s
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, A,
        Set.mem_ofPred_eq]
      constructor
      · exact fun h ↦ ⟨n i, fun h' ↦ h ⟨i, v, rfl, h'⟩, i, v, rfl, rfl⟩
      · rintro ⟨m, hm, i', v', hv', rfl⟩ ⟨i'', v'', hv'', h''⟩
        exact hm ((hn i' i'' v' v'' (hv'.trans hv''.symm)).trans h'')
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun m _ ↦ hopen m
  have hrank (k : 𝒰.I₀) (v : 𝒰.X k) : n k = n k₀ := by
    obtain ⟨i', v', hv', h'⟩ : (𝒰.f k).base v ∈ A (n k₀) := by
      rw [hA]
      trivial
    exact (hn k i' v v' hv'.symm).trans h'
  -- trivialisations of a single rank
  have he (k : 𝒰.I₀) : Nonempty (Mod.finiteFree
      (condensedRingObj (Profinite.continuousMapRingObj E.1) (𝒰.X k)) (n k₀) ≅
        (𝒰.f k)^*⟦Profinite.continuousMapRingObj E.1⟧.obj L) := by
    by_cases hk : Nonempty (𝒰.X k)
    · obtain ⟨v⟩ := hk
      rw [← hrank k v]
      exact ⟨e' k⟩
    · have : IsEmpty (𝒰.X k) := not_nonempty_iff.1 hk
      exact ⟨(isZero_mod_of_isEmpty _).iso (isZero_mod_of_isEmpty _)⟩
  have : Finite 𝒰.I₀ := h𝒰
  obtain ⟨Tval, hc, hc', hcomp, htrans, hself, hdesc⟩ :=
    exists_transitionValues L 𝒰 fun k ↦ (he k).some
  obtain ⟨g, hg, hg', hint₁, hint₂⟩ :=
    exists_integral_conj_of_transitionValues 𝒰 Tval hc hc' hcomp htrans hself
  exact hdesc g hg hg' hint₁ hint₂

end AlgebraicGeometry.ProEtale
