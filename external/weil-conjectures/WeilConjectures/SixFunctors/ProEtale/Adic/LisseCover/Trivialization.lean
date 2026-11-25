/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# A lisse sheaf is trivialised on a single affine pro-étale cover

Let `Y` be a connected quasi-compact quasi-separated scheme and `G` a lisse `ℓ`-adic sheaf on
`Y_proét`. Then there is a single weakly étale, surjective and quasi-compact morphism
`f : V ⟶ Y` from an affine scheme `V` with `f^* G ≅ ℚ̄_ℓ,Vⁿ` for some `n`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_affine_cover_iso`): a trivialising
pro-étale cover is refined by finitely many affine opens of its members, their disjoint union is
affine, and the ranks of the trivialisations agree, being locally constant on the connected `Y`
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- Two sheaves on an empty scheme are isomorphic. -/
noncomputable def isoOfIsEmpty {T : Scheme.{u}} [IsEmpty T] (M N : AdicSheaf l T) : M ≅ N :=
  (isZero_adicSheaf_of_isEmpty l M).iso (isZero_adicSheaf_of_isEmpty l N)

/-- **Trivialisations on a finite disjoint union.** If `U_s^* M ≅ ℚ̄_ℓⁿ` on every summand of a
finite disjoint union `∐_s U_s`, then `M ≅ ℚ̄_ℓⁿ`: both are the products of the pushforwards
of their restrictions to the summands
(`AlgebraicGeometry.ProEtale.isIso_pi_lift_adicUpperStarLowerStarAdjunction_unit`). -/
lemma nonempty_iso_of_sigma {S : Type u} [Finite S] (U : S → Scheme.{u}) {M : AdicSheaf l (∐ U)}
    {n : ℕ} (e : ∀ s, (Sigma.ι U s)^*ᵃ[l].obj M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U s)) :
    Nonempty (M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (∐ U)) := by
  have hM := isIso_pi_lift_adicUpperStarLowerStarAdjunction_unit l U M
  have hN := isIso_pi_lift_adicUpperStarLowerStarAdjunction_unit l U
    (⨁ fun _ : Fin n ↦ AdicSheaf.unit l (∐ U))
  exact ⟨@asIso _ _ _ _
      (Pi.lift fun s ↦ (adicUpperStarLowerStarAdjunction l (Sigma.ι U s)).unit.app M) hM ≪≫
    Pi.mapIso (fun s ↦ (Sigma.ι U s)_*ᵃ[l].mapIso
      (e s ≪≫ (AdicSheaf.freeUpperStarIso l (Fin n) (Sigma.ι U s)).symm)) ≪≫
    (@asIso _ _ _ _ (Pi.lift fun s ↦ (adicUpperStarLowerStarAdjunction l (Sigma.ι U s)).unit.app
      (⨁ fun _ : Fin n ↦ AdicSheaf.unit l (∐ U))) hN).symm⟩

/-- **A lisse sheaf on a connected qcqs scheme is trivialised on a single affine pro-étale
cover**, with a single rank. -/
theorem IsAdicLisseSheaf.exists_affine_cover_iso {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] [ConnectedSpace Y] {G : AdicSheaf l Y} (hG : IsAdicLisseSheaf G) :
    ∃ (V : Scheme.{u}) (f : V ⟶ Y), WeaklyEtale f ∧ Surjective f ∧ QuasiCompact f ∧
      IsAffine V ∧ ∃ n : ℕ, Nonempty ((f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) := by
  classical
  obtain ⟨R, hR, hRG⟩ := hG
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRG (f i) (.mk i)
  have hsurj : ∀ y, ∃ i, y ∈ Set.range (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  -- the ranks agree at points with the same image
  have hn (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 G) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  -- the rank is constant, `Y` being connected
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  obtain ⟨i₀, v₀, -⟩ := hsurj y₀
  let A (m : ℕ) : Set Y := {y | ∃ i, ∃ v : V i, f i v = y ∧ n i = m}
  have hpre (m : ℕ) (j : ι) : (f j).base ⁻¹' A m = if n j = m then Set.univ else ∅ := by
    ext v
    simp only [Set.mem_preimage, A, Set.mem_ofPred_eq]
    split_ifs with h
    · exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨j, v, rfl, h⟩⟩
    · exact ⟨fun ⟨i, v', hv', hi⟩ ↦ h ((hn j i v v' hv'.symm).trans hi), fun h ↦ h.elim⟩
  have hopen (m : ℕ) : IsOpen (A m) :=
    Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage f hR _ fun j ↦ by
      rw [hpre]
      split_ifs <;> simp
  have hA : A (n i₀) = Set.univ := by
    refine (IsClopen.eq_univ ⟨?_, hopen _⟩ ⟨f i₀ v₀, i₀, v₀, rfl, rfl⟩)
    have : (A (n i₀))ᶜ = ⋃ m ∈ ({n i₀}ᶜ : Set ℕ), A m := by
      ext y
      obtain ⟨i, v, rfl⟩ := hsurj y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, A,
        Set.mem_ofPred_eq]
      constructor
      · exact fun h ↦ ⟨n i, fun h' ↦ h ⟨i, v, rfl, h'⟩, i, v, rfl, rfl⟩
      · rintro ⟨m, hm, i', v', hv', rfl⟩ ⟨i'', v'', hv'', h''⟩
        exact hm ((hn i' i'' v' v'' (hv'.trans hv''.symm)).trans h'')
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun m _ ↦ hopen m
  have hrank (i : ι) (v : V i) : n i = n i₀ := by
    obtain ⟨i', v', hv', h'⟩ : f i v ∈ A (n i₀) := by rw [hA]; trivial
    exact (hn i i' v v' hv'.symm).trans h'
  -- finitely many affine opens of the members cover `Y`
  let E : PreZeroHypercover Y := ⟨ι, V, f⟩
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.1
    ((show Scheme.proetalePrecoverage ≤ Scheme.qcPrecoverage from inf_le_left) _ hR)
  obtain ⟨N, a, W, hW, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  let U (s : ULift.{u} (Fin N)) : Scheme.{u} := (W s.down).toScheme
  have : ∀ s, IsAffine (U s) := fun s ↦ hW s.down
  let g : ∐ U ⟶ Y := Sigma.desc fun s ↦ (W s.down).ι ≫ f (a s.down)
  have hg (s : ULift.{u} (Fin N)) : Sigma.ι U s ≫ g = (W s.down).ι ≫ f (a s.down) :=
    Sigma.ι_comp_desc _ _
  have : WeaklyEtale g :=
    IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) fun s ↦ inferInstance
  have : Surjective g := by
    refine ⟨fun y ↦ ?_⟩
    have : y ∈ ⋃ i, E.f (a i) '' (W i : Set _) := by rw [hcov]; trivial
    obtain ⟨i, w, hw, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using this
    refine ⟨Sigma.ι U ⟨i⟩ ⟨w, hw⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hg]
    rfl
  refine ⟨∐ U, g, inferInstance, inferInstance, inferInstance, inferInstance, n i₀, ?_⟩
  refine nonempty_iso_of_sigma U fun s ↦ ?_
  by_cases hs : Nonempty (U s)
  · rw [← hrank (a s.down) ((W s.down).ι hs.some)]
    exact ((adicUpperStarComp l (Sigma.ι U s) g).app G).symm ≪≫
      (adicUpperStarCongr l (hg s)).app G ≪≫
      AdicSheaf.trivPull (f (a s.down)) (e (a s.down)).some (W s.down).ι
  · have : IsEmpty (U s) := not_nonempty_iff.1 hs
    exact isoOfIsEmpty _ _

end AlgebraicGeometry.ProEtale
