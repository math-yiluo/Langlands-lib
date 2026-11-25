/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Lisse `ℓ`-adic sheaves on irreducible schemes

On an irreducible scheme `Y`, the pointwise rank of a morphism of lisse sheaves, computed on a
trivialising pro-étale cover, is constant: it descends to `Y`
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`), it is constant along
specializations (continuous functions to the Hausdorff space `ℚ̄_ℓ` are constant along
specializations, and flat morphisms lift generizations), and every point of `Y` is a
specialization of the generic point. Hence:

- the kernel and cokernel of a morphism of lisse sheaves on an irreducible quasi-compact scheme
  are lisse
  (`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace`);
- a nonzero lisse sheaf on an irreducible quasi-compact scheme has nonzero sections at every
  geometric point
  (`IsAdicLisseSheaf.nontrivial_globalSections_upperStar_of_irreducibleSpace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Abelian.hasFiniteBiproducts

open AdicSheaf in
/-- **Kernels and cokernels of lisse sheaves on an irreducible scheme are lisse.** On an
irreducible scheme the pointwise rank of a morphism of lisse sheaves is constant, being constant
along specializations, so that its kernel and cokernel are lisse
(`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_kernel_cokernel_of_rank_eq`). -/
theorem isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace {Y : Scheme.{u}}
    [IrreducibleSpace Y] {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicLisseSheaf G) (φ : F ⟶ G) :
    IsAdicLisseSheaf (kernel φ) ∧ IsAdicLisseSheaf (cokernel φ) := by
  classical
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨R', hR', hR'G⟩ := hG
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨ι', V', f', rfl⟩ := R'.exists_eq_ofArrows
  have hW := Precoverage.comp_mem_coverings f hR (fun i j ↦ pullback.fst (f i) (f' j))
    (fun i ↦ Precoverage.mem_coverings_of_isPullback f' hR' (f i) _ _
      fun j ↦ IsPullback.of_hasPullback (f i) (f' j))
  let W (k : Σ _ : ι, ι') : Scheme.{u} := pullback (f k.1) (f' k.2)
  let g (k : Σ _ : ι, ι') : W k ⟶ Y := pullback.fst (f k.1) (f' k.2) ≫ f k.1
  change Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage Y at hW
  have hgw (k) : WeaklyEtale (g k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hW (.mk k)
  choose n e using fun i ↦ hRF (f i) (.mk i)
  choose m e' using fun j ↦ hR'G (f' j) (.mk j)
  let eF (k : Σ _ : ι, ι') : (g k)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin (n k.1) ↦ unit l (W k) :=
    trivPull (f k.1) (e k.1).some (pullback.fst (f k.1) (f' k.2))
  let eG (k : Σ _ : ι, ι') : (g k)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin (m k.2) ↦ unit l (W k) :=
    (adicUpperStarCongr l pullback.condition).app G ≪≫
      trivPull (f' k.2) (e' k.2).some (pullback.snd (f k.1) (f' k.2))
  let M (k : Σ _ : ι, ι') := unitMatrix ((eF k).inv ≫ (g k)^*ᵃ[l].map φ ≫ (eG k).hom)
  let rk (k : Σ _ : ι, ι') (v : W k) : ℕ :=
    ((M k).map (PadicAlgCl.locallyFiniteFunctionsEval v)).rank
  have hfc (k k' : Σ _ : ι, ι') (v : W k) (v' : W k') (h : g k v = g k' v') :
      rk k v = rk k' v' :=
    rank_eq_of_apply_eq φ (g k) (g k') (eF k) (eG k) (eF k') (eG k') v v' h
  have hspec (k : Σ _ : ι, ι') {v₀ v : W k} (hv : v₀ ⤳ v) : rk k v₀ = rk k v := by
    have : (M k).map (PadicAlgCl.locallyFiniteFunctionsEval v₀) =
        (M k).map (PadicAlgCl.locallyFiniteFunctionsEval v) := by
      ext a b
      exact (hv.map ((M k) a b).1.continuous).eq
    simp only [rk, this]
  -- the rank at every point equals the rank at the generic point
  have hsurj : ∀ y, ∃ k, y ∈ Set.range (g k) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hW)).1
  -- the rank at every point equals the rank over the generic point
  obtain ⟨k₀, v₀, hv₀⟩ := hsurj (genericPoint Y)
  have hr (k : Σ _ : ι, ι') (v : W k) : rk k v = rk k₀ v₀ := by
    have hg : GeneralizingMap (g k) := Flat.generalizingMap _
    obtain ⟨w, hw, hgw⟩ := hg (show genericPoint Y ⤳ g k v from genericPoint_specializes _)
    rw [← hspec k hw]
    exact hfc _ _ _ _ (hgw.trans hv₀.symm)
  have hmem (k : Σ _ : ι, ι') :
      IsAdicLisseSheaf (kernel ((g k)^*ᵃ[l].map φ)) ∧
        IsAdicLisseSheaf (cokernel ((g k)^*ᵃ[l].map φ)) :=
    isAdicLisseSheaf_kernel_of_eq_comp _ _ (eF k).symm (eG k) rfl
      (isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ (rk k₀ v₀) (hr k))
  exact ⟨IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).1.of_iso (PreservesKernel.iso _ _).symm,
    IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).2.of_iso (PreservesCokernel.iso _ _).symm⟩

open ZeroObject in
/-- **A nonzero lisse sheaf on an irreducible scheme has nonzero stalks everywhere.** Let `H` be a
nonzero lisse sheaf on an irreducible quasi-compact scheme `Y`. Then `Γ(Spec K, s^* H)` is
nonzero at every geometric point `s : Spec K ⟶ Y`. Indeed the rank of a trivialisation of `H`
descends to `Y`, is constant along specializations (flat morphisms lift generizations), hence
constant on `Y`, and is positive somewhere, `H` being nonzero. -/
theorem IsAdicLisseSheaf.nontrivial_globalSections_upperStar_of_irreducibleSpace
    {Y : Scheme.{u}} [IrreducibleSpace Y] {H : AdicSheaf l Y}
    (hH : IsAdicLisseSheaf H) (hH0 : ¬ IsZero H) (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ Y) :
    Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X)) := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  -- the rank of the trivialisations descends to `Y`
  have hn (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 H) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  -- the rank is the same at all points: compare with the generic point
  have hgen (i : ι) (v : V i) (i' : ι) (v' : V i') : n i = n i' := by
    obtain ⟨w, -, hw⟩ := (Flat.generalizingMap (f i)) (genericPoint_specializes (f i v))
    obtain ⟨w', -, hw'⟩ := (Flat.generalizingMap (f i')) (genericPoint_specializes (f i' v'))
    exact hn i i' w w' (hw.trans hw'.symm)
  -- some member has a point and positive rank
  obtain ⟨i, v, hi⟩ : ∃ i, ∃ _ : V i, 0 < n i := by
    by_contra! hcon
    have hz (i : ι) : IsZero ((f i)^*ᵃ[l].obj H) := by
      by_cases hV : Nonempty (V i)
      · obtain ⟨v⟩ := hV
        have h0 : n i = 0 := Nat.le_zero.1 (hcon i v)
        refine IsZero.of_iso ?_ (e i).some
        rw [h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      · have : IsEmpty (V i) := not_nonempty_iff.1 hV
        exact isZero_adicSheaf_of_isEmpty l _
    have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
      have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
      rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
      infer_instance
    exact hH0 ((isZero_zero _).of_iso (asIso (0 : H ⟶ 0)))
  have hsurj : ∀ y, ∃ j, y ∈ Set.range (f j) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  obtain ⟨j, w, hw⟩ := hsurj (s.base (IsLocalRing.closedPoint K))
  have hpos : 0 < n j := (hgen j w i v) ▸ hi
  obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale (f j) s ⟨w, hw⟩
  let E : (s)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin (n j) ↦ AdicSheaf.unit l (Spec (.of K)) :=
    (adicUpperStarCongr l ht.symm).app H ≪≫ AdicSheaf.trivPull (f j) (e j).some t
  let a := biproduct.ι (fun _ : Fin (n j) ↦ AdicSheaf.unit l (Spec (.of K))) ⟨0, hpos⟩ ≫ E.inv
  let b := E.hom ≫ biproduct.π (fun _ : Fin (n j) ↦ AdicSheaf.unit l (Spec (.of K))) ⟨0, hpos⟩
  have hab : a.hom ≫ b.hom = 𝟙 _ := by
    rw [← Mod.comp_hom']
    simp [a, b]
  have : Nonempty (Spec (.of K)) := ⟨IsLocalRing.closedPoint K⟩
  have : Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      (AdicSheaf.unit l (Spec (.of K))).X) :=
    nontrivial_globalSections_adicConstantSheaf (l := l) (Spec (.of K))
  refine Function.Injective.nontrivial (f := ((Sheaf.Γ _ _).map a.hom).hom) fun x x' hxx' ↦ ?_
  have h₁ := congrArg ((Sheaf.Γ _ _).map b.hom).hom hxx'
  have h₂ (z) : ((Sheaf.Γ _ _).map b.hom).hom (((Sheaf.Γ _ _).map a.hom).hom z) = z := by
    have := congrArg (fun φ ↦ φ.hom z) (((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K)))
      (WeilCoefficients.{u} l)).map_comp a.hom b.hom).symm.trans
        ((congrArg (Sheaf.Γ _ _).map hab).trans ((Sheaf.Γ _ _).map_id _)))
    simpa using this
  rwa [h₂, h₂] at h₁

end AlgebraicGeometry.ProEtale
