/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Bounded rank of a lisse `ℓ`-adic sheaf

A lisse `ℓ`-adic sheaf `H` on a quasi-compact scheme `Y` has bounded rank: there is `d` such that
for every point `s : Spec K ⟶ Y` with values in an algebraically closed field the stalk
`Γ(Spec K, s^* H)` has dimension at most `d`. Indeed `H` is trivialised, `≅ ℚ̄_ℓⁿⁱ`, on the
members `fᵢ : Vᵢ ⟶ Y` of a pro-étale cover, finitely many of which cover `Y`, the cover being
quasi-compact; the point `s` lifts to a member `fᵢ` whose image contains it, so that
`s^* H ≅ ℚ̄_ℓⁿⁱ` on `Spec K`, whose global sections have dimension `nᵢ`.

## Main statements

- `AlgebraicGeometry.ProEtale.finrank_globalSections_biproduct_unit`: the global sections of
  `ℚ̄_ℓⁿ` on the spectrum of a field have dimension `n`.
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_finrank_globalSections_upperStar_le`: the
  stalks of a lisse sheaf on a quasi-compact scheme have bounded dimension.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The global sections of `ℚ̄_ℓⁿ` on the spectrum of a field form an `n`-dimensional space. -/
theorem finrank_globalSections_biproduct_unit (K : Type u) [Field K] (n : ℕ) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
        (⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))).X)) = n := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let G := Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l
  let e' : G.obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))).X ≅
      ModuleCat.of _ (Fin n → G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    G.mapIso ((AdicSheaf.forget _).mapBiproduct
      (fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K)))) ≪≫
      G.mapBiproduct (fun _ : Fin n ↦ adicConstantSheaf l (Spec (.of K))) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj (adicConstantSheaf l (Spec (.of K))))
  have h1 : Module.finrank (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) = 1 :=
    finrank_globalSections_adicConstantSheaf (Spec (.of K))
  have : FiniteDimensional (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    Module.finite_of_finrank_eq_succ h1
  change Module.finrank (PadicAlgCl l)
    (G.obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))).X) = n
  calc _ = Module.finrank (PadicAlgCl l) (Fin n → G.obj (adicConstantSheaf l (Spec (.of K)))) :=
        e'.toLinearEquiv.finrank_eq
    _ = n := by rw [Module.finrank_pi_fintype, h1]; simp

/-- **A lisse sheaf on a quasi-compact scheme has bounded rank.** If `H` is a lisse `ℓ`-adic
sheaf on a quasi-compact scheme `Y` and `K` is an algebraically closed field, the stalks
`Γ(Spec K, s^* H)` at the points `s : Spec K ⟶ Y` have bounded dimension. -/
theorem IsAdicLisseSheaf.exists_finrank_globalSections_upperStar_le {Y : Scheme.{u}}
    [CompactSpace Y] {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (K : Type u) [Field K]
    [IsAlgClosed K] :
    ∃ d : ℕ, ∀ s : Spec (.of K) ⟶ Y, Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj
        ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
          ((s)^*ᵃ[l].obj H).X)) ≤ d := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  -- finitely many members of the cover suffice, the cover being quasi-compact
  let E : PreZeroHypercover.{u + 1} Y := ⟨ι, V, f⟩
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.1
    ((show Scheme.proetalePrecoverage ≤ Scheme.qcPrecoverage from inf_le_left) _ hR)
  obtain ⟨m, g, W, -, hW⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) (by simpa using isCompact_univ)
  refine ⟨(Finset.univ.image g).sup n, fun s ↦ ?_⟩
  have hy : s.base (IsLocalRing.closedPoint K) ∈ ⋃ k, (f (g k)).base '' (W k) := by
    rw [hW]
    trivial
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
  obtain ⟨v, -, hv⟩ := hk
  obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale (f (g k)) s ⟨v, hv⟩
  obtain ⟨e'⟩ := nonempty_upperStar_iso_biproduct t ⟨adicUpperStarUnitIso l t⟩ (e (g k)).some
  let e'' : (s)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin (n (g k)) ↦ AdicSheaf.unit l (Spec (.of K)) :=
    (adicUpperStarCongr l ht.symm).app H ≪≫ (adicUpperStarComp l _ _).app H ≪≫ e'
  refine le_of_eq_of_le ((WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
    ((AdicSheaf.forget _).mapIso e''))).finrank_eq.trans
      (finrank_globalSections_biproduct_unit K (n (g k)))) ?_
  exact Finset.le_sup (Finset.mem_image_of_mem g (Finset.mem_univ k))

/-- **The stalks of a lisse sheaf on a quasi-compact scheme have bounded dimension.** If `F` is
lisse on `Y` and `Y` is quasi-compact, there is `N` such that the stalk `Γ(Spec K, s^* F)` at
every geometric point `s : Spec K ⟶ Y` has dimension at most `N`: finitely many members `fᵢ` of a
trivialising cover, with `fᵢ^* F ≅ ℚ̄_ℓ^{nᵢ}`, cover `Y`, and `s` lifts through one of them since
weakly étale covers of `Spec K` split, so the stalk has dimension some `nᵢ`. -/
theorem IsAdicLisseSheaf.exists_forall_finrank_le {Y : Scheme.{u}} [CompactSpace Y]
    {F : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y),
      Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
        ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
          ((s)^*ᵃ[l].obj F).X)) ≤ N := by
  obtain ⟨R, hR, h⟩ := hF
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : _ ∈ Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) _ :=
    (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from inf_le_right) _ hR
  rw [Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale : MorphismProperty Scheme.{u})] at hR'
  -- finitely many members of the cover suffice
  let E : PreZeroHypercover Y := ⟨ι, V, f⟩
  have hqc : QuasiCompactCover E := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact hR.1
  obtain ⟨m, a, W, -, hW⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E (U := ⊤) isCompact_univ
  choose n hn using fun i ↦ h (f i) (.mk i)
  refine ⟨Finset.univ.sup fun j : Fin m ↦ n (a j), fun K _ _ s ↦ ?_⟩
  -- `s` lifts through one of the finitely many members
  have hy : s.base (IsLocalRing.closedPoint K) ∈ ⋃ j, f (a j) '' W j := by
    rw [hW]
    trivial
  obtain ⟨j, v, -, hv⟩ := Set.mem_iUnion.1 hy
  have : WeaklyEtale (f (a j)) := hR'.2 (a j)
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (f := f (a j)) (g := s)
    v (IsLocalRing.closedPoint K) hv
  have : WeaklyEtale (pullback.snd (f (a j)) s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @WeaklyEtale)
      (IsPullback.of_hasPullback (f (a j)) s) ‹_›
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (pullback.snd (f (a j)) s) p
  have hs : (σ ≫ pullback.fst (f (a j)) s) ≫ f (a j) = s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  obtain ⟨e⟩ := hn (a j)
  have : (σ ≫ pullback.fst (f (a j)) s)^*ᵃ[l].Additive := inferInstance
  -- `s^* F ≅ t^* fⱼ^* F ≅ t^* ℚ̄_ℓⁿ ≅ ℚ̄_ℓⁿ`
  let e₁ : (s)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin (n (a j)) ↦ AdicSheaf.unit l (Spec (.of K)) :=
    (adicUpperStarCongr l hs).symm.app F ≪≫
      (adicUpperStarComp l (σ ≫ pullback.fst (f (a j)) s) (f (a j))).app F ≪≫
      (σ ≫ pullback.fst (f (a j)) s)^*ᵃ[l].mapIso e ≪≫
      (σ ≫ pullback.fst (f (a j)) s)^*ᵃ[l].mapBiproduct _ ≪≫
      biproduct.mapIso fun _ ↦ adicUpperStarUnitIso l _
  let G := Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l
  have := (G.mapIso ((AdicSheaf.forget _).mapIso e₁)).toLinearEquiv.finrank_eq
  calc _ = _ := this
    _ = n (a j) := finrank_globalSections_biproduct_unit K _
    _ ≤ _ := Finset.le_sup (f := fun j : Fin m ↦ n (a j)) (Finset.mem_univ j)

end AlgebraicGeometry.ProEtale
