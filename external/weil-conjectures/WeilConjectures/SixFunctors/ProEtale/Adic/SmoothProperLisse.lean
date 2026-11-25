/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.EtaleBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperTwistedLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.RegularLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TransitionCocycle
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedProperBaseChange

/-!
# Higher direct images of lisse sheaves along smooth proper morphisms are lisse

Let `K` be an algebraically closed field (or any field), `Y` locally of finite type over `K`,
`f : X ⟶ Y` smooth and proper and `F` a lisse `ℓ`-adic sheaf on `X`, `ℓ` invertible in `K`.
Then every `Hⁿ(Rf_* F[0])` is lisse
(`ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`,
Step 1 of blueprint `theorem-purity-higher-direct-images-under`).

The proof follows the blueprint. Being lisse is local on `Y`, so `Y` may be assumed affine,
hence `X` quasi-compact, and by the decomposition along connected components `X` may be assumed
connected. Then `F` is trivialised on a single affine pro-étale cover `V ⟶ X`, with transition
cocycle `γ : V ×_X V → GL_n(E)`, and a lattice of `F` is a twisted section of `γ` acting on the
lattices of `Eⁿ`. The geometric fibres of `f` are regular, so `F` has a lattice on them
(`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice_of_isRegular`), and by proper base
change in degree zero every point of `Y` has an étale neighbourhood `U` such that `F` has a
lattice on `X ×_Y U` (`AlgebraicGeometry.exists_etale_isTwistedSection_of_isProper`). There the
lattice case applies
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_isTwistedSection`),
and étale base change identifies the result with the restriction of `Hⁿ(Rf_* F[0])` to `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf

variable {l : ℕ} [Fact l.Prime]

/-- The transition matrices of the base change of a trivialisation to a pulled back cover are
the pulled back transition matrices. -/
lemma transitionMatrix_trivBaseChange_eval {X T V : Scheme.{u}} {G : AdicSheaf l X}
    (f₀ : V ⟶ X) [WeaklyEtale f₀] {n : ℕ}
    (ε : (f₀)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) (π : T ⟶ X) [WeaklyEtale π]
    (w : ↥(pullback (pullback.snd f₀ π) (pullback.snd f₀ π))) :
    (transitionMatrix (trivBaseChange ε π (pullback.snd f₀ π) (pullback.fst f₀ π)
        pullback.condition.symm) (pullback.snd (pullback.snd f₀ π) (pullback.snd f₀ π))
        (pullback.fst (pullback.snd f₀ π) (pullback.snd f₀ π)) pullback.condition.symm).map
        (locallyFiniteFunctionsEval w) =
      (transitionMatrix ε (pullback.snd f₀ f₀) (pullback.fst f₀ f₀) pullback.condition.symm).map
        (locallyFiniteFunctionsEval ((twistedPairMap f₀ π).base w)) := by
  set m := twistedPairMap f₀ π
  set r₁ := pullback.fst (pullback.snd f₀ π) (pullback.snd f₀ π)
  set r₂ := pullback.snd (pullback.snd f₀ π) (pullback.snd f₀ π)
  have hm₁ : m ≫ pullback.fst f₀ f₀ = r₁ ≫ pullback.fst f₀ π := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f₀ f₀ = r₂ ≫ pullback.fst f₀ π := pullback.lift_snd _ _ _
  have : WeaklyEtale (m ≫ pullback.fst f₀ f₀) := by rw [hm₁]; infer_instance
  have : WeaklyEtale m := WeaklyEtale.of_comp _ (pullback.fst f₀ f₀)
  have hr : r₁ ≫ pullback.snd f₀ π = r₂ ≫ pullback.snd f₀ π := pullback.condition
  have hr' : (r₂ ≫ pullback.fst f₀ π) ≫ f₀ = (r₁ ≫ pullback.fst f₀ π) ≫ f₀ := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
      hr]
  rw [transitionMatrix_baseChange ε π _ _ pullback.condition.symm r₂ r₁ _ hr',
    transitionMatrix_congr ε hm₂.symm hm₁.symm _ (by rw [hm₁, hm₂, hr']),
    transitionMatrix_comp ε m _ _ pullback.condition.symm]
  simp only [map_locallyFiniteFunctionsComp_map_eval]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf

variable {l : ℕ} [Fact l.Prime]

/-- **Lisse direct images along smooth proper morphisms, connected case.** For `Y` affine and
locally of finite type over a field of characteristic `≠ ℓ`, `f : X ⟶ Y` smooth and proper with
`X` connected, and `F` lisse on `X`, every `Rⁿf_* F` is lisse. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper_of_connected
    {K : Type u} [Field K] (hK : ringChar K ≠ l) {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType s] [IsAffine Y] (f : X ⟶ Y) [Smooth f] [IsProper f] [ConnectedSpace X]
    {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨V, f₀, hfe, hfs, hfq, hV, m, ⟨ε⟩⟩ := hF.exists_affine_cover_iso (l := l)
  have : CompactSpace ↥(pullback f₀ f₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f₀ f₀)
  obtain ⟨E, hE, γ, hγ, hγc, hγc', hdiag, hcoc⟩ := AdicSheaf.exists_transitionCocycle f₀ ε
  have hc := AdicSheaf.isDescentCocycle_smul_compactOpenLattice f₀ γ hγc hγc' hdiag hcoc
  have hloc (y : Y) : ∃ (U : Scheme.{u}) (j : U ⟶ Y), Etale j ∧ y ∈ Set.range j.base ∧
      IsAdicLisseSheaf ((j)^*ᵃ[l].obj ((DerivedCategory.homologyFunctor _ n).obj
        ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
    obtain ⟨U, j, hj, hU, hy, σ, hσ⟩ := exists_etale_isTwistedSection_of_isProper f f₀ hc
      (fun Z π _ _ _ ↦ exists_isTwistedSection_compactOpenLattice_of_isRegular f₀ γ hc π) y
    have := hU
    refine ⟨U, j, hj, hy, ?_⟩
    set π := pullback.fst f j
    have : IsAffineHom π := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
    have key := isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_isTwistedSection hK
      (j ≫ s) (pullback.snd f j) (F := (π)^*ᵃ[l].obj F) (pullback.snd f₀ π)
      (trivBaseChange ε π (pullback.snd f₀ π) (pullback.fst f₀ π) pullback.condition.symm) E
      (fun w ↦ γ ((twistedPairMap f₀ π).base w))
      (fun w ↦ by rw [hγ, transitionMatrix_trivBaseChange_eval])
      _ hσ.pullbackCover n
    exact key.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      (mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIsoOfEtale f j F).symm ≪≫
      (((j)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app _).symm)
  choose U j hj hy hlisse using hloc
  refine IsAdicLisseSheaf.of_cover j (Scheme.etalePrecoverage_le_proetalePrecoverage _ ?_) hlisse
  exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun y ↦ ⟨y, hy y⟩, hj⟩

/-- **Lisse direct images along smooth proper morphisms, over an affine base.** For `Y` affine
and locally of finite type over a field of characteristic `≠ ℓ`, `f : X ⟶ Y` smooth and proper
and `F` lisse on `X`, every `Rⁿf_* F` is lisse: reduce to the connected components of `X`. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper_of_isAffine
    {K : Type u} [Field K] (hK : ringChar K ≠ l) {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType s] [IsAffine Y] (f : X ⟶ Y) [Smooth f] [IsProper f]
    {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
  refine isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_connectedComponents f F n
    fun Z ι _ _ _ ↦ ?_
  exact isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper_of_connected
    hK s (ι ≫ f) (hF.upperStar ι) n

/-- **Higher direct images of lisse sheaves along smooth proper morphisms are lisse** (Step 1 of
blueprint `theorem-purity-higher-direct-images-under`): over a field `K` of characteristic `≠ ℓ`,
the higher direct images `Rⁿf_* F` of a lisse `ℓ`-adic sheaf along a smooth proper morphism `f` of
schemes locally of finite type over `K` are lisse. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper
    {K : Type u} [Field K] {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (hK : ringChar K ≠ l) [LocallyOfFiniteType s] [Smooth f] [IsProper f] {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have hloc (y : Y) : ∃ (W : Scheme.{u}) (j : W ⟶ Y), Etale j ∧ y ∈ Set.range j.base ∧
      IsAdicLisseSheaf ((j)^*ᵃ[l].obj ((DerivedCategory.homologyFunctor _ n).obj
        ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    have : IsAffine W.toScheme := hW
    refine ⟨W.toScheme, W.ι, inferInstance, ⟨⟨y, hyW⟩, rfl⟩, ?_⟩
    refine
      (isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper_of_isAffine
      hK (W.ι ≫ s) (pullback.snd f W.ι) (hF.upperStar (pullback.fst f W.ι)) n).of_iso ?_
    exact (DerivedCategory.homologyFunctor _ n).mapIso
      (mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIsoOfEtale f W.ι F).symm ≪≫
      (((W.ι)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app _).symm
  choose W j hj hy hlisse using hloc
  refine IsAdicLisseSheaf.of_cover j (Scheme.etalePrecoverage_le_proetalePrecoverage _ ?_) hlisse
  exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun y ↦ ⟨y, hy y⟩, hj⟩

end AlgebraicGeometry.ProEtale
