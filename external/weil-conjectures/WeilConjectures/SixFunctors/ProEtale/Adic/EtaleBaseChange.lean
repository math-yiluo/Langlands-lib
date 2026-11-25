/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.Adic.EtaleLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.SplitCovering

/-!
# Étale base change and clopen decomposition for direct images of `ℓ`-adic sheaves

* For an étale `j : U ⟶ Y`, the restriction of `Rf_* F` to `U` is computed on `X ×_Y U`
  (`AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIsoOfEtale`),
  generalising the open base change
  `AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso`.
* If `X` has finitely many connected components, `Hⁿ(Rf_* F)` is lisse as soon as the
  corresponding sheaves for the restrictions of `f` to the connected components are
  (`isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_connectedComponents`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Étale base change for `Rf_*`**: the restriction of `Rf_* F` along an étale `j : U ⟶ Y` is
computed on `X ×_Y U`. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIsoOfEtale
    {U : Scheme.{u}} (j : U ⟶ Y) [Etale j] (F : AdicSheaf l X) :
    (j)^*ᵃ[l].mapDerivedCategory.obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (pullback.snd f j)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((pullback.fst f j)^*ᵃ[l].obj F)) :=
  (adicDerivedBaseChangeIsoOfWeaklyEtale l (IsPullback.of_hasPullback f j).flip).app _ ≪≫
    Functor.mapIso _ (((pullback.fst f j)^*ᵃ[l].mapDerivedCategorySingleFunctor 0).app F)

section Clopen

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Z T : Scheme.{u}}

/-- The pushforward along an open and closed immersion is exact: it is the extension by zero
(`AlgebraicGeometry.ProEtale.isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range`). -/
instance preservesFiniteColimits_adicLowerStar_of_isOpenImmersion_of_isClosedImmersion
    (ι : Z ⟶ T) [IsOpenImmersion ι] [IsClosedImmersion ι] :
    PreservesFiniteColimits (ι)_*ᵃ[l] :=
  have := isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range l ι
    ι.isClosedEmbedding.isClosed_range
  preservesFiniteColimits_of_natIso (asIso (adicOpenImmersionLowerShriekToLowerStar l ι))

/-- For an open and closed immersion `ι`, `R(ι ≫ g)_* (H[0]) ≅ Rg_* ((ι_* H)[0])`, the
pushforward `ι_*` being exact. -/
noncomputable def rightDerivedFunctorLowerStarCompSingleIso (ι : Z ⟶ T) [IsOpenImmersion ι]
    [IsClosedImmersion ι] (g : T ⟶ Y) (H : AdicSheaf l Z) :
    (ι ≫ g)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅
      (g)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((ι)_*ᵃ[l].obj H)) :=
  (Functor.rightDerivedFunctorIsoMapDerivedCategoryComp (adicLowerStarComp l ι g)).app _ ≪≫
    (g)_*ᵃ[l].rightDerivedFunctor.mapIso (((ι)_*ᵃ[l].mapDerivedCategorySingleFunctor 0).app H)

/-- **Clopen decomposition of higher direct images.** For finitely many open and closed
immersions `s k : Z k ⟶ T` with pairwise disjoint ranges covering `T`,
`Hⁿ(Rg_* G) ≅ ⨁ₖ Hⁿ(R(s k ≫ g)_* (s k)^* G)`: the sheaf `G` is the direct sum of the
`(s k)_* (s k)^* G`. -/
noncomputable def homologyRightDerivedFunctorLowerStarIsoBiproduct {κ : Type} [Finite κ]
    {Z : κ → Scheme.{u}} (s : ∀ k, Z k ⟶ T) [∀ k, IsOpenImmersion (s k)]
    [∀ k, IsClosedImmersion (s k)]
    (hs : Pairwise fun k k' ↦ Disjoint (Set.range (s k).base) (Set.range (s k').base))
    (hcov : ∀ x, ∃ k, x ∈ Set.range (s k).base) (g : T ⟶ Y) (G : AdicSheaf l T) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).obj
        ((g)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      ⨁ fun k ↦ (DerivedCategory.homologyFunctor _ n).obj
        ((s k ≫ g)_*ᵃ[l].rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj ((s k)^*ᵃ[l].obj G))) :=
  have := isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit_of_cover (l := l) s hs hcov G
  let Φ := DerivedCategory.singleFunctor (AdicSheaf l T) 0 ⋙ (g)_*ᵃ[l].rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ n
  Φ.mapIso (@asIso _ _ _ _ (biproduct.lift fun k ↦
      (adicUpperStarLowerStarAdjunction l (s k)).unit.app G) this) ≪≫ Φ.mapBiproduct _ ≪≫
    biproduct.mapIso fun k ↦ (DerivedCategory.homologyFunctor _ n).mapIso
      (rightDerivedFunctorLowerStarCompSingleIso (s k) g _).symm


/-- **Lisse direct images can be checked on connected components.** -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_connectedComponents
    [IsLocallyNoetherian X] [CompactSpace X] (F : AdicSheaf l X) (n : ℤ)
    (h : ∀ (Z : Scheme.{u}) (ι : Z ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
      [ConnectedSpace Z], IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
        ((ι ≫ f)_*ᵃ[l].rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj ((ι)^*ᵃ[l].obj F))))) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  have : IsNoetherian X := ⟨⟩
  by_cases hX : Nonempty X
  swap
  · have : ∀ k : Empty, QuasiCompact (k.elim : X ⟶ X) := fun k ↦ k.elim
    have hF : IsZero F := isZero_of_forall_isZero_adicUpperStar (κ := Empty) (Z := fun _ ↦ X)
      (fun k ↦ k.elim) (fun x ↦ (hX ⟨x⟩).elim) F fun k ↦ k.elim
    exact IsAdicLisseSheaf.of_isZero ((DerivedCategory.singleFunctor _ 0 ⋙
      (f)_*ᵃ[l].rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ n).map_isZero hF)
  suffices key : ∀ (V : X.Opens) (Z : Scheme.{u}) (ι : Z ⟶ X) [IsOpenImmersion ι]
      [IsClosedImmersion ι], Nonempty Z → (Set.range ι.base)ᶜ = (V : Set X) →
      IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
        ((ι ≫ f)_*ᵃ[l].rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj ((ι)^*ᵃ[l].obj F)))) by
    have hid := key ⟨_, (𝟙 X : X ⟶ X).isClosedEmbedding.isClosed_range.isOpen_compl⟩ X (𝟙 X)
      hX rfl
    rw [Category.id_comp] at hid
    exact hid.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((f)_*ᵃ[l].rightDerivedFunctor.mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso ((adicUpperStarId l X).app F))))
  intro V
  induction V using WellFoundedGT.induction
  rename_i V ih
  intro Z ι _ _ hZ hV
  by_cases hc : ConnectedSpace Z
  · exact h Z ι
  obtain ⟨S, hS, hS0, hSu⟩ : ∃ S : Set Z, IsClopen S ∧ S.Nonempty ∧ S ≠ Set.univ := by
    rw [connectedSpace_iff_clopen] at hc
    push Not at hc
    exact hc hZ
  let O : Bool → Z.Opens := fun b ↦ cond b ⟨S, hS.isOpen⟩ ⟨Sᶜ, hS.compl.isOpen⟩
  have hO (b : Bool) : IsClosed (O b : Set Z) := by
    cases b
    · exact hS.isOpen.isClosed_compl
    · exact hS.isClosed
  have : ∀ b, IsClosedImmersion (O b).ι := fun b ↦
    IsClosedImmersion.of_isOpenImmersion _ (by rw [Scheme.Opens.range_ι]; exact hO b)
  have hdisj : Pairwise fun b b' : Bool ↦
      Disjoint (Set.range (O b).ι.base) (Set.range (O b').ι.base) := by
    intro b b' hbb'
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    cases b <;> cases b'
    · exact absurd rfl hbb'
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact absurd rfl hbb'
  have hcov (x : Z) : ∃ b, x ∈ Set.range (O b).ι.base := by
    by_cases hx : x ∈ S
    · exact ⟨true, by rw [Scheme.Opens.range_ι]; exact hx⟩
    · exact ⟨false, by rw [Scheme.Opens.range_ι]; exact hx⟩
  refine (IsAdicLisseSheaf.biproduct fun b ↦ ?_).of_iso
    (homologyRightDerivedFunctorLowerStarIsoBiproduct (fun b ↦ (O b).ι) hdisj hcov (ι ≫ f)
      ((ι)^*ᵃ[l].obj F) n).symm
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (O b : Set Z) := by
    cases b
    · obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem S).1 hSu
      exact ⟨y, hy⟩
    · exact hS0
  obtain ⟨z, hz⟩ : ∃ z, z ∉ (O b : Set Z) := by
    cases b
    · obtain ⟨z, hz⟩ := hS0
      exact ⟨z, fun h ↦ h hz⟩
    · exact (Set.ne_univ_iff_exists_notMem S).1 hSu
  have hlt : V < ⟨(Set.range ((O b).ι ≫ ι).base)ᶜ,
      ((O b).ι ≫ ι).isClosedEmbedding.isClosed_range.isOpen_compl⟩ := by
    rw [IsConcreteLE.lt_iff_le_and_exists]
    refine ⟨fun x hx hx' ↦ ?_, ι.base z, fun hw ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨w, hw⟩ := hx'
      have hx'' : x ∈ (V : Set X) := hx
      rw [← hV] at hx''
      exact hx'' ⟨(O b).ι.base w, hw⟩
    · obtain ⟨w, hw⟩ := hw
      have hw' : ι.base ((O b).ι.base w) = ι.base z := hw
      have hw'' := ι.isOpenEmbedding.injective hw'
      exact hz (by rw [← hw'', ← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩)
    · have hx' : ι.base z ∈ (V : Set X) := hx
      rw [← hV] at hx'
      exact hx' ⟨z, rfl⟩
  have hb := ih _ hlt _ ((O b).ι ≫ ι) ⟨⟨y, hy⟩⟩ rfl
  rw [Category.assoc] at hb
  exact hb.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
    (((O b).ι ≫ ι ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((adicUpperStarComp l (O b).ι ι).app F))))

end Clopen

end AlgebraicGeometry.ProEtale
