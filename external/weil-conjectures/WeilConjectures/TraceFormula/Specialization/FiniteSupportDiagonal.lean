/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointsSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper

/-!

# Finite direct image is conservative where the diagonal is open

Let `f : Z ⟶ B` be a finite morphism of separated `k`-schemes of finite type and `F` a bounded
constructible `ℚ̄_ℓ`-complex on `Z` with `Rf_* F = 0`. By proper base change along `f`,
`Rp₁_* Lp₂^* F = 0` on `Z`, where `p₁, p₂ : Z ×_B Z ⟶ Z` are the projections. Over an open `V` of
`B` above which the diagonal `Δ : Z ⟶ Z ×_B Z` has open image, the open–closed triangle of `Δ`
splits, so that `F|_{f⁻¹ V} = LΔ^* Lp₂^* F|_{f⁻¹ V}` is a retract of `Rp₁_* Lp₂^* F|_{f⁻¹ V} = 0`
(`ProEtale.CondensedRing.isZero_upperStar_opensOverι_of_isOpen_range_diagonal`).

The splitting is `ProEtale.CondensedRing.isZero_upperStar_of_isZero_lowerStar_of_isOpen_range`:
a section `σ` of `p : W ⟶ Y` with open image satisfies `Lσ^* G = 0` whenever `Rp_* G = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Sections with open image -/

section Section

variable (ℓ) in
/-- **Hom vanishing along a proper morphism factoring through an open**: if `x = xV ≫ jV` is
proper with `jV` an open immersion and `D` vanishes on `V`, then every morphism `Rx_* E ⟶ D`
vanishes. Indeed `Rx_* ≅ Rx_!`, and `Rx^! D ≅ RxV^! RjV^! D ≅ RxV^! LjV^* D = 0`. -/
lemma eq_zero_of_lowerStar_of_isZero_upperStar {X V Z : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (xV : Z ⟶ V) (jV : V ⟶ X) [IsOpenImmersion jV.left] {x : Z ⟶ X} [IsProper x.left]
    (hx : xV ≫ jV = x) (E : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (D : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hD : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jV).obj D))
    (φ : (boundedConstructibleLowerStar ℓ x).obj E ⟶ D) :
    φ = 0 := by
  subst hx
  have hZ : IsZero ((boundedConstructibleUpperShriek ℓ
      (xV ≫ jV)).obj D) :=
    ((boundedConstructibleUpperShriek ℓ xV).map_isZero
      (hD.of_iso ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ jV).app D))).of_iso
      ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ xV jV).app D)
  set adj := boundedConstructibleUpperShriekAdjunction ℓ
    (xV ≫ jV)
  set e := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (xV ≫ jV)).app E
  have h : e.hom ≫ φ = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ φ), hZ.eq_of_tgt (adj.homEquiv _ _ _) 0,
      Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact (cancel_epi e.hom).1 (h.trans comp_zero.symm)

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- A section of a morphism of separated schemes is a closed immersion. -/
lemma isClosedImmersion_left_of_comp_eq_id {W Y : Over (Spec (.of k))} [IsSeparated W.hom]
    (p : W ⟶ Y) (σ : Y ⟶ W) (hσ : σ ≫ p = 𝟙 Y) : IsClosedImmersion σ.left := by
  have : IsSeparated (p.left ≫ Y.hom) := by
    rw [Over.w p]
    infer_instance
  have : IsSeparated p.left := IsSeparated.of_comp p.left Y.hom
  have : IsClosedImmersion (σ.left ≫ p.left) := by
    rw [← Over.comp_left, hσ, Over.id_left]
    infer_instance
  exact IsClosedImmersion.of_comp σ.left p.left

-- The last step identifies `Rp_* Rσ_*` with `R(σ ≫ p)_*`, which unfolds the pro-étale pullback.
/-- **Sections with open image split off**: let `σ` be a section of `p : W ⟶ Y` whose image is
open. If `Rp_* G = 0`, then `Lσ^* G = 0`. Indeed the connecting morphism of the open–closed
triangle `j_! Lj^* G ⟶ G ⟶ Rσ_* Lσ^* G ⟶` of `σ` vanishes, since `j_! Lj^* G` vanishes on the
open image of `σ` (`eq_zero_of_lowerStar_of_isZero_upperStar`); hence `Rσ_* Lσ^* G` is a retract
of `G`, and `Lσ^* G = Rp_* Rσ_* Lσ^* G` is a retract of `Rp_* G = 0`. -/
theorem isZero_upperStar_of_isZero_lowerStar_of_isOpen_range {W Y : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : W ⟶ Y) (σ : Y ⟶ W) (hσ : σ ≫ p = 𝟙 Y) (hopen : IsOpen (Set.range σ.left.base))
    (G : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hG : IsZero ((boundedConstructibleLowerStar ℓ p).obj G)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ σ).obj G) := by
  have := isClosedImmersion_left_of_comp_eq_id p σ hσ
  let A : W.left.Opens := ⟨Set.range σ.left.base, hopen⟩
  let C : W.left.Opens := ⟨(Set.range σ.left.base)ᶜ,
    σ.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hcompl : IsCompl (Set.range (opensOverι C).left.base) (Set.range σ.left.base) := by
    rw [range_opensOverι]
    exact isCompl_compl.symm
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_openClosed
    (opensOverι C) σ hcompl G
  obtain ⟨δ₀, hδ₀⟩ := WeilBoundedConstructible.exists_eq_map_comp_commShiftIso
    (ObjectProperty.fullyFaithfulι _) δ
  have hW : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι A)).obj ((shiftFunctor (Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (1 : ℤ)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (opensOverι C)).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (opensOverι C)).obj G)))) := by
    refine ((shiftFunctor _ (1 : ℤ)).map_isZero
      (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ (opensOverι C)
        (opensOverι A) ?_ _)).of_iso
      (((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι A)).commShiftIso (1 : ℤ)).app _)
    rw [range_opensOverι, range_opensOverι]
    exact disjoint_compl_left
  have hδ₀' : δ₀ = 0 :=
    eq_zero_of_lowerStar_of_isZero_upperStar ℓ (opensOverLift A σ subset_rfl) (opensOverι A)
      (opensOverLift_ι _ _ _) _ _ hW δ₀
  have hδ : δ = 0 := by
    rw [hδ₀, hδ₀', Functor.map_zero, zero_comp]
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hT (𝟙 _) (by
    rw [Triangle.mk_mor₃, hδ]
    exact comp_zero)
  have hs' : (ObjectProperty.fullyFaithfulι _).preimage s ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        σ).unit.app G = 𝟙 _ :=
    (boundedConstructible _).ι.map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_id]
      exact hs.symm)
  have hP : IsZero ((boundedConstructibleLowerStar ℓ p).obj
      ((boundedConstructibleLowerStar ℓ σ).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ σ).obj G))) := by
    have h := congrArg (boundedConstructibleLowerStar ℓ p).map hs'
    rw [Functor.map_comp, CategoryTheory.Functor.map_id,
      hG.eq_of_tgt ((boundedConstructibleLowerStar ℓ p).map _) 0, zero_comp] at h
    exact (IsZero.iff_id_eq_zero _).2 h.symm
  have key (q : Y ⟶ Y) (hq : q = 𝟙 Y) (X : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      (h : IsZero ((boundedConstructibleLowerStar ℓ q).obj X)) :
      IsZero X := by
    subst hq
    exact h.of_iso ((boundedConstructibleLowerStarId ℓ Y).app X).symm
  exact key _ hσ _ (hP.of_iso ((boundedConstructibleLowerStarComp ℓ σ p).app _).symm)

end Section

/-! ### The fibre square of a finite morphism -/

section Diagonal

variable {Z B : Over (Spec (.of k))} (f : Z ⟶ B)

/-- The fibre product `Z ×_B Z` of a morphism `f : Z ⟶ B`, as a scheme over `s`. -/
noncomputable abbrev fibreSquare : Over (Spec (.of k)) :=
  Over.mk (pullback.fst f.left f.left ≫ Z.hom)

/-- The first projection `Z ×_B Z ⟶ Z`. -/
noncomputable abbrev fibreSquareFst : fibreSquare f ⟶ Z :=
  Over.homMk (pullback.fst f.left f.left)

/-- The second projection `Z ×_B Z ⟶ Z`. -/
noncomputable abbrev fibreSquareSnd : fibreSquare f ⟶ Z :=
  Over.homMk (pullback.snd f.left f.left) (by
    simp only [Over.mk_left, Over.mk_hom, ← Over.w f, pullback.condition_assoc])

/-- The diagonal `Z ⟶ Z ×_B Z`. -/
noncomputable abbrev fibreSquareDiagonal : Z ⟶ fibreSquare f :=
  Over.homMk (pullback.diagonal f.left) (by simp)

instance [IsFinite f.left] [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (fibreSquare f).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.fst f.left f.left ≫ Z.hom))

instance [IsFinite f.left] [QuasiCompact Z.hom] : QuasiCompact (fibreSquare f).hom :=
  inferInstanceAs (QuasiCompact (pullback.fst f.left f.left ≫ Z.hom))

instance [IsFinite f.left] [IsSeparated Z.hom] : IsSeparated (fibreSquare f).hom :=
  inferInstanceAs (IsSeparated (pullback.fst f.left f.left ≫ Z.hom))

instance [IsFinite f.left] : IsFinite (fibreSquareFst f).left :=
  inferInstanceAs (IsFinite (pullback.fst f.left f.left))

omit [Fact (ringChar k).Prime] in
/-- The fibre square of `f` is cartesian. -/
lemma isPullback_fibreSquare :
    IsPullback (fibreSquareSnd f) (fibreSquareFst f) f f :=
  IsPullback.of_map (Over.forget _) (by ext1; exact pullback.condition.symm)
    (IsPullback.of_hasPullback f.left f.left).flip

variable [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] [IsFinite f.left]

/-- **Finite direct image is conservative where the diagonal is open**: let `f : Z ⟶ B` be finite
and `V ⊆ B` an open above which the diagonal of `Z ×_B Z` has open image. If `Rf_* F = 0`, then `F`
vanishes on `f⁻¹ V`. By proper base change, `Rp₁_* Lp₂^* F = 0`, also after restriction to
`f⁻¹ V`, where the diagonal is a section of `p₁` with open image; so
`F|_{f⁻¹ V} = LΔ^* Lp₂^* F|_{f⁻¹ V} = 0` by
`isZero_upperStar_of_isZero_lowerStar_of_isOpen_range`. -/
theorem isZero_upperStar_opensOverι_of_isOpen_range_diagonal
    (F : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hF : IsZero ((boundedConstructibleLowerStar ℓ f).obj F))
    (V : B.left.Opens)
    (hV : IsOpen (Set.range (pullback.diagonal f.left).base ∩
      (pullback.fst f.left f.left ≫ f.left).base ⁻¹' V)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (f.left ⁻¹ᵁ V))).obj F) := by
  set O := f.left ⁻¹ᵁ V
  set U : (fibreSquare f).left.Opens := pullback.fst f.left f.left ⁻¹ᵁ O
  -- proper base change along `f`
  have h₁ : IsZero ((boundedConstructibleLowerStar ℓ
      (fibreSquareFst f)).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (fibreSquareSnd f)).obj F)) := by
    have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ (isPullback_fibreSquare f)
    exact ((boundedConstructibleUpperStar _ ℓ f).map_isZero hF).of_iso
      ((asIso (boundedConstructibleBaseChange ℓ (isPullback_fibreSquare f).toCommSq)).app F).symm
  -- restriction to `f⁻¹ V`
  let p' : opensOver U ⟶ opensOver O :=
    Over.homMk (pullback.fst f.left f.left ∣_ O) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [morphismRestrict_ι_assoc])
  have w : p' ≫ opensOverι O = opensOverι U ≫ fibreSquareFst f := by
    ext1
    exact morphismRestrict_ι _ _
  have sq : IsPullback (opensOverι U) p' (fibreSquareFst f) (opensOverι O) :=
    (IsPullback.of_map (Over.forget _) w
      (isPullback_morphismRestrict (pullback.fst f.left f.left) O)).flip
  have h₂ : IsZero ((boundedConstructibleLowerStar ℓ p').obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι U)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (fibreSquareSnd f)).obj F))) := by
    have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
    exact ((boundedConstructibleUpperStar _ ℓ (opensOverι O)).map_isZero h₁).of_iso
      ((asIso (boundedConstructibleBaseChange ℓ sq.toCommSq)).app _).symm
  -- the restricted diagonal
  have hΔ (x : Z.left) : (pullback.fst f.left f.left) ((pullback.diagonal f.left) x) = x := by
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    rfl
  have himage : (pullback.diagonal f.left).base '' (O : Set Z.left) =
      Set.range (pullback.diagonal f.left).base ∩
        (pullback.fst f.left f.left ≫ f.left).base ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      rw [Set.mem_preimage, Scheme.Hom.comp_apply, hΔ]
      exact hx
    · rintro ⟨⟨x, rfl⟩, hx⟩
      refine ⟨x, ?_, rfl⟩
      rw [Set.mem_preimage, Scheme.Hom.comp_apply, hΔ] at hx
      exact hx
  have hrange : Set.range (O.ι ≫ pullback.diagonal f.left).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hΔ]
    exact x.2
  let σl : O.toScheme ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (O.ι ≫ pullback.diagonal f.left) hrange
  have hσU : σl ≫ U.ι = O.ι ≫ pullback.diagonal f.left :=
    IsOpenImmersion.lift_fac _ _ _
  let σ : opensOver O ⟶ opensOver U :=
    Over.homMk σl (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [reassoc_of% hσU, pullback.diagonal_fst_assoc])
  have hp' : p'.left ≫ O.ι = U.ι ≫ pullback.fst f.left f.left := morphismRestrict_ι _ _
  have hσ : σ ≫ p' = 𝟙 _ := by
    ext1
    rw [← cancel_mono O.ι, Over.comp_left, Category.assoc, hp']
    exact (reassoc_of% hσU) _ |>.trans (by rw [pullback.diagonal_fst, Category.comp_id]; rfl)
  have hσ₂ : (σ ≫ opensOverι U) ≫ fibreSquareSnd f = opensOverι O := by
    ext1
    exact (reassoc_of% hσU) (pullback.snd f.left f.left) |>.trans
      (by rw [pullback.diagonal_snd, Category.comp_id]; rfl)
  have hσx (x : O) : U.ι (σl x) = pullback.diagonal f.left x.1 := by
    rw [← Scheme.Hom.comp_apply, hσU, Scheme.Hom.comp_apply]
    rfl
  have hset : Set.range σl.base = U.ι.base ⁻¹' (Set.range (pullback.diagonal f.left).base ∩
      (pullback.fst f.left f.left ≫ f.left).base ⁻¹' V) := by
    rw [← himage]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, (hσx x).symm⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨⟨z, hz⟩, U.ι.isOpenEmbedding.injective ?_⟩
      rw [hσx]
      exact hzy
  have hopen : IsOpen (Set.range σl.base) := by
    rw [hset]
    exact hV.preimage U.ι.base.hom.continuous
  have h₃ := isZero_upperStar_of_isZero_lowerStar_of_isOpen_range p' σ hσ hopen _ h₂
  have key (g : opensOver O ⟶ Z) (hg : g = opensOverι O)
      (h : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj F)) :
      IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι O)).obj F) := by
    subst hg
    exact h
  exact key _ hσ₂ (h₃.of_iso ((boundedConstructibleUpperStarComp _ ℓ (σ ≫ opensOverι U)
    (fibreSquareSnd f)).app F ≪≫ (boundedConstructibleUpperStarComp _ ℓ σ (opensOverι U)).app _))

end Diagonal

end AlgebraicGeometry.ProEtale.CondensedRing
