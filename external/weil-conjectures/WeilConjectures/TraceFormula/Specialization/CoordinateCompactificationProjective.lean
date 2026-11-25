/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint
public import WeilConjectures.TraceFormula.Specialization.CoordinateCompactification
public import WeilConjectures.TraceFormula.Specialization.GenericSliceHom
public import WeilConjectures.TraceFormula.Specialization.NearbyTwistProjectiveLineSlice

/-!

# Projective compactification of a trait model along a coordinate

Let `S = Spec k'⟦t⟧` be the trait and `η` its generic point.

* `NearbyCyclesModel.exists_closedImmersion_comp_smooth_of_isPullback`: a morphism `f : Z ⟶ T`
  over a field which is the base change of a projective morphism `e ≫ (ℙ(n; B) ⟶ B)`, `e` a
  closed immersion, is a closed immersion followed by a proper morphism smooth of relative
  dimension `d` (`Nat.card n = d + 1`). This is the shape of the morphisms `b = i ≫ p` of
  `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projective_of_comp_eq`.
* `IsTraitModelOfGenericBase.exists_coordinateCompactification_of_closedImmersion`:
  the conclusion of
  `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification` from an open
  immersion `𝒳 ⟶ Z` into a closed subscheme `Z ⊆ ℙ(n; ℙ¹_S)` over `b ≫ χ : 𝒳 ⟶ ℙ¹_S`, with in
  addition the morphisms `b̄₁ : X̄₁ ⟶ ℙ¹_η`, `b̄₂ : X̄' ⟶ ℙ¹_{k'}` of the compactification written
  as closed immersions followed by smooth proper morphisms.
* `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_projectiveCoordinateCompactification`: the
  same for a *quasi-projective* total space, given by an immersion `e : 𝒳 ⟶ ℙ(n; S)` over `S`:
  `Z` is the scheme-theoretic closure of the graph `𝒳 ⟶ ℙ(n; S) ×_S ℙ¹_S = ℙ(n; ℙ¹_S)` of
  `b ≫ χ`.
* `NearbyCyclesModel.isIso_upperShriekBaseChangeOfMap_projectiveLineGenericSlice`,
  `NearbyCyclesModel.isIso_upperShriekBaseChangeOfMap_projectiveLineSpecialSlice`: for `x`
  transcendental over `k'` and `b = i ≫ p` projective over `ℙ¹_η` (resp. `ℙ¹_{k'}`), the base
  change maps `γ` of `Rb^!` along the slices `c_P`, `p_P` of the projective line are invertible.
  These are the hypotheses on `γ` of `NearbyCyclesModel.exists_twist_of_slice_of_composition_law`
  for `P = ℙ¹_S`.

## Implementation notes

The Nagata compactification of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification`
is not known to be projective over `ℙ¹_S`, and Chow's lemma (`AlgebraicGeometry.ChowModification`)
only produces a projective modification which is an isomorphism over a dense open, which need not
contain `𝒳`. Hence the hypothesis that `𝒳` be quasi-projective over `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme ProjectiveSpace ProjectiveLine

section Factor

variable {F : Type u} [Field F] {Z T : Over (Spec (.of F))} [LocallyOfFiniteType T.hom]
  [QuasiCompact T.hom] [IsSeparated T.hom]

/-- **Base changes of projective morphisms are projective**: if `f : Z ⟶ T` over a field is the
base change of `e ≫ (ℙ(n; B) ⟶ B)` with `e` a closed immersion, then `f = i ≫ p` with `i` a
closed immersion into `ℙ(n; T)` and `p : ℙ(n; T) ⟶ T` proper and smooth of relative dimension
`d`, `Nat.card n = d + 1`. -/
theorem exists_closedImmersion_comp_smooth_of_isPullback (f : Z ⟶ T) {n : Type u} [Finite n]
    {d : ℕ} (hn : Nat.card n = d + 1) {A B : Scheme.{u}} {πZ : Z.left ⟶ A} {πT : T.left ⟶ B}
    {G : A ⟶ B} (h : IsPullback πZ f.left G πT) (e : A ⟶ ℙ(n; B)) [IsClosedImmersion e]
    (he : e ≫ ℙ(n; B) ↘ B = G) :
    ∃ (Y : Over (Spec (.of F))) (_ : LocallyOfFiniteType Y.hom) (_ : QuasiCompact Y.hom)
      (_ : IsSeparated Y.hom) (i : Z ⟶ Y) (p : Y ⟶ T), IsClosedImmersion i.left ∧
        IsProper p.left ∧ SmoothOfRelativeDimension d p.left ∧ i ≫ p = f := by
  subst he
  have w : f.left ≫ πT = (πZ ≫ e) ≫ ℙ(n; B) ↘ B := by
    rw [Category.assoc]
    exact h.w.symm
  have hl := isPullback_liftBaseChange (n := n) f.left h w
  let Y : Over (Spec (.of F)) := Over.mk (ℙ(n; T.left) ↘ T.left ≫ T.hom)
  let p : Y ⟶ T := Over.homMk (ℙ(n; T.left) ↘ T.left) rfl
  let i : Z ⟶ Y := Over.homMk (liftBaseChange f.left (πZ ≫ e) w) (by
    change liftBaseChange _ _ _ ≫ ℙ(n; T.left) ↘ T.left ≫ T.hom = Z.hom
    rw [liftBaseChange_over_assoc, Over.w f])
  have hi : IsClosedImmersion i.left := MorphismProperty.of_isPullback hl inferInstance
  refine ⟨Y, inferInstanceAs (LocallyOfFiniteType (_ ≫ _)),
    inferInstanceAs (QuasiCompact (_ ≫ _)), inferInstanceAs (IsSeparated (_ ≫ _)), i, p, hi,
    inferInstanceAs (IsProper (ℙ(n; T.left) ↘ T.left)),
    ProjectiveSpace.smoothOfRelativeDimension n T.left hn, ?_⟩
  apply Over.OverMorphism.ext
  change liftBaseChange f.left (πZ ≫ e) w ≫ ℙ(n; T.left) ↘ T.left = f.left
  exact liftBaseChange_over f.left (πZ ≫ e) w

end Factor

section Compactification

variable {k' : Type u} [Field k']

/-- **Compactifying a trait model along a coordinate, projectively**: the conclusion of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification`, from an open
immersion `ι : 𝒳 ⟶ Z` and a closed immersion `e : Z ⟶ ℙ(n; ℙ¹_S)` with
`ι ≫ e ≫ (ℙ(n; ℙ¹_S) ⟶ ℙ¹_S) = b ≫ χ`; the total space of `M̄` is `Z`. In addition, the maps
`b̄₁ : X̄₁ ⟶ ℙ¹_η` and `b̄₂ : X̄' ⟶ ℙ¹_{k'}` of `b̄` are closed immersions `i₁`, `i₂` followed by
proper morphisms `p₁`, `p₂` smooth of relative dimension `d`, `Nat.card n = d + 1`. -/
theorem IsTraitModelOfGenericBase.exists_coordinateCompactification_of_closedImmersion
    {X₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ (𝟙 _) q g)
    (hfull : ∃ w : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom (𝟙 _), IsIso w ∧
      w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ = M.ε)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) {n : Type u} [Finite n] {d : ℕ}
    (hn : Nat.card n = d + 1) {Zc : Scheme.{u}} (ci : M.total ⟶ Zc) [IsOpenImmersion ci]
    (ec : Zc ⟶ ℙ(n; ProjectiveLine (trait k'))) [IsClosedImmersion ec]
    (hci : ci ≫ ec ≫ ℙ(n; ProjectiveLine (trait k')) ↘ ProjectiveLine (trait k') =
      b ≫ coordChart (trait k')) :
    ∃ (Xc : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)))
      (_ : LocallyOfFiniteType Xc.hom) (_ : QuasiCompact Xc.hom) (_ : IsSeparated Xc.hom)
      (_ : IsProper (CondensedRing.toPoint Xc).left) (Xc' : Over (Spec (.of k')))
      (_ : LocallyOfFiniteType Xc'.hom) (_ : QuasiCompact Xc'.hom) (_ : IsSeparated Xc'.hom)
      (_ : IsProper (CondensedRing.toPoint Xc').left) (Mc : NearbyCyclesModel Xc.left Xc'.left)
      (qc : Mc.total ⟶ trait k') (gc : Mc.generic ⟶ Spec (.of (traitGenericField k')))
      (_ : Mc.IsTraitModelOfGenericBase Xc (𝟙 _) qc gc) (_ : IsProper qc)
      (_ : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ 𝟙 _))
      (b₁ : Xc ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))))
      (_ : IsProper b₁.left) (b₂ : Xc' ⟶ overProjectiveLine (point k')) (_ : IsProper b₂.left)
      (bc : Mc.Hom (projectiveLineModel k') b₁.left b₂.left)
      (_ : qc = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
      (_ : gc = bc.generic ≫
        (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k'))))
      (U : Mc.total.Opens) (_ : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
      (_ : QuasiCompact U.ι)
      (_ : LocallyOfFiniteType (Mc.restrictSpecialFibre U).hom)
      (_ : QuasiCompact (Mc.restrictSpecialFibre U).hom)
      (_ : IsSeparated (Mc.restrictSpecialFibre U).hom)
      (bW : (Mc.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
      (_ : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qc)
      (_ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
      (j : X₁ ⟶ Xc) (_ : IsOpenImmersion j.left) (j' : X' ⟶ Mc.restrictSpecialFibre U)
      (_ : IsOpenImmersion j'.left) (φ : M.Hom (Mc.restrictOpen U) j.left j'.left)
      (_ : IsOpenImmersion φ.total)
      (Y₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)))
      (_ : LocallyOfFiniteType Y₁.hom) (_ : QuasiCompact Y₁.hom) (_ : IsSeparated Y₁.hom)
      (i₁ : Xc ⟶ Y₁) (p₁ : Y₁ ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))))
      (Y₂ : Over (Spec (.of k'))) (_ : LocallyOfFiniteType Y₂.hom) (_ : QuasiCompact Y₂.hom)
      (_ : IsSeparated Y₂.hom) (i₂ : Xc' ⟶ Y₂) (p₂ : Y₂ ⟶ overProjectiveLine (point k')),
      IsPullback φ.generic M.j (Mc.restrictOpen U).j φ.total ∧ q = φ.total ≫ U.ι ≫ qc ∧
        g = φ.generic ≫ (Mc.j ⁻¹ᵁ U).ι ≫ gc ∧ φ.total ≫ bW = b ∧
        (IsClosedImmersion i₁.left ∧ IsProper p₁.left ∧ SmoothOfRelativeDimension d p₁.left ∧
          i₁ ≫ p₁ = b₁) ∧
        (IsClosedImmersion i₂.left ∧ IsProper p₂.left ∧ SmoothOfRelativeDimension d p₂.left ∧
          i₂ ≫ p₂ = b₂) := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := hfull
  have hM := h.isTraitModelOver
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  let χ := coordChart (trait k')
  let πS := ProjectiveLine (trait k') ↘ trait k'
  let f : M.total ⟶ ProjectiveLine (trait k') := b ≫ χ
  have hf : f ≫ πS = q := by
    simp only [f, πS, χ, Category.assoc, coordChart_over, hb]
  -- the compactification `Z ⟶ ℙ(n; ℙ¹_S) ⟶ ℙ¹_S`
  let cg : Zc ⟶ ProjectiveLine (trait k') :=
    ec ≫ ℙ(n; ProjectiveLine (trait k')) ↘ ProjectiveLine (trait k')
  have : IsProper cg := inferInstanceAs (IsProper (ec ≫ _))
  have hci' : ci ≫ cg = f := hci
  let qc : Zc ⟶ trait k' := cg ≫ πS
  have : IsProper qc := inferInstance
  have hciq : ci ≫ qc = q := by rw [← Category.assoc, hci', hf]
  let Mc := traitFibreModel qc
  have hc := isTraitModelOfGenericBase_traitFibreModel qc
  have hcM := hc.isTraitModelOver
  -- the morphism of models `b̄ : M̄ ⟶ ℙ¹_S`
  let ιS := traitGenericSpec k'
  let γ := traitGenericPointToSpec k'
  have hγ : γ ≫ ιS = traitGenericPoint k' := traitGenericPointToSpec_traitGenericSpec k'
  have hPη := isPullback_map (ULift.{u} (Fin 2)) ιS
  have hPΩ := isPullback_map (ULift.{u} (Fin 2)) (traitGenericPoint k')
  have hPs := isPullback_map (ULift.{u} (Fin 2)) (traitClosedPoint k')
  let b₁l : pullback qc ιS ⟶ ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) :=
    hPη.lift (pullback.fst _ _ ≫ cg) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  let b₂l : pullback qc (traitClosedPoint k') ⟶ ProjectiveLine (Spec (.of k')) :=
    hPs.lift (pullback.fst _ _ ≫ cg) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  let bgen : pullback qc (traitGenericPoint k') ⟶
      ProjectiveLine (Spec (.of (traitGenericField k'))) :=
    hPΩ.lift (pullback.fst _ _ ≫ cg) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  let b₁ : traitGenericBase qc ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))) :=
    Over.homMk b₁l (by
      change b₁l ≫ (_ ↘ _ ≫ 𝟙 _) = _
      rw [Category.comp_id]
      exact hPη.lift_snd _ _ _)
  let b₂ : traitStdSpecialFibre qc ⟶ overProjectiveLine (point k') :=
    Over.homMk b₂l (by
      change b₂l ≫ (_ ↘ _ ≫ 𝟙 _) = _
      rw [Category.comp_id]
      exact hPs.lift_snd _ _ _)
  have hb₁ : IsPullback (pullback.fst qc ιS) b₁l cg (ProjectiveSpace.map _ ιS) := by
    refine IsPullback.of_bot ?_ (hPη.lift_fst _ _ _).symm hPη
    rw [hPη.lift_snd]
    exact IsPullback.of_hasPullback qc ιS
  have hb₂ : IsPullback (pullback.fst qc (traitClosedPoint k')) b₂l cg
      (ProjectiveSpace.map _ (traitClosedPoint k')) := by
    refine IsPullback.of_bot ?_ (hPs.lift_fst _ _ _).symm hPs
    rw [hPs.lift_snd]
    exact IsPullback.of_hasPullback qc (traitClosedPoint k')
  have hb₁p : IsProper b₁.left := MorphismProperty.of_isPullback hb₁ inferInstance
  have hb₂p : IsProper b₂.left := MorphismProperty.of_isPullback hb₂ inferInstance
  obtain ⟨Y₁, hY₁a, hY₁b, hY₁c, i₁, p₁, hi₁⟩ :=
    exists_closedImmersion_comp_smooth_of_isPullback b₁ hn hb₁ ec rfl
  obtain ⟨Y₂, hY₂a, hY₂b, hY₂c, i₂, p₂, hi₂⟩ :=
    exists_closedImmersion_comp_smooth_of_isPullback b₂ hn hb₂ ec rfl
  let bc : Mc.Hom (projectiveLineModel k') b₁.left b₂.left :=
    { total := cg
      generic := bgen
      comm_j := hPΩ.lift_fst _ _ _
      comm_i := hPs.lift_fst _ _ _
      comm_ε := by
        change bgen ≫ ProjectiveSpace.map _ γ = Mc.ε ≫ b₁l
        apply hPη.hom_ext
        · rw [Category.assoc, Category.assoc, hPη.lift_fst, ← ProjectiveSpace.map_comp, hγ,
            traitFibreModel_ε, pullback.lift_fst_assoc]
          exact hPΩ.lift_fst _ _ _
        · rw [Category.assoc, Category.assoc, hPη.lift_snd, traitFibreModel_ε, pullback.lift_snd,
            ProjectiveSpace.map_over, ← Category.assoc, hPΩ.lift_snd] }
  have hbcg : pullback.snd qc (traitGenericPoint k') = bc.generic ≫
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘
        Spec (.of (traitGenericField k'))) := (hPΩ.lift_snd _ _ _).symm
  -- the open `U = b̄⁻¹(𝔸¹_S)` and its coordinate
  let O := χ.opensRange
  let U : Mc.total.Opens := cg ⁻¹ᵁ O
  have hRU := isPullback_morphismRestrict cg O
  have : QuasiCompact O.ι := by
    rw [← χ.isoOpensRange_inv_comp]
    infer_instance
  have hUqc : QuasiCompact U.ι := MorphismProperty.of_isPullback hRU inferInstance
  have hRj := isPullback_morphismRestrict Mc.j U
  have hRi := isPullback_morphismRestrict Mc.i U
  have : QuasiCompact (Mc.i ⁻¹ᵁ U).ι := MorphismProperty.of_isPullback hRi hUqc
  have hW := hc.restrictOpen U
  have hWM := hW.isTraitModelOver
  let bW : (Mc.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k') :=
    (cg ∣_ O) ≫ χ.isoOpensRange.inv
  have hbWχ : bW ≫ χ = U.ι ≫ cg := by
    change ((cg ∣_ O) ≫ χ.isoOpensRange.inv) ≫ χ = _
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    exact hRU.w
  have hbW : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qc := by
    rw [← coordChart_over, ← Category.assoc]
    change (bW ≫ χ) ≫ πS = _
    rw [hbWχ, Category.assoc]
  -- the open immersion of models `M ⟶ W`
  let φt : M.total ⟶ U := IsOpenImmersion.lift U.ι ci (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change cg (ci y) ∈ O
    rw [← Scheme.Hom.comp_apply, hci']
    exact ⟨b y, rfl⟩)
  have hφU : φt ≫ U.ι = ci := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion φt := IsOpenImmersion.of_comp φt U.ι
  have hbb : φt ≫ bW = b := by
    rw [← cancel_mono χ, Category.assoc, hbWχ, reassoc_of% hφU, hci']
  let genVc : M.generic ⟶ pullback qc (traitGenericPoint k') :=
    pullback.lift (M.j ≫ ci) g (by rw [Category.assoc, hciq, hM.isPullback_j.w])
  let φg : M.generic ⟶ (Mc.restrictOpen U).generic :=
    hRj.lift (M.j ≫ φt) genVc (by
      rw [Category.assoc, hφU]
      exact (pullback.lift_fst _ _ _).symm)
  have hφg : φg ≫ (Mc.j ⁻¹ᵁ U).ι = genVc := hRj.lift_snd _ _ _
  let spVc : X'.left ⟶ pullback qc (traitClosedPoint k') :=
    pullback.lift (M.i ≫ ci) X'.hom (by rw [Category.assoc, hciq, hM.isPullback_i.w])
  let j'l : X'.left ⟶ (Mc.restrictSpecialFibre U).left :=
    hRi.lift (M.i ≫ φt) spVc (by
      rw [Category.assoc, hφU]
      exact (pullback.lift_fst _ _ _).symm)
  let j' : X' ⟶ Mc.restrictSpecialFibre U :=
    Over.homMk j'l (by
      change j'l ≫ (Mc.i ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = _
      rw [hRi.lift_snd_assoc]
      exact pullback.lift_snd _ _ _)
  let e : pullback q ιS ⟶ X₁.left := w ≫ pullback.fst _ _
  have : IsIso e := inferInstance
  have he : e ≫ X₁.hom = pullback.snd _ _ := by
    rw [Category.assoc, pullback.condition, Category.comp_id, hw₁]
  let pm : pullback q ιS ⟶ pullback qc ιS :=
    pullback.map _ _ _ _ ci (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hciq]) (by simp)
  have hpm₁ : pm ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ci := pullback.lift_fst _ _ _
  have hpm₂ : pm ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
  have : IsOpenImmersion pm := inferInstance
  let j : X₁ ⟶ traitGenericBase qc :=
    Over.homMk (inv e ≫ pm) (by
      change (inv e ≫ pm) ≫ pullback.snd _ _ = _
      rw [Category.assoc, pullback.lift_snd, Category.comp_id, IsIso.inv_comp_eq, he])
  have hsε : genericFibreInclusion M q g hM.isPullback_j.w ≫ e = M.ε := hw₂
  let φ : M.Hom (Mc.restrictOpen U) j.left j'.left :=
    { total := φt
      generic := φg
      comm_j := hRj.lift_fst _ _ _
      comm_i := hRi.lift_fst _ _ _
      comm_ε := by
        change φg ≫ (Mc.j ⁻¹ᵁ U).ι ≫ Mc.ε = M.ε ≫ inv e ≫ pm
        rw [reassoc_of% hφg, ← hsε, Category.assoc, IsIso.hom_inv_id_assoc]
        apply pullback.hom_ext
        · rw [Category.assoc, traitFibreModel_ε, pullback.lift_fst, Category.assoc, hpm₁,
            genericFibreInclusion_fst_assoc]
          exact pullback.lift_fst _ _ _
        · rw [Category.assoc, traitFibreModel_ε, pullback.lift_snd, Category.assoc, hpm₂,
            Category.comp_id, genericFibreInclusion_snd]
          exact pullback.lift_snd_assoc _ _ _ _ }
  have hφq : q = φt ≫ U.ι ≫ qc := by rw [reassoc_of% hφU, hciq]
  have hφgq : g = φg ≫ (Mc.j ⁻¹ᵁ U).ι ≫ pullback.snd qc (traitGenericPoint k') := by
    rw [reassoc_of% hφg]
    exact (pullback.lift_snd _ _ _).symm
  have hφpb : IsPullback φg M.j (Mc.restrictOpen U).j φt := by
    refine IsPullback.of_right ?_ (hRj.lift_fst _ _ _) hWM.isPullback_j.flip
    rw [← hφgq, ← hφq]
    exact hM.isPullback_j.flip
  have hj'pb : IsPullback j'l M.i (Mc.restrictOpen U).i φt := by
    refine IsPullback.of_right ?_ (hRi.lift_fst _ _ _) hWM.isPullback_i.flip
    rw [← hφq]
    convert hM.isPullback_i.flip using 1
    exact Over.w j'
  have : IsOpenImmersion j'l := MorphismProperty.of_isPullback hj'pb.flip inferInstance
  exact ⟨traitGenericBase qc, inferInstance, inferInstance, inferInstance,
    isProper_toPoint_traitGenericBase qc, traitStdSpecialFibre qc, inferInstance, inferInstance,
    inferInstance, isProper_toPoint_traitStdSpecialFibre qc, Mc, qc, _, hc, inferInstance,
    isPullback_traitFibreModel_ε qc, b₁, hb₁p, b₂, hb₂p, bc, rfl, hbcg, U, rfl, hUqc,
    inferInstanceAs (LocallyOfFiniteType ((Mc.i ⁻¹ᵁ U).ι ≫ _)),
    inferInstanceAs (QuasiCompact ((Mc.i ⁻¹ᵁ U).ι ≫ _)),
    inferInstanceAs (IsSeparated ((Mc.i ⁻¹ᵁ U).ι ≫ _)), bW, hbW, hbWχ, j,
    inferInstanceAs (IsOpenImmersion (inv e ≫ pm)), j', ‹_›, φ, ‹_›, Y₁, hY₁a, hY₁b, hY₁c, i₁,
    p₁, Y₂, hY₂a, hY₂b, hY₂c, i₂, p₂, hφpb, hφq, hφgq, hbb, hi₁, hi₂⟩

/-- **Compactifying a quasi-projective trait model along a coordinate, projectively**: let `M` be
as in `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification`, and
assume that its total space is quasi-projective over `S`: there is an immersion
`e : 𝒳 ⟶ ℙ(n; S)` over `S`. Then the conclusion of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification_of_closedImmersion`
holds: `M̄` is the scheme-theoretic closure of the graph `𝒳 ⟶ ℙ(n; ℙ¹_S)` of `b ≫ χ` (an
immersion, quasi-compact since `𝒳` is quasi-compact over `S`), and `b̄₁`, `b̄₂` are closed
immersions followed by proper morphisms smooth of relative dimension `d`, `Nat.card n = d + 1`. -/
theorem IsTraitModelOfGenericBase.exists_projectiveCoordinateCompactification
    {X₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ (𝟙 _) q g)
    (hfull : ∃ w : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom (𝟙 _), IsIso w ∧
      w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ = M.ε)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) {n : Type u} [Finite n] {d : ℕ}
    (hn : Nat.card n = d + 1) (e : M.total ⟶ ℙ(n; trait k')) [IsImmersion e]
    (he : e ≫ ℙ(n; trait k') ↘ trait k' = q) :
    ∃ (Xc : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)))
      (_ : LocallyOfFiniteType Xc.hom) (_ : QuasiCompact Xc.hom) (_ : IsSeparated Xc.hom)
      (_ : IsProper (CondensedRing.toPoint Xc).left) (Xc' : Over (Spec (.of k')))
      (_ : LocallyOfFiniteType Xc'.hom) (_ : QuasiCompact Xc'.hom) (_ : IsSeparated Xc'.hom)
      (_ : IsProper (CondensedRing.toPoint Xc').left) (Mc : NearbyCyclesModel Xc.left Xc'.left)
      (qc : Mc.total ⟶ trait k') (gc : Mc.generic ⟶ Spec (.of (traitGenericField k')))
      (_ : Mc.IsTraitModelOfGenericBase Xc (𝟙 _) qc gc) (_ : IsProper qc)
      (_ : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ 𝟙 _))
      (b₁ : Xc ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))))
      (_ : IsProper b₁.left) (b₂ : Xc' ⟶ overProjectiveLine (point k')) (_ : IsProper b₂.left)
      (bc : Mc.Hom (projectiveLineModel k') b₁.left b₂.left)
      (_ : qc = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
      (_ : gc = bc.generic ≫
        (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k'))))
      (U : Mc.total.Opens) (_ : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
      (_ : QuasiCompact U.ι)
      (_ : LocallyOfFiniteType (Mc.restrictSpecialFibre U).hom)
      (_ : QuasiCompact (Mc.restrictSpecialFibre U).hom)
      (_ : IsSeparated (Mc.restrictSpecialFibre U).hom)
      (bW : (Mc.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
      (_ : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qc)
      (_ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
      (j : X₁ ⟶ Xc) (_ : IsOpenImmersion j.left) (j' : X' ⟶ Mc.restrictSpecialFibre U)
      (_ : IsOpenImmersion j'.left) (φ : M.Hom (Mc.restrictOpen U) j.left j'.left)
      (_ : IsOpenImmersion φ.total)
      (Y₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)))
      (_ : LocallyOfFiniteType Y₁.hom) (_ : QuasiCompact Y₁.hom) (_ : IsSeparated Y₁.hom)
      (i₁ : Xc ⟶ Y₁) (p₁ : Y₁ ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))))
      (Y₂ : Over (Spec (.of k'))) (_ : LocallyOfFiniteType Y₂.hom) (_ : QuasiCompact Y₂.hom)
      (_ : IsSeparated Y₂.hom) (i₂ : Xc' ⟶ Y₂) (p₂ : Y₂ ⟶ overProjectiveLine (point k')),
      IsPullback φ.generic M.j (Mc.restrictOpen U).j φ.total ∧ q = φ.total ≫ U.ι ≫ qc ∧
        g = φ.generic ≫ (Mc.j ⁻¹ᵁ U).ι ≫ gc ∧ φ.total ≫ bW = b ∧
        (IsClosedImmersion i₁.left ∧ IsProper p₁.left ∧ SmoothOfRelativeDimension d p₁.left ∧
          i₁ ≫ p₁ = b₁) ∧
        (IsClosedImmersion i₂.left ∧ IsProper p₂.left ∧ SmoothOfRelativeDimension d p₂.left ∧
          i₂ ≫ p₂ = b₂) := by
  have hM := h.isTraitModelOver
  have := hM.quasiCompact
  let πS := ProjectiveLine (trait k') ↘ trait k'
  have w : (b ≫ coordChart (trait k')) ≫ πS = e ≫ ℙ(n; trait k') ↘ trait k' := by
    rw [he, Category.assoc, coordChart_over, hb]
  -- the graph `𝒳 ⟶ ℙ(n; S) ×_S ℙ¹_S = ℙ(n; ℙ¹_S)` of `b ≫ χ`
  let γ : M.total ⟶ ℙ(n; ProjectiveLine (trait k')) := liftBaseChange (g := πS) _ e w
  have hγ : γ ≫ ℙ(n; ProjectiveLine (trait k')) ↘ ProjectiveLine (trait k') =
      b ≫ coordChart (trait k') := liftBaseChange_over _ _ _
  have : QuasiCompact (γ ≫ ℙ(n; ProjectiveLine (trait k')) ↘ ProjectiveLine (trait k') ≫ πS) := by
    rw [reassoc_of% hγ]
    change QuasiCompact (b ≫ coordChart (trait k') ≫ ProjectiveLine (trait k') ↘ trait k')
    rw [coordChart_over, hb]
    infer_instance
  have : QuasiCompact γ := QuasiCompact.of_comp γ
    (ℙ(n; ProjectiveLine (trait k')) ↘ ProjectiveLine (trait k') ≫ πS)
  exact h.exists_coordinateCompactification_of_closedImmersion hfull hb hn γ.toImage γ.imageι
    (by rw [γ.toImage_imageι_assoc, hγ])

end Compactification

section BaseChangeIso

variable (ℓ : ℕ) [Fact ℓ.Prime] {k' K : Type u} [Field k'] [Field K] [Algebra k' K] {x : K}
  (hx : Transcendental k' x) {d : ℕ}

include hx in
/-- **Base change of `Rb^!` along the generic slice of `ℙ¹`**: for `x` transcendental over `k'`
and `b = i ≫ p : Z ⟶ Y ⟶ ℙ¹_η` a closed immersion followed by a proper morphism smooth of
relative dimension `d`, the base change map `γ` of `Rb^!` along the slice
`c_P : Spec Frac K⟦t⟧ ⟶ ℙ¹_η` (`NearbyCyclesModel.projectiveLineGenericSlice`) is invertible:
`c_P` is the field extension `Frac K⟦t⟧ / Frac k'⟦t⟧(x)` followed by the weakly étale generic
point of `𝔸¹_η` and the affine chart. -/
theorem isIso_upperShriekBaseChangeOfMap_projectiveLineGenericSlice
    [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
    [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)]
    [Fact (ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1))
      (FractionRing (PowerSeries k'))))).Prime]
    [Fact (ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1))
      (FractionRing (PowerSeries k')))) ≠ ℓ)]
    [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
    [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]
    {Z Y : Over (Spec (.of (FractionRing (PowerSeries k'))))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (i : Z ⟶ Y)
    (p : Y ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))))
    [IsClosedImmersion i.left] [IsProper p.left] [SmoothOfRelativeDimension d p.left]
    {Z' : Over (Spec (.of (FractionRing (PowerSeries K))))} [LocallyOfFiniteType Z'.hom]
    [QuasiCompact Z'.hom] [IsSeparated Z'.hom] {f' : Z' ⟶ point (FractionRing (PowerSeries K))}
    [IsProper f'.left] {π : Z'.left ⟶ Z.left}
    (sq : IsPullback π f'.left (i ≫ p).left (projectiveLineGenericSlice x)) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    IsIso (upperShriekBaseChangeOfMap ℓ sq) := by
  let := (traitGenericSliceLift hx).toAlgebra
  have : IsIso (point (FractionRing (PowerSeries K))).hom := IsIso.id _
  refine isIso_upperShriekBaseChangeOfMap_of_projective_of_isIso_hom ℓ d
    (affineLineGenericPoint (FractionRing (PowerSeries k')) ≫ (affineLineReindexIso _).hom ≫
      ProjectiveLine.affineChart _) ?_ sq
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp, projectiveLineGenericSlice_eq,
    traitGenericSlice_eq_comp_affineLineGenericPoint hx, Category.assoc]
  rfl

include hx in
/-- **Base change of `Rb^!` along the special slice of `ℙ¹`**: for `x` transcendental over `k'`
and `b = i ≫ p : Z ⟶ Y ⟶ ℙ¹_{k'}` a closed immersion followed by a proper morphism smooth of
relative dimension `d`, the base change map `γ` of `Rb^!` along the slice `p_P : Spec K ⟶ ℙ¹_{k'}`
(`NearbyCyclesModel.projectiveLineSpecialSlice`) is invertible: `p_P` is the field extension
`K / k'(x)` followed by the weakly étale generic point of `𝔸¹_{k'}` and the affine chart. -/
theorem isIso_upperShriekBaseChangeOfMap_projectiveLineSpecialSlice
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    [Fact (ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k'))).Prime]
    [Fact (ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k')) ≠ ℓ)]
    [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
    {Z Y : Over (Spec (.of k'))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (i : Z ⟶ Y) (p : Y ⟶ overProjectiveLine (point k'))
    [IsClosedImmersion i.left] [IsProper p.left] [SmoothOfRelativeDimension d p.left]
    {Z' : Over (Spec (.of K))} [LocallyOfFiniteType Z'.hom]
    [QuasiCompact Z'.hom] [IsSeparated Z'.hom] {f' : Z' ⟶ point K}
    [IsProper f'.left] {π : Z'.left ⟶ Z.left}
    (sq : IsPullback π f'.left (i ≫ p).left (projectiveLineSpecialSlice x)) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    IsIso (upperShriekBaseChangeOfMap ℓ sq) := by
  let := (transcendentalFractionLift hx).toAlgebra
  have : IsIso (point K).hom := IsIso.id _
  refine isIso_upperShriekBaseChangeOfMap_of_projective_of_isIso_hom ℓ d
    (affineLineGenericPoint k' ≫ (affineLineReindexIso _).hom ≫ ProjectiveLine.affineChart _) ?_ sq
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp, projectiveLineSpecialSlice_eq,
    traitSlicePoint_eq_comp_affineLineGenericPoint hx, Category.assoc]
  rfl

end BaseChangeIso

section SliceData

variable {k' K : Type u} [Field k'] [Field K] [Algebra k' K] (x : K)

/-- The two presentations of the affine chart of `ℙ¹` on `𝔸(ULift (Fin 1); S)` agree. -/
lemma coordChart_eq_affineLineReindexIso (S : Scheme.{u}) :
    coordChart S = (affineLineReindexIso S).hom ≫ ProjectiveLine.affineChart S := by
  rw [coordChart, AffineSpace.reindexIso_inv, AffineSpace.reindexIso_hom]
  have : (⇑(Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit.{u + 1}).symm : PUnit → ULift (Fin 1)) =
      ⇑(Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1))) := Subsingleton.elim _ _
  rw [this]

/-- The slice of the projective line is the generic slice followed by the affine chart
`AlgebraicGeometry.ProjectiveLine.coordChart`. -/
lemma projectiveLineSlice_eq_coordChart :
    projectiveLineSlice (k' := k') x = traitSlice x ≫ coordChart (trait k') := by
  rw [projectiveLineSlice, coordChart_eq_affineLineReindexIso]

section TraitHom

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- The structure morphism `X₂ ⟶ Spec Frac K⟦t⟧` of the base of the generic slice, as a morphism
to the point. -/
noncomputable def genericSliceBaseToPoint :
    genericSliceBase x hb ⟶ point (FractionRing (PowerSeries K)) :=
  Over.homMk (genericSliceBase x hb).hom (Category.comp_id _)

/-- The structure morphism `𝒳''_s ⟶ Spec K` of the special fibre of the generic slice, as a
morphism to the point. -/
noncomputable def baseChangeSpecialToPoint : baseChangeSpecial b (traitSlice x) ⟶ point K :=
  Over.homMk (baseChangeSpecial b (traitSlice x)).hom (Category.comp_id _)

/-- **The generic slice model over the slice trait** `φ'' : M'' ⟶ P''`: the projection
`𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ Spec K⟦t⟧` as a morphism of models from the generic slice model
(`NearbyCyclesModel.genericSliceModel`) to the slice trait
(`NearbyCyclesModel.sliceTraitPointModel`),
(`NearbyCyclesModel.sliceTraitPointModel`),
over the structure morphisms of the base and of the special fibre. -/
noncomputable def genericSliceToTraitHom :
    (genericSliceModel x hb).Hom (sliceTraitPointModel K) (genericSliceBaseToPoint x hb).left
      (baseChangeSpecialToPoint (b := b) x).left where
  total := pullback.snd b (traitSlice x)
  generic := pullback.snd _ _
  comm_j := pullback.condition.symm
  comm_i := pullback.condition.symm
  comm_ε := by
    change pullback.snd _ _ ≫ (traitGenericPointToSpec K ≫ 𝟙 _) =
      (pullback.lift _ _ _ ≫ (genericSliceFibreIso x hb).hom) ≫ (genericSliceBase x hb).hom
    rw [Category.assoc, genericSliceFibreIso_hom_over, pullback.lift_snd, Category.comp_id]

@[simp]
lemma genericSliceToTraitHom_total :
    (genericSliceToTraitHom x hb).total = pullback.snd b (traitSlice x) := rfl

end TraitHom

variable {Xc : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
  {Xc' : Over (Spec (.of k'))} {N : NearbyCyclesModel Xc.left Xc'.left} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {b₁ : Xc ⟶ overProjectiveLine (point (FractionRing (PowerSeries k')))}
  {b₂ : Xc' ⟶ overProjectiveLine (point k')} (bc : N.Hom (projectiveLineModel k') b₁.left b₂.left)
  {U : N.total.Opens} {bW : (N.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}

/-- **The slice of `W = b̄⁻¹(𝔸¹_S)` is the slice of `M̄`**: for the open `U = b̄⁻¹(𝔸¹_S)` and the
coordinate `b_W` of `W` with `b_W ≫ χ = b̄|_U`, the square
`𝒳'' = W ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳̄`, `Spec K⟦t⟧ ⟶ ℙ¹_S` over `b̄` is cartesian. -/
lemma isPullback_genericSlice_projectiveLineSlice
    (hU : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
    (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total) :
    IsPullback (pullback.fst bW (traitSlice x) ≫ U.ι) (pullback.snd bW (traitSlice x)) bc.total
      (projectiveLineSlice x) := by
  subst hU
  let χ := coordChart (trait k')
  let O := χ.opensRange
  have hRU := isPullback_morphismRestrict bc.total O
  have hχ : χ.isoOpensRange.hom ≫ O.ι = χ := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Iso.hom_inv_id_assoc]
  have hb : bW ≫ χ.isoOpensRange.hom = bc.total ∣_ O := by
    rw [← cancel_mono O.ι, Category.assoc, hχ, hRU.w]
    exact hbWχ
  have hQ : IsPullback (bc.total ⁻¹ᵁ O).ι bW bc.total χ := by
    have h₁ : IsPullback (𝟙 _) bW (bc.total ∣_ O) χ.isoOpensRange.hom :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hb]⟩
    have h := h₁.paste_horiz hRU.flip
    rw [Category.id_comp, hχ] at h
    exact h
  rw [projectiveLineSlice_eq_coordChart]
  exact (IsPullback.of_hasPullback bW (traitSlice x)).paste_horiz hQ

variable {hN : N.IsTraitModelOfGenericBase Xc (𝟙 _) qN gN} [QuasiCompact U.ι]
  (hbW : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qN)

variable (hN) in
/-- The morphism of models `s : M'' ⟶ W ⟶ M̄` from the generic slice of the open sub-model
`W = M̄|_U` along its coordinate `b_W`. -/
noncomputable abbrev genericSliceCompHom :
    (genericSliceModel x hbW).Hom N ((hN.restrictOpen U).genericSliceBaseMap x hbW ≫ 𝟙 _)
      (sliceSpecialMap x (hN.restrictOpen U).isTraitModelOver hbW ≫ (N.i ⁻¹ᵁ U).ι) :=
  ((hN.restrictOpen U).genericSliceHom x hbW).comp (N.restrictOpenHom U)

/-- **The square of total spaces** `s ≫ b̄ = φ'' ≫ s_P` (`htot` of
`NearbyCyclesModel.exists_twist_of_slice_of_composition_law`). -/
lemma genericSliceCompHom_total_comp (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total) :
    (genericSliceCompHom x hN hbW).total ≫ bc.total =
      (genericSliceToTraitHom x hbW).total ≫ (projectiveLineSliceHom x).total := by
  change (pullback.fst bW (traitSlice x) ≫ U.ι) ≫ bc.total =
    pullback.snd bW (traitSlice x) ≫ projectiveLineSlice x
  rw [Category.assoc, ← hbWχ, pullback.condition_assoc, projectiveLineSlice_eq_coordChart]

/-- **The square of geometric generic fibres** `s ≫ b̄ = φ'' ≫ s_P` (`hgen` of
`NearbyCyclesModel.exists_twist_of_slice_of_composition_law`). -/
lemma genericSliceCompHom_generic_comp (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
    (hgN : gN = bc.generic ≫
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k')))) :
    (genericSliceCompHom x hN hbW).generic ≫ bc.generic =
      (genericSliceToTraitHom x hbW).generic ≫ (projectiveLineSliceHom x).generic := by
  have htot := genericSliceCompHom_total_comp (hN := hN) x bc hbW hbWχ
  have hP := isPullback_map (ULift.{u} (Fin 2)) (traitGenericPoint k')
  refine hP.hom_ext ?_ ?_
  · have h₁ : bc.generic ≫ ProjectiveSpace.map _ (traitGenericPoint k') = N.j ≫ bc.total :=
      bc.comm_j
    have h₂ := (genericSliceCompHom x hN hbW).comm_j
    have h₃ : (genericSliceToTraitHom x hbW).generic ≫ traitGenericPoint K =
        (genericSliceModel x hbW).j ≫ (genericSliceToTraitHom x hbW).total :=
      (genericSliceToTraitHom x hbW).comm_j
    have htot' : (genericSliceCompHom x hN hbW).total ≫ bc.total =
        (genericSliceToTraitHom x hbW).total ≫ projectiveLineSlice x := htot
    calc _ = (genericSliceCompHom x hN hbW).generic ≫ N.j ≫ bc.total := by
          rw [Category.assoc, h₁]
      _ = (genericSliceModel x hbW).j ≫ (genericSliceToTraitHom x hbW).total ≫
          projectiveLineSlice x := by
          rw [reassoc_of% h₂, htot']
      _ = (genericSliceToTraitHom x hbW).generic ≫ projectiveLineGeometricSlice x ≫
          ProjectiveSpace.map _ (traitGenericPoint k') := by
          rw [← reassoc_of% h₃, projectiveLineGeometricSlice_map]
      _ = _ := (Category.assoc _ _ _).symm
  · rw [Category.assoc, Category.assoc, ← hgN]
    change _ = (genericSliceToTraitHom x hbW).generic ≫ projectiveLineGeometricSlice x ≫
      ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k'))
    rw [projectiveLineGeometricSlice_over]
    exact (Category.assoc _ _ _).trans (baseChangeGenericMap_g
      (hN.restrictOpen U).isTraitModelOver bW hbW (traitSlice x) (traitSlice_over x))

/-- **The square of special fibres is cartesian**: `𝒳''_s = 𝒳̄_s ×_{ℙ¹_{k'}} Spec K` along the
special slice `p_P` (`hssq` of `NearbyCyclesModel.exists_twist_of_slice_of_composition_law`). -/
lemma isPullback_genericSliceCompHom_special
    (hU : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
    (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
    (hqN : qN = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k')) :
    IsPullback (sliceSpecialMap x (hN.restrictOpen U).isTraitModelOver hbW ≫ (N.i ⁻¹ᵁ U).ι)
      (baseChangeSpecialToPoint (b := bW) x).left b₂.left (projectiveLineSpecialSlice x) := by
  have hT := isPullback_genericSlice_projectiveLineSlice x bc hU hbWχ
  have hPs := isPullback_map (ULift.{u} (Fin 2)) (traitClosedPoint k')
  -- the special fibre of `M̄` over `ℙ¹_{k'}`
  have hR : IsPullback N.i b₂.left bc.total (ProjectiveSpace.map _ (traitClosedPoint k')) := by
    refine IsPullback.of_bot ?_ bc.comm_i.symm hPs
    have hb₂ : b₂.left ≫ ProjectiveLine (Spec (.of k')) ↘ Spec (.of k') = Xc'.hom := by
      have := Over.w b₂
      change b₂.left ≫ (_ ↘ _ ≫ 𝟙 _) = _ at this
      rwa [Category.comp_id] at this
    rw [hb₂, ← hqN]
    exact hN.isTraitModelOver.isPullback_i
  -- the outer square
  have hO : IsPullback
      ((sliceSpecialMap x (hN.restrictOpen U).isTraitModelOver hbW ≫ (N.i ⁻¹ᵁ U).ι) ≫ N.i)
      (baseChangeSpecialToPoint (b := bW) x).left bc.total
      (projectiveLineSpecialSlice x ≫ ProjectiveSpace.map _ (traitClosedPoint k')) := by
    rw [(genericSliceCompHom x hN hbW).comm_i, projectiveLineSpecialSlice_map]
    exact (IsPullback.of_hasPullback (pullback.snd bW (traitSlice x))
      (traitClosedPoint K)).paste_horiz hT
  refine IsPullback.of_right hO ?_ hR
  refine hPs.hom_ext ?_ ?_
  · rw [Category.assoc, ← hR.w]
    have := hO.w
    simp only [Category.assoc] at this ⊢
    exact this
  · have hb₂ : b₂.left ≫ ProjectiveLine (Spec (.of k')) ↘ Spec (.of k') = Xc'.hom := by
      have := Over.w b₂
      change b₂.left ≫ (_ ↘ _ ≫ 𝟙 _) = _ at this
      rwa [Category.comp_id] at this
    simp only [Category.assoc]
    rw [hb₂, projectiveLineSpecialSlice_over]
    exact (hN.restrictOpen U).isTraitModelOver.isPullback_i.lift_snd
      (pullback.fst _ _ ≫ pullback.fst bW (traitSlice x))
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K))) (by
        rw [Category.assoc, pullback_fst_comp_eq_snd_traitMap x hbW, pullback.condition_assoc,
          traitClosedPoint_traitMap, Category.assoc])

/-- **The square of bases is cartesian**: for `M̄` with full geometric generic fibre,
`X₂ = X̄₁ ×_{ℙ¹_η} Spec Frac K⟦t⟧` along the generic slice `c_P` (`hbsq` of
`NearbyCyclesModel.exists_twist_of_slice_of_composition_law`). The map `c : X₂ ⟶ X̄₁` is computed
through the generic fibres (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap_eq`),
and `X̄₁ ≅ 𝒳̄_η = 𝒳̄ ×_{ℙ¹_S} ℙ¹_η`. -/
lemma isPullback_genericSliceCompHom_generic
    (hU : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
    (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
    (hqN : qN = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
    (hNgen : IsPullback N.ε gN Xc.hom (traitGenericPointToSpec k' ≫ 𝟙 _)) :
    IsPullback ((hN.restrictOpen U).genericSliceBaseMap x hbW ≫ 𝟙 _)
      (genericSliceBaseToPoint x hbW).left b₁.left (projectiveLineGenericSlice x) := by
  have hT := isPullback_genericSlice_projectiveLineSlice x bc hU hbWχ
  obtain ⟨wN, hwN, hwN₁, hwN₂⟩ := hN.exists_isIso_genericFibre hNgen
  have hM := hN.isTraitModelOver
  have hPη := isPullback_map (ULift.{u} (Fin 2)) (traitGenericSpec k')
  let E : pullback qN (traitGenericSpec k') ⟶ Xc.left := wN ≫ pullback.fst _ _
  have : IsIso E := inferInstance
  -- the generic fibre of `M̄` over `ℙ¹_η`
  let bη : pullback qN (traitGenericSpec k') ⟶
      ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) :=
    hPη.lift (pullback.fst _ _ ≫ bc.total) (pullback.snd _ _) (by
      rw [Category.assoc, ← hqN]
      exact pullback.condition)
  have hRη : IsPullback (pullback.fst qN (traitGenericSpec k')) bη bc.total
      (ProjectiveSpace.map _ (traitGenericSpec k')) := by
    refine IsPullback.of_bot ?_ (hPη.lift_fst _ _ _).symm hPη
    rw [hPη.lift_snd, ← hqN]
    exact IsPullback.of_hasPullback qN (traitGenericSpec k')
  have hE : E ≫ b₁.left = bη := by
    refine hPη.hom_ext ?_ ?_
    · have : Epi (genericFibreInclusion N qN gN hM.isPullback_j.w) :=
        hM.epi_lift_traitGenericPointToSpec
      refine (cancel_epi (genericFibreInclusion N qN gN hM.isPullback_j.w)).1 ?_
      have hε : bc.generic ≫ ProjectiveSpace.map _ (traitGenericPointToSpec k') =
          N.ε ≫ b₁.left := bc.comm_ε
      have hj : bc.generic ≫ ProjectiveSpace.map _ (traitGenericPoint k') = N.j ≫ bc.total :=
        bc.comm_j
      calc _ = N.ε ≫ b₁.left ≫ ProjectiveSpace.map _ (traitGenericSpec k') := by
            rw [← hwN₂]
            simp only [E, Category.assoc]
        _ = N.j ≫ bc.total := by
            rw [← reassoc_of% hε, ← ProjectiveSpace.map_comp,
              traitGenericPointToSpec_traitGenericSpec, hj]
        _ = _ := by rw [hPη.lift_fst, genericFibreInclusion_fst_assoc]
    · have h1 : (E ≫ b₁.left) ≫ (overProjectiveLine (point (FractionRing (PowerSeries k')))).hom =
          E ≫ Xc.hom := by
        rw [Category.assoc, Over.w b₁]
      change (E ≫ b₁.left) ≫ (_ ↘ _ ≫ 𝟙 _) = _ at h1
      rw [Category.comp_id] at h1
      have h2 : E ≫ Xc.hom = pullback.snd qN (traitGenericSpec k') := by
        change (wN ≫ pullback.fst _ _) ≫ Xc.hom = _
        rw [Category.assoc, pullback.condition, Category.comp_id, hwN₁]
      exact (h1.trans h2).trans (hPη.lift_snd _ _ _).symm
  -- the map `c` through the generic fibres
  have hwW : genericFibreInclusion (N.restrictOpen U) (U.ι ≫ qN) ((N.j ⁻¹ᵁ U).ι ≫ gN)
      (hN.restrictOpen U).isTraitModelOver.isPullback_j.w ≫
        (restrictGenericFibreMap (q := qN) U ≫ wN) ≫ pullback.fst _ _ =
      (N.restrictOpen U).ε := by
    rw [Category.assoc, genericFibreInclusion_restrictOpen_comp_assoc hM U, hwN₂]
    rfl
  have hc := (hN.restrictOpen U).genericSliceBaseMap_eq x hbW _ hwW
  let c' : (genericSliceBase x hbW).left ⟶ pullback qN (traitGenericSpec k') :=
    (genericSliceFibreIso x hbW).inv ≫ genericSliceFibreMap x hbW ≫ restrictGenericFibreMap U
  have hX₂ : (genericSliceFibreIso x hbW).inv ≫ pullback.snd _ _ =
      (genericSliceBase x hbW).hom := by
    rw [Iso.inv_comp_eq, genericSliceFibreIso_hom_over]
  -- the outer square
  have hO : IsPullback (c' ≫ pullback.fst qN (traitGenericSpec k')) (genericSliceBase x hbW).hom
      bc.total (projectiveLineGenericSlice x ≫ ProjectiveSpace.map _ (traitGenericSpec k')) := by
    have I₁ : IsPullback (genericSliceFibreIso x hbW).inv (genericSliceBase x hbW).hom
        (pullback.snd (pullback.snd bW (traitSlice x)) (traitGenericSpec K)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hX₂]⟩
    have h := I₁.paste_horiz ((IsPullback.of_hasPullback (pullback.snd bW (traitSlice x))
      (traitGenericSpec K)).paste_horiz hT)
    convert h using 1
    · simp only [c', Category.assoc, restrictGenericFibreMap_fst, genericSliceFibreMap_fst_assoc]
    · rw [projectiveLineGenericSlice_map, Category.id_comp]
  have hc' : IsPullback c' (genericSliceBase x hbW).hom bη (projectiveLineGenericSlice x) := by
    refine IsPullback.of_right hO ?_ hRη
    refine hPη.hom_ext ?_ ?_
    · rw [Category.assoc, ← hRη.w, ← Category.assoc]
      exact hO.w.trans (Category.assoc _ _ _).symm
    · have e1 : bη ≫ ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) ↘
          Spec (.of (FractionRing (PowerSeries k'))) = pullback.snd qN (traitGenericSpec k') :=
        hPη.lift_snd _ _ _
      have e2 := projectiveLineGenericSlice_over (k' := k') x
      have e3 : c' ≫ pullback.snd qN (traitGenericSpec k') =
          (genericSliceBase x hbW).hom ≫ traitGenericSpecMap k' K := by
        simp only [c', Category.assoc, restrictGenericFibreMap_snd, genericSliceFibreMap_snd]
        rw [← Category.assoc, hX₂]
      exact ((Category.assoc _ _ _).trans ((congrArg (c' ≫ ·) e1).trans e3)).trans
        ((congrArg ((genericSliceBase x hbW).hom ≫ ·) e2).symm.trans (Category.assoc _ _ _).symm)
  have hEsq : IsPullback E bη b₁.left (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hE]⟩
  have e : (hN.restrictOpen U).genericSliceBaseMap x hbW ≫ 𝟙 _ = c' ≫ E := by
    rw [Category.comp_id, hc]
    simp only [c', E, Category.assoc]
  rw [e]
  have h := hc'.paste_horiz hEsq
  rw [Category.comp_id] at h
  exact h

end SliceData

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
