/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DenseCompactification
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Cohomological dimension of fibres and the amplitude of compactly supported direct images

Over an algebraically closed field `k'`, a `k'`-scheme `X` of finite type and dimension at most
`d` has no cohomology above `2d` with coefficients in a sheaf of modules over a finite ring
(`AlgebraicGeometry.Etale.subsingleton_H_forget₂_of_two_mul_lt`, blueprint
`proposition-proper-direct-image-finite-coefficients`). Consequently, for a separated morphism of
finite type `f : X ⟶ Y` between schemes of finite type over a field whose geometric fibres have
dimension at most `d`, `Rᵠf_! F = 0` for `q > 2d`
(`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt`,
blueprint `theorem-results-from-etale-theory--5`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section ProperFibre

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Proper base change at a geometric point**, in the form of a vanishing criterion: for a
proper `p : S ⟶ T`, a point `t` of `T` with geometric point `x : Spec Ω ⟶ T` and a sheaf `G` of
`Λ`-modules on `S`, if `Rᵠh_*(G|)` vanishes for the geometric fibre `h : S ×_T Spec Ω ⟶ Spec Ω`,
then so does `x^* Rᵠp_* G`. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_isProper (hΛ : IsAddTorsion Λ)
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (t : T)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (h : IsZero (Etale.higherDirectImage Λ (pullback.snd p (T.algClosurePoint t)) q
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p (T.algClosurePoint t))).obj G))) :
    IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj
      (((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q |>.obj G)) := by
  let x := T.algClosurePoint t
  let sq := IsPullback.of_hasPullback p x
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  exact IsZero.of_iso h
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapIso
        ((p)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso G q).symm ≪≫
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlusHomologyFunctorIso q).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.obj K) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd p x)).rightDerivedFunctorPlus.mapIso
          (((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst p x)).mapDerivedCategoryPlusSingleFunctor 0).app G)))

/-- For a closed immersion `k : C ⟶ Z` and any `h : Z ⟶ T`, `Rᵠh_*(k_* H) ≅ Rᵠ(k ≫ h)_* H`, the
direct image along `k` being exact. -/
noncomputable def rightDerivedLowerStarObjLowerStarIsoOfIsFinite {C Z T : Scheme.{u}}
    (k : C ⟶ Z) [IsFinite k] (h : Z ⟶ T) (H : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    ((h)_*[ModuleCat.{u + 1} Λ].rightDerived q).obj ((k)_*[ModuleCat.{u + 1} Λ].obj H) ≅
      ((k ≫ h)_*[ModuleCat.{u + 1} Λ].rightDerived q).obj H :=
  ((h)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((R((h)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((((k)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app H).symm ≪≫
      (R((h)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory _ k).app _).symm ≪≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) k h).app _) ≪≫
    (k ≫ h)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorObjSingleFunctorIso H q

/-- **Vanishing above twice the dimension of a support.** Let `h : Z ⟶ Spec K` be quasi-compact
and locally of finite type, `S₀ ⊆ Z` open of dimension at most `d`, and `M` a sheaf of
`Λ`-modules on `Z` vanishing on the complement of the closure of `S₀`. Then `Rᵠh_* M = 0` for
`q > 2d`: `M` is the direct image of a sheaf on the reduced closure `C` of `S₀`, which has
dimension at most `d` since `S₀` is dense in it. -/
theorem isZero_rightDerived_lowerStar_of_isZero_upperStar_compl_closure (hΛ : IsAddTorsion Λ)
    {K : Type u} [Field K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K)) [LocallyOfFiniteType h]
    [QuasiCompact h] (S₀ : Set Z) (hS₀ : IsOpen S₀) (d : ℕ)
    (hdim : topologicalKrullDim S₀ ≤ (d : WithBot ℕ∞))
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : IsZero
      ((Scheme.Opens.ι ⟨(closure S₀)ᶜ, isClosed_closure.isOpen_compl⟩)^*[ModuleCat.{u + 1} Λ].obj
        M)) (q : ℕ) (hq : 2 * d < q) :
    IsZero (((h)_*[ModuleCat.{u + 1} Λ].rightDerived q).obj M) := by
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨closure S₀, isClosed_closure⟩
  let k := I.subschemeι
  have hrange : Set.range k.base = closure S₀ := by
    simp [k, I, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hij : Set.range k.base = (Set.range (Scheme.Opens.ι
      ⟨(closure S₀)ᶜ, isClosed_closure.isOpen_compl⟩).base)ᶜ := by
    rw [hrange, Scheme.Opens.range_ι]
    simp
  obtain ⟨H, ⟨e⟩⟩ := mem_essImage_lowerStar_of_isZero_upperStar (i := k) hij hM
  refine IsZero.of_iso ?_ (((h)_*[ModuleCat.{u + 1} Λ].rightDerived q).mapIso e.symm ≪≫
    rightDerivedLowerStarObjLowerStarIsoOfIsFinite Λ k h H q)
  let V : I.subscheme.Opens := k ⁻¹ᵁ ⟨S₀, hS₀⟩
  have hV : Dense (V : Set I.subscheme) := by
    rw [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_mk, dense_iff_closure_eq,
      k.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_preimage_eq_of_subset (hrange ▸ subset_closure), ← hrange, Set.preimage_range]
  let φ : V → S₀ := fun v ↦ ⟨k v.1, v.2⟩
  have hφ : Topology.IsInducing φ :=
    Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val (g := Subtype.val)
      (k.isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal :
        Topology.IsInducing fun v : V ↦ k v.1)
  exact isZero_rightDerived_lowerStar_of_two_mul_lt Λ hΛ (k ≫ h) (𝟙 _) (k ≫ h)
    (Category.comp_id _) d
    ((topologicalKrullDim_le_of_dense (k ≫ h) V hV).trans (hφ.topologicalKrullDim_le.trans hdim))
    H q hq

end ProperFibre

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Cohomological dimension over an
algebraically closed field.

Let `k'` be an algebraically closed field, `X` a `k'`-scheme of finite type of dimension at most
`d`, and `F` an étale sheaf of `Λ`-modules over a finite ring `Λ`. Then `Hᵠ(X_ét, F) = 0` for
`q > 2d`, cohomology being that of the underlying abelian sheaf. The blueprint assumes `F`
constructible; this is not needed, since `F` is torsion as `Λ` is finite, and the bound
`cd_tor(X) ≤ 2d` (`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`) applies
to all torsion sheaves. -/
theorem subsingleton_H_forget₂_of_two_mul_lt {k' : Type u} [Field k'] [IsAlgClosed k']
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k')) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Sheaf.H ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  refine Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d a hX _ ?_ q hq
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
  have := Fintype.ofFinite Λ
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Fintype.card Λ, Fintype.card_pos, ?_⟩
  let y : F.obj.obj U := x
  change Fintype.card Λ • y = 0
  rw [← one_smul Λ y, ← smul_assoc, card_nsmul_eq_zero, zero_smul]

/-- Blueprint `theorem-results-from-etale-theory--5`: The compact-support bound uses the original
fibres.

Let `f : X ⟶ Y` be a separated morphism of finite type (here: one admitting a compactification)
between schemes of finite type over a field `k`, whose geometric fibres have dimension at most
`d`, and let `Λ` be a finite ring. Then for every étale sheaf `F` of `Λ`-modules on `X`,
`Rᵠf_! F = 0` for `q > 2d`. The blueprint also assumes the exponent of `Λ` invertible on `Y`;
this is not needed, proper base change holding for all torsion coefficients. -/
theorem isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt {k : Type u}
    [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (_hf : f ≫ aY = aX) (d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  let c := HasCompactification.compactification f
  lift q to ℕ using by lia
  have hq' : 2 * d < q := by exact_mod_cast hq
  let G := (c.i)_!open[ModuleCat.{u + 1} Λ].obj F
  refine IsZero.of_iso ?_ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((R((c.g)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((((c.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    (c.g)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorObjSingleFunctorIso G q)
  refine isZero_of_forall_isZero_upperStar_algClosurePoint Λ _ fun t ↦ ?_
  let x := Y.algClosurePoint t
  refine isZero_upperStar_rightDerived_lowerStar_of_isProper Λ hΛ c.g t G q ?_
  refine IsZero.of_iso ?_ (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ _ _ q).symm
  refine IsZero.of_iso ?_ ((pullback.snd c.g x)_*[ModuleCat.{u + 1} Λ]
    |>.homologyRightDerivedFunctorObjSingleFunctorIso _ q)
  have : IsProper (pullback.snd c.g x) := MorphismProperty.pullback_snd _ _ inferInstance
  let S₀ : Set ↥(pullback c.g x) := Set.range (pullback.snd c.i (pullback.fst c.g x))
  refine isZero_rightDerived_lowerStar_of_isZero_upperStar_compl_closure Λ hΛ
    (pullback.snd c.g x) S₀
    (pullback.snd c.i (pullback.fst c.g x)).isOpenEmbedding.isOpen_range d ?_ _ ?_ q hq'
  · rw [← (pullback.snd c.i (pullback.fst c.g x)).isOpenEmbedding.isEmbedding
        |>.topologicalKrullDim_eq_range,
      IsHomeomorph.topologicalKrullDim_eq _
        (pullbackRightPullbackFstIso c.g x c.i).hom.homeomorph.isHomeomorph,
      ← IsHomeomorph.topologicalKrullDim_eq _
        (pullback.congrHom c.comm rfl).hom.homeomorph.isHomeomorph]
    exact hd _ x
  · refine IsZero.of_iso (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
      (ModuleCat.{u + 1} Λ) c.i (Scheme.Opens.ι _ ≫ pullback.fst c.g x) ?_ F)
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) _ (pullback.fst c.g x)).app G).symm
    refine Set.disjoint_left.2 ?_
    rintro _ hi ⟨p, rfl⟩
    refine p.2 (subset_closure ?_)
    simp only [S₀, Scheme.Pullback.range_snd]
    simpa using hi

end Etale

end AlgebraicGeometry
