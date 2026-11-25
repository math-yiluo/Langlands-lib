/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.ClosedRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.NonClosedBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Unbounded
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# Base change along a strict localization, without torsion hypotheses

Étale base change holds for arbitrary coefficients (no torsion hypothesis), so the limit form of
base change (blueprint `corollary-open-direct-image-over-field--2`, Stacks 0EZT) gives base change
along a cofiltered limit of étale morphisms with affine transition maps, for arbitrary sheaves of
`Λ`-modules. In particular, for a geometric point `s` of `S`, a morphism `f : W ⟶ S` from a
quasi-compact quasi-separated scheme and the base change `W' = W ×_S S_(s) ⟶ W` of the strict
localization, the base change maps along `W' ⟶ W` of a quasi-compact quasi-separated morphism are
isomorphisms in every degree and for every sheaf, and the derived base change map on bounded below
complexes is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_forall_isIso_baseChangeHomologyMap`:
  base change in every degree and for every sheaf gives the derived base change on `D⁺`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_etale`: base change along a
  limit of étale morphisms.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization_of_qcqs`
  and `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isPullback_strictLocalization`:
  base change along the base change of a strict localization.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Derived base change from base change in every degree.** For a cartesian square such that
the degree-`q` base change maps `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` are isomorphisms for all `q` and
all sheaves `F`, the derived base change map `p^* R⁺g_* ⟶ R⁺h_* e^*` is an isomorphism: in
degree `0` the underived base change map is an isomorphism, in positive degrees the pullback
`e^* I` of an injective sheaf is `h_*`-acyclic, and the derived base change map is computed on
complexes of injectives. -/
theorem Etale.isIso_derivedBaseChangeMapPlus_of_forall_isIso_baseChangeHomologyMap
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p)
    (H : ∀ (q : ℕ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (Etale.baseChangeHomologyMap Λ sq q F)) :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    have := H 0 F
    obtain ⟨a⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_zero Λ sq F
    exact (Arrow.isIso_hom_iff_isIso_hom_of_isIso a.hom).1 this
  have hI (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
      ((h)_*[ModuleCat.{u + 1} Λ]).rightAcyclic ((e)^*[ModuleCat.{u + 1} Λ].obj I) := by
    intro q
    have := H (q + 1) I
    have hz : IsZero ((p)^*[ModuleCat.{u + 1} Λ].obj
        ((((g)_*[ModuleCat.{u + 1} Λ]).rightDerived (q + 1)).obj I)) :=
      Functor.map_isZero _ (Functor.isZero_rightDerived_obj_injective_succ _ q I)
    exact hz.of_iso ((Etale.baseChangeHomologyMapTargetIso Λ e h (q + 1) I).symm ≪≫
      (asIso (Etale.baseChangeHomologyMap Λ sq (q + 1 : ℕ) I)).symm ≪≫
      Etale.baseChangeHomologyMapSourceIso Λ p (q + 1) I g)
  have hK : ∀ K, IsIso
      ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
    intro K
    obtain ⟨n, hn⟩ := K.2
    have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
    obtain ⟨L, _, ⟨i⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
    let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
    let P := (HomotopyCategory.Plus.quotient _).obj M
    suffices IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (DerivedCategory.Plus.Qh.obj P)) by
      rw [← NatTrans.isIso_app_iff_of_iso _
        ((DerivedCategory.Plus.quotientCompQhIso _).app M ≪≫ i)]
      exact this
    have hM : ∀ m, (h)_*[ModuleCat.{u + 1} Λ].rightAcyclic
        ((((e)^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M).obj.X m) := fun m ↦
      have : Injective (M.obj.X m) := (L.obj.X m).2
      hI (M.obj.X m)
    have h₁ : IsIso ((h)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
        (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj P)) :=
      (h)_*[ModuleCat.{u + 1} Λ].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
        (((e)^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M) hM
    have h₂ : IsIso ((g)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) := by
      dsimp only [P, M]
      infer_instance
    have hfac := Etale.derivedBaseChangeMapPlus_fac_app (ModuleCat.{u + 1} Λ) sq.toCommSq P
    have : IsIso (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((g)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) ≫
        (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          (DerivedCategory.Plus.Qh.obj P)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((g)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P)) _
  exact NatIso.isIso_of_isIso_app _

section Limit

variable {S T : Scheme.{u}} (g : T ⟶ S) {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u})
  (p : X ⟶ (Functor.const I).obj S)

/-- **Base change along a limit of étale schemes over a quasi-compact quasi-separated base.**
Let `Xᵢ ⟶ S` be a cofiltered system of étale quasi-compact quasi-separated morphisms with affine
transition maps and limit `X₀ ⟶ S`, `S` quasi-compact and quasi-separated, and `g : T ⟶ S`
quasi-compact quasi-separated. For every sheaf `F` on `T`, the base-change map of the Cartesian
square `Y = T ×_S X₀` is an isomorphism in every degree: this is the limit form of base change
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`) together with étale base
change at the stages (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale`). -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_etale_of_qcqs [IsCofiltered I]
    [QuasiCompact g] [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, Etale (p.app i)] [∀ i, QuasiCompact (p.app i)] [∀ i, QuasiSeparated (p.app i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    {cX : Cone X} (hX : IsLimit cX) (p₀ : cX.pt ⟶ S)
    (hp₀ : ∀ i, cX.π.app i ≫ p.app i = p₀) {Y : Scheme.{u}} {e : Y ⟶ T} {h : Y ⟶ cX.pt}
    (sq : IsPullback e h g p₀) (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : IsConnected I := IsCofiltered.isConnected I
  have : ∀ i, CompactSpace (((Functor.const I).obj S).obj i) := fun _ ↦
    inferInstanceAs (CompactSpace S)
  have : ∀ i, QuasiSeparatedSpace (((Functor.const I).obj S).obj i) :=
    fun _ ↦ inferInstanceAs (QuasiSeparatedSpace S)
  have : ∀ i, CompactSpace (X.obj i) := fun i ↦ QuasiCompact.compactSpace_of_compactSpace (p.app i)
  have : ∀ i, QuasiSeparatedSpace (X.obj i) := fun i ↦ quasiSeparatedSpace_of_quasiSeparated
    (p.app i)
  have : ∀ i, QuasiCompact (((Functor.const I).map g).app i) := fun _ ↦
    inferInstanceAs (QuasiCompact g)
  have : ∀ i, QuasiSeparated (((Functor.const I).map g).app i) := fun _ ↦
    inferInstanceAs (QuasiSeparated g)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (((Functor.const I).obj S).map f) :=
    fun _ ↦ (inferInstance : IsAffineHom (𝟙 S))
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (((Functor.const I).obj T).map f) :=
    fun _ ↦ (inferInstance : IsAffineHom (𝟙 T))
  let e' : Etale.smoothLimitPullbackFunctor g X p ⟶ (Functor.const I).obj T :=
    { app i := pullback.fst g (p.app i)
      naturality i j f := by simp }
  let h' : Etale.smoothLimitPullbackFunctor g X p ⟶ X :=
    { app i := pullback.snd g (p.app i)
      naturality i j f := by simp }
  have hsq (i : I) : IsPullback (e'.app i) (h'.app i) (((Functor.const I).map g).app i)
      (p.app i) := IsPullback.of_hasPullback g (p.app i)
  let cY : Cone (Etale.smoothLimitPullbackFunctor g X p) :=
    { pt := Y
      π :=
        { app i := pullback.lift e (h ≫ cX.π.app i)
            (by rw [sq.w, Category.assoc, hp₀])
          naturality i j f := pullback.hom_ext (by simp) (by simp) } }
  have hcY : IsLimit cY := isLimitOfIsPullbackOfIsConnected h' cY cX
    { hom := h
      w i := by simp [cY, h'] }
    (fun i ↦ by
      refine IsPullback.of_right ?_ (by simp [cY, h']) (IsPullback.of_hasPullback g (p.app i))
      simp only [cY, pullback.lift_fst, hp₀]
      exact sq)
    hX
  have key := Etale.isIso_baseChangeHomologyMap_of_isLimit Λ p ((Functor.const I).map g) e' h'
    hsq (isLimitConstCone I S) hX (isLimitConstCone I T) hcY (p₀ := p₀) (g₀ := g) (e₀ := e)
    (h₀ := h) (fun i ↦ (Category.comp_id _).trans (hp₀ i).symm)
    (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)
    (fun _ ↦ (Category.comp_id _).trans (pullback.lift_fst _ _ _).symm)
    (fun i ↦ by simp [cY, h']) sq (𝟙 _) (𝟙 T) (fun _ ↦ Category.id_comp _) F q
    (fun i ↦ Etale.isIso_baseChangeHomologyMap_of_etale Λ (hsq i) q _)
  exact (Etale.isIso_baseChangeHomologyMap_iff_of_iso Λ sq q
    ((Etale.upperStarId (ModuleCat.{u + 1} Λ) T).app F)).1 key

end Limit

/-- **Base change along a limit of étale schemes** (blueprint
`corollary-open-direct-image-over-field--2`), for a quasi-compact quasi-separated base `S` and a
system given as a diagram `D` in `Over S` of étale quasi-compact quasi-separated `S`-schemes with
affine transition maps: for `g : T ⟶ S` quasi-compact quasi-separated, the base-change maps of the
Cartesian square `Y = T ×_S lim D` are isomorphisms in every degree and for every sheaf of
`Λ`-modules. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_etale {S T : Scheme.{u}} (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S]
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, Etale (D.obj i).hom] [∀ i, QuasiCompact (D.obj i).hom]
    [∀ i, QuasiSeparated (D.obj i).hom] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) {Y : Scheme.{u}} {e : Y ⟶ T}
    {h : Y ⟶ c.pt.left} (sq : IsPullback e h g c.pt.hom) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let p : D ⋙ Over.forget S ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality i j f := by simp }
  have : ∀ i, Etale (p.app i) := fun i ↦ (inferInstance : Etale (D.obj i).hom)
  have : ∀ i, QuasiCompact (p.app i) := fun i ↦ (inferInstance : QuasiCompact (D.obj i).hom)
  have : ∀ i, QuasiSeparated (p.app i) := fun i ↦
    (inferInstance : QuasiSeparated (D.obj i).hom)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget S).map f) := fun f ↦
    (inferInstance : IsAffineHom (D.map f).left)
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_etale_of_qcqs Λ g (D ⋙ Over.forget S) p hc
    c.pt.hom (fun i ↦ Over.w (c.π.app i)) sq q F

/-- **Base change along the base change of a strict localization.** Let `s` be a geometric point
of a quasi-separated scheme `S`, `f : W ⟶ S` a morphism from a quasi-compact quasi-separated
scheme and `W' = W ×_S S_(s)`. The projection `W' ⟶ W` is the limit of the étale `W`-schemes
`W ×_S V` for the affine pointed étale neighbourhoods `(V, v)` of `s`, so the base change maps
along `W' ⟶ W` of a quasi-compact quasi-separated `g : T ⟶ W` are isomorphisms in every degree
and for every sheaf of `Λ`-modules. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization_of_qcqs
    {S : Scheme.{u}} [QuasiSeparatedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {W W' : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (f : W ⟶ S) (uW : W' ⟶ W) (r : W' ⟶ strictLocalization s)
    (hW' : IsPullback uW r f (strictLocalizationToBase s)) {T Y : Scheme.{u}} (g : T ⟶ W)
    [QuasiCompact g] [QuasiSeparated g] {e : Y ⟶ T} {h : Y ⟶ W'} (sq : IsPullback e h g uW)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let I₀ := InitiallySmall.CofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  let ι₀ := InitiallySmall.fromCofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  have : IsConnected I₀ := IsCofiltered.isConnected _
  let D₀ := ι₀ ⋙ affineNeighborhoodDiagramOver s
  let cO := (strictLocalizationConeOver s).whisker ι₀
  have hcO : IsLimit cO :=
    (Functor.Initial.isLimitWhiskerEquiv ι₀ _).symm (isLimitStrictLocalizationConeOver s)
  let cD := (CategoryTheory.Over.forget S).mapCone cO
  have hcD : IsLimit cD := isLimitOfPreserves (CategoryTheory.Over.forget S) hcO
  let w : D₀ ⋙ CategoryTheory.Over.forget S ⟶ (Functor.const I₀).obj S :=
    { app k := (D₀.obj k).hom
      naturality k k' a := (CategoryTheory.Over.w (D₀.map a)).trans (Category.comp_id _).symm }
  have hw (k : I₀) : cD.π.app k ≫ w.app k = strictLocalizationToBase s :=
    CategoryTheory.Over.w (cO.π.app k)
  let cP := constPullbackCone f w cD uW r hw hW'.w
  have hP : IsLimit cP := isLimitConstPullbackCone f w hcD uW r hw hW'
  let P := pullback ((Functor.const I₀).map f) w
  let D' : I₀ ⥤ CategoryTheory.Over W :=
    P.toOver W (fun k ↦ (pullback.fst ((Functor.const I₀).map f) w).app k)
      (fun a ↦ ((pullback.fst ((Functor.const I₀).map f) w).naturality a).trans
        (Category.comp_id _))
  let c' : Cone D' :=
    { pt := CategoryTheory.Over.mk uW
      π :=
        { app k := CategoryTheory.Over.homMk (cP.π.app k)
            (constPullbackCone_π_app_fst f w cD uW r hw hW'.w k)
          naturality k k' a := CategoryTheory.Over.OverMorphism.ext (cP.π.naturality a) } }
  have hc' : IsLimit ((CategoryTheory.Over.forget W).mapCone c') := hP
  have hiso (k : I₀) := isPullback_pullback_evaluation ((Functor.const I₀).map f) w k
  have haffk (k : I₀) : IsAffine ((D₀ ⋙ CategoryTheory.Over.forget S).obj k) := (ι₀.obj k).2
  have hét (k : I₀) : Etale (w.app k) := (ι₀.obj k).obj.1.prop
  have hqsS (k : I₀) : QuasiSeparatedSpace (((Functor.const I₀).obj S).obj k) :=
    inferInstanceAs (QuasiSeparatedSpace S)
  have het (k : I₀) : Etale (D'.obj k).hom :=
    MorphismProperty.of_isPullback (P := @Etale) (hiso k).flip inferInstance
  have hqc (k : I₀) : QuasiCompact (D'.obj k).hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hiso k).flip
      (quasiCompact_of_compactSpace _)
  have hqs (k : I₀) : QuasiSeparated (D'.obj k).hom :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hiso k).flip
      (QuasiSeparated.of_quasiSeparatedSpace _)
  have haff {k k' : I₀} (a : k ⟶ k') : IsAffineHom (D'.map a).left :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const f w a).flip (isAffineHom_of_isAffine _)
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_etale Λ g D' c' hc' (h := h) sq q F

/-- **Derived base change along the base change of a strict localization.** In the situation of
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization_of_qcqs`,
the derived base change map `uW^* R⁺g_* ⟶ R⁺h_* e^*` on bounded below complexes is an
isomorphism, for arbitrary coefficients `Λ`. -/
theorem Etale.isIso_derivedBaseChangeMapPlus_of_isPullback_strictLocalization
    {S : Scheme.{u}} [QuasiSeparatedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {W W' : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (f : W ⟶ S) (uW : W' ⟶ W) (r : W' ⟶ strictLocalization s)
    (hW' : IsPullback uW r f (strictLocalizationToBase s)) {T Y : Scheme.{u}} (g : T ⟶ W)
    [QuasiCompact g] [QuasiSeparated g] {e : Y ⟶ T} {h : Y ⟶ W'} (sq : IsPullback e h g uW) :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  Etale.isIso_derivedBaseChangeMapPlus_of_forall_isIso_baseChangeHomologyMap Λ sq fun q F ↦
    Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization_of_qcqs Λ s f uW r hW' g
      sq q F

end AlgebraicGeometry
