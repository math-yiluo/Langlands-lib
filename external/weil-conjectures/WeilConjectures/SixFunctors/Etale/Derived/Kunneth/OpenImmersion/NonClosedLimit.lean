/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange
public import WeilConjectures.AlgebraicGeometry.LimitFiberProduct

/-!
# Base change along open immersions: passing to a limit of the factors

This file contains the limit step of the "stalks over points with positive transcendence
degree" part of the proof of blueprint `corollary-open-direct-image-over-field--2`. Let `L` be a
field and suppose that the statement of `corollary-open-direct-image-over-field--2` holds for all
data with `dim X + dim Y < N`.

* `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_snd`: if `Y' = lim Yᵢ` is a
  cofiltered limit of affine `L`-schemes of finite type with `dim X + dim Yᵢ < N`, then the base
  change maps of the square `U ×_X (X ×_L Y') ⟶ X ×_L Y'` over an open immersion `U ⟶ X` of
  `L`-schemes of finite type are isomorphisms.
* `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_fst`: if `X' = lim Xᵢ` is a
  cofiltered limit of affine `L`-schemes of finite type with `dim Xᵢ + dim Y < N` and
  `U' ⊆ X'` is a quasi-compact open, then the base change maps of the square
  `U' ×_{X'} (X' ×_L Y) ⟶ X' ×_L Y` are isomorphisms. The open `U'` descends to an open
  `Uᵢ ⊆ Xᵢ` (blueprint `corollary-open-direct-image-over-field--2`).

Both follow from the limit theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall`
(blueprint `corollary-open-direct-image-over-field--2`) applied to the systems of fibre products,
which are limits by the commutation of fibre products with limits (blueprint
`lem-kun-fibre-product-limits`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]

/-- Converse of `CategoryTheory.IsPullback.isPullback_map_of_isLimit`: given a system of
cartesian squares `Pⱼ → Xⱼ, Pⱼ → Yⱼ, Xⱼ → Sⱼ, Yⱼ → Sⱼ`, limit cones of the diagrams `X`, `Y`,
`S`, and a cone `cP` over `P` whose induced square of cone points is cartesian, the cone `cP`
is a limit cone (blueprint `lem-kun-fibre-product-limits`). -/
noncomputable def IsPullback.isLimitOfIsPullbackLimMap {P X Y S : J ⥤ C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : ∀ j, IsPullback (fst.app j) (snd.app j) (f.app j) (g.app j))
    {cP : Cone P} {cX : Cone X} {cY : Cone Y} {cS : Cone S} (hX : IsLimit cX)
    (hY : IsLimit cY) (hS : IsLimit cS)
    (hP : IsPullback (hX.map cP fst) (hY.map cP snd) (hS.map cX f) (hS.map cY g)) :
    IsLimit cP where
  lift s := hP.lift (hX.map s fst) (hY.map s snd) (hS.hom_ext fun j ↦ by
    simp only [Category.assoc, IsLimit.map_π, IsLimit.map_π_assoc]
    exact s.π.app j ≫= (h j).w)
  fac s j := (h j).hom_ext
    (by rw [Category.assoc, ← IsLimit.map_π, ← Category.assoc, hP.lift_fst, IsLimit.map_π])
    (by rw [Category.assoc, ← IsLimit.map_π, ← Category.assoc, hP.lift_snd, IsLimit.map_π])
  uniq s m hm := hP.hom_ext (hX.hom_ext fun j ↦ by simp [← hm])
    (hY.hom_ext fun j ↦ by simp [← hm])

namespace Limits

variable [HasPullbacks C]

/-- Pullbacks in a functor category are computed pointwise. -/
lemma isPullback_pullback_evaluation {F G H : J ⥤ C} (f : F ⟶ H) (g : G ⟶ H) (j : J) :
    IsPullback ((pullback.fst f g).app j) ((pullback.snd f g).app j) (f.app j) (g.app j) :=
  (IsPullback.of_hasPullback f g).map ((evaluation J C).obj j)

/-- The transition squares of the diagram `j ↦ X ×_W Dⱼ` over the diagram `D` are cartesian. -/
lemma isPullback_map_pullback_const {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) {j k : J} (u : j ⟶ k) :
    IsPullback ((pullback ((Functor.const J).map a) w).map u)
      ((pullback.snd ((Functor.const J).map a) w).app j)
      ((pullback.snd ((Functor.const J).map a) w).app k) (D.map u) := by
  refine IsPullback.of_right ?_ ((pullback.snd ((Functor.const J).map a) w).naturality u)
    (isPullback_pullback_evaluation _ w k)
  have h₁ : (pullback ((Functor.const J).map a) w).map u ≫
      (pullback.fst ((Functor.const J).map a) w).app k =
        (pullback.fst ((Functor.const J).map a) w).app j := by
    simp
  have h₂ : D.map u ≫ w.app k = w.app j := by simp
  rw [h₁, h₂]
  exact isPullback_pullback_evaluation _ w j

/-- The cone with vertex `X'` over the diagram `j ↦ X ×_W Dⱼ`, for a commutative square
`X' → X, X' → lim D` over `W`. -/
@[simps pt]
noncomputable def constPullbackCone {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) (cD : Cone D) {X' : C} (b : X' ⟶ X) (p' : X' ⟶ cD.pt)
    {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀) (hb : b ≫ a = p' ≫ w₀) :
    Cone (pullback ((Functor.const J).map a) w) where
  pt := X'
  π :=
    { app j := (isPullback_pullback_evaluation _ w j).lift b (p' ≫ cD.π.app j)
        (by simp [hw₀, hb])
      naturality j k u := (isPullback_pullback_evaluation _ w k).hom_ext (by simp) (by simp) }

@[reassoc (attr := simp)]
lemma constPullbackCone_π_app_fst {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) (cD : Cone D) {X' : C} (b : X' ⟶ X) (p' : X' ⟶ cD.pt)
    {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀) (hb : b ≫ a = p' ≫ w₀) (j : J) :
    (constPullbackCone a w cD b p' hw₀ hb).π.app j ≫
      (pullback.fst ((Functor.const J).map a) w).app j = b :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma constPullbackCone_π_app_snd {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) (cD : Cone D) {X' : C} (b : X' ⟶ X) (p' : X' ⟶ cD.pt)
    {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀) (hb : b ≫ a = p' ≫ w₀) (j : J) :
    (constPullbackCone a w cD b p' hw₀ hb).π.app j ≫
      (pullback.snd ((Functor.const J).map a) w).app j = p' ≫ cD.π.app j :=
  IsPullback.lift_snd _ _ _ _

/-- Over a connected index category, the base change `X ×_W (lim D)` of a limit along a map
`a : X ⟶ W` is the limit of the base changes `X ×_W Dⱼ`. -/
noncomputable def isLimitConstPullbackCone [IsConnected J] {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) {cD : Cone D} (hD : IsLimit cD) {X' : C} (b : X' ⟶ X)
    (p' : X' ⟶ cD.pt) {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀)
    (hpb : IsPullback b p' a w₀) :
    IsLimit (constPullbackCone a w cD b p' hw₀ hpb.w) := by
  refine IsPullback.isLimitOfIsPullbackLimMap (isPullback_pullback_evaluation _ w)
    (isLimitConstCone J X) hD (isLimitConstCone J W) ?_
  have e₁ : (isLimitConstCone J X).map (constPullbackCone a w cD b p' hw₀ hpb.w)
      (pullback.fst ((Functor.const J).map a) w) = b :=
    (isLimitConstCone J X).hom_ext fun j ↦ by
      rw [IsLimit.map_π, constPullbackCone_π_app_fst]
      exact (Category.comp_id _).symm
  have e₂ : hD.map (constPullbackCone a w cD b p' hw₀ hpb.w)
      (pullback.snd ((Functor.const J).map a) w) = p' :=
    hD.hom_ext fun j ↦ by rw [IsLimit.map_π, constPullbackCone_π_app_snd]
  have e₃ : (isLimitConstCone J W).map (constCone J X) ((Functor.const J).map a) = a :=
    (isLimitConstCone J W).hom_ext fun j ↦ by
      rw [IsLimit.map_π]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have e₄ : (isLimitConstCone J W).map cD w = w₀ :=
    (isLimitConstCone J W).hom_ext fun j ↦ by
      rw [IsLimit.map_π]
      rw [hw₀]
      exact (Category.comp_id _).symm
  rw [e₁, e₂, e₃, e₄]
  exact hpb

end Limits

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A scheme which is quasi-compact and locally of finite type over a field is
quasi-separated. -/
lemma quasiSeparatedSpace_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] : QuasiSeparatedSpace X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  inferInstance

/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, the limit step over a limit
`Y' = lim Yᵢ` of the second factor: let `j : U ⟶ X` be an open immersion of schemes of finite type
over a field `L` and `Y' = lim Yᵢ` a cofiltered limit of affine `L`-schemes of finite type. If the
statement of `corollary-open-direct-image-over-field--2` holds for all data with `dim X + dim Y < N`
and `dim X + dim Yᵢ < N` for all `i`, then the base change maps of the square
`V = U ×_X W ⟶ W = X ×_L Y'` are isomorphisms. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_snd {L : Type u} [Field L]
    {X U : Scheme.{u}} (aX : X ⟶ Spec (.of L)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ X) [IsOpenImmersion j]
    {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
    (hc : IsLimit c) (qD : D ⟶ (Functor.const I).obj (Spec (.of L)))
    (ℓ : c.pt ⟶ Spec (.of L)) (hℓ : ∀ i, c.π.app i ≫ qD.app i = ℓ)
    [∀ i, IsAffine (D.obj i)] [∀ {i i' : I} (f : i ⟶ i'), IsAffineHom (D.map f)]
    [∀ i, LocallyOfFiniteType (qD.app i)]
    {W V : Scheme.{u}} {p : W ⟶ X} {r : W ⟶ c.pt} (hW : IsPullback p r aX ℓ)
    {e : V ⟶ U} {h : V ⟶ W} (sq : IsPullback e h j p) (n : ℕ) (hn : IsUnit (n : L))
    (hΛ : (n : Λ) = 0) {N : WithBot ℕ∞} (IH : Etale.OpenImmersionBaseChangeBelow Λ N)
    (hdim : ∀ i, topologicalKrullDim X + topologicalKrullDim (D.obj i) < N) (q : ℤ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : IsConnected I := IsCofiltered.isConnected I
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_field aX
  have : QuasiSeparated aX := QuasiSeparated.of_quasiSeparatedSpace aX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiCompact (show (constCone I U).pt ⟶ (constCone I X).pt from j) :=
    inferInstanceAs (QuasiCompact j)
  have : QuasiSeparated (show (constCone I U).pt ⟶ (constCone I X).pt from j) :=
    inferInstanceAs (QuasiSeparated j)
  let a' := (Functor.const I).map aX
  let XD := pullback a' qD
  let pD : XD ⟶ (Functor.const I).obj X := pullback.fst _ _
  let j' := (Functor.const I).map j
  let YD := pullback j' pD
  let eD : YD ⟶ (Functor.const I).obj U := pullback.fst _ _
  let hD : YD ⟶ XD := pullback.snd _ _
  have hX (i : I) := isPullback_pullback_evaluation a' qD i
  have hsq (i : I) : IsPullback (eD.app i) (hD.app i) (j'.app i) (pD.app i) :=
    isPullback_pullback_evaluation j' pD i
  let cX := constPullbackCone aX qD c p r hℓ hW.w
  have hXl : IsLimit cX := isLimitConstPullbackCone aX qD hc p r hℓ hW
  have hpX (i : I) : cX.π.app i ≫ pD.app i = p := constPullbackCone_π_app_fst _ _ _ _ _ _ _ i
  let cY := constPullbackCone j pD cX e h hpX sq.w
  have hYl : IsLimit cY := isLimitConstPullbackCone j pD hXl e h hpX sq
  have hqc (i : I) : QuasiCompact (j'.app i) := inferInstanceAs (QuasiCompact j)
  have hqs (i : I) : QuasiSeparated (j'.app i) := inferInstanceAs (QuasiSeparated j)
  have hcS (i : I) : CompactSpace (((Functor.const I).obj X).obj i) :=
    inferInstanceAs (CompactSpace X)
  have hqsS (i : I) : QuasiSeparatedSpace (((Functor.const I).obj X).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace X)
  have hcX (i : I) : CompactSpace (XD.obj i) := by
    have : QuasiCompact ((pullback.snd a' qD).app i) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) (hX i) (inferInstanceAs
        (QuasiCompact aX))
    exact QuasiCompact.compactSpace_of_compactSpace ((pullback.snd a' qD).app i)
  have hqsX (i : I) : QuasiSeparatedSpace (XD.obj i) := by
    have : QuasiSeparated ((pullback.snd a' qD).app i) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) (hX i) (inferInstanceAs
        (QuasiSeparated aX))
    exact quasiSeparatedSpace_of_quasiSeparated ((pullback.snd a' qD).app i)
  have haS {i i' : I} (f : i ⟶ i') : IsAffineHom (((Functor.const I).obj X).map f) :=
    inferInstanceAs (IsAffineHom (𝟙 X))
  have haT {i i' : I} (f : i ⟶ i') : IsAffineHom (((Functor.const I).obj U).map f) :=
    inferInstanceAs (IsAffineHom (𝟙 U))
  have haX {i i' : I} (f : i ⟶ i') : IsAffineHom (XD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const aX qD f).flip inferInstance
  have haY {i i' : I} (f : i ⟶ i') : IsAffineHom (YD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const j pD f).flip (haX f)
  refine Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall Λ pD j' eD hD hsq
    (isLimitConstCone I X) hXl (isLimitConstCone I U) hYl (p₀ := p) (g₀ := j) (e₀ := e)
    (h₀ := h) (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) sq q (fun i G ↦ ?_) F
  · rw [constPullbackCone_π_app_fst aX qD c p r hℓ hW.w i]
    exact Category.comp_id _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [constPullbackCone_π_app_fst j pD cX e h hpX sq.w i]
    exact Category.comp_id _
  · exact (constPullbackCone_π_app_snd j pD cX e h hpX sq.w i).symm
  · have : QuasiSeparatedSpace (((Functor.const I).obj (Spec (.of L))).obj i) :=
      inferInstanceAs (QuasiSeparatedSpace (Spec (.of L)))
    have : QuasiCompact (qD.app i) := quasiCompact_of_compactSpace _
    exact IH aX (qD.app i) j (pD.app i) ((pullback.snd a' qD).app i) (hX i) (eD.app i)
      (hD.app i) (hsq i) n hn hΛ (hdim i) q G

/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, the limit step over a limit
`X' = lim Xᵢ` of the first factor: let `X' = lim Xᵢ` be a cofiltered limit of affine schemes of
finite type over a field `L`, `j : U' ⟶ X'` a quasi-compact open immersion and `Y` a scheme of
finite type over `L`. If the statement of `corollary-open-direct-image-over-field--2` holds for all
data with `dim X + dim Y < N` and `dim Xᵢ + dim Y < N` for all `i`, then the base change maps of the
square `V = U' ×_{X'} W ⟶ W = X' ×_L Y` are isomorphisms. The open `U'` descends to an open `U₀` of
some `X_{i₀}` (blueprint `corollary-open-direct-image-over-field--2`), and the square is the limit
of the squares `U₀ ×_{X_{i₀}} Xᵢ ⟶ Xᵢ` base changed to `Xᵢ ×_L Y`, for `i ⟶ i₀`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_fst {L : Type u} [Field L]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of L)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
    (hc : IsLimit c) (qD : D ⟶ (Functor.const I).obj (Spec (.of L)))
    (ℓ : c.pt ⟶ Spec (.of L)) (hℓ : ∀ i, c.π.app i ≫ qD.app i = ℓ)
    [∀ i, IsAffine (D.obj i)] [∀ {i i' : I} (f : i ⟶ i'), IsAffineHom (D.map f)]
    [∀ i, LocallyOfFiniteType (qD.app i)]
    {U' : Scheme.{u}} (j : U' ⟶ c.pt) [IsOpenImmersion j] [QuasiCompact j] [CompactSpace U']
    {W V : Scheme.{u}} {p : W ⟶ c.pt} {r : W ⟶ Y} (hW : IsPullback p r ℓ aY)
    {e : V ⟶ U'} {h : V ⟶ W} (sq : IsPullback e h j p) (n : ℕ) (hn : IsUnit (n : L))
    (hΛ : (n : Λ) = 0) {N : WithBot ℕ∞} (IH : Etale.OpenImmersionBaseChangeBelow Λ N)
    (hdim : ∀ i, topologicalKrullDim (D.obj i) + topologicalKrullDim Y < N) (q : ℤ)
    (F : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_field aY
  have : QuasiSeparated aY := QuasiSeparated.of_quasiSeparatedSpace aY
  -- descend the open `U'` to an open `U₀` of some `X_{i₀}`
  obtain ⟨i₀, U₀, hU₀c, hU₀⟩ := Scheme.exists_preimage_eq_of_isAffine D hc j.opensRange
    (by simpa using isCompact_range j.continuous)
  have : CompactSpace U₀ := isCompact_iff_compactSpace.mp hU₀c
  have hrange : Set.range (j ≫ c.π.app i₀).base ⊆ Set.range U₀.ι.base := by
    rintro _ ⟨x, rfl⟩
    have hx : j.base x ∈ c.π.app i₀ ⁻¹ᵁ U₀ := by
      rw [hU₀]
      simp
    simpa using hx
  let uU : U' ⟶ U₀ := IsOpenImmersion.lift U₀.ι (j ≫ c.π.app i₀) hrange
  have huU : uU ≫ U₀.ι = j ≫ c.π.app i₀ := IsOpenImmersion.lift_fac _ _ _
  have hUpb : IsPullback uU j U₀.ι (c.π.app i₀) :=
    IsOpenImmersion.isPullback uU j U₀.ι (c.π.app i₀) huU.symm (by simpa using hU₀)
  -- restrict the system to the indices over `i₀`
  let Φ := Over.forget i₀
  let D' := Φ ⋙ D
  have hc' : IsLimit (c.whisker Φ) := (Functor.Initial.isLimitWhiskerEquiv Φ c).symm hc
  have : IsConnected (Over i₀) := IsCofiltered.isConnected _
  let qD' : D' ⟶ (Functor.const (Over i₀)).obj (Spec (.of L)) :=
    { app k := qD.app k.left
      naturality k k' f := qD.naturality f.left }
  let w' : D' ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) :=
    { app k := D.map k.hom
      naturality k k' f := by
        simp only [D', Φ, Functor.comp_obj, Over.forget_obj, Functor.comp_map, Over.forget_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, ← D.map_comp,
          Over.w f] }
  have hℓ' (k : Over i₀) : (c.whisker Φ).π.app k ≫ qD'.app k = ℓ := hℓ k.left
  have hw' (k : Over i₀) : (c.whisker Φ).π.app k ≫ w'.app k = c.π.app i₀ := by
    exact c.w k.hom
  -- the systems of schemes and the cartesian squares
  let XD := pullback ((Functor.const (Over i₀)).map aY) qD'
  let pD : XD ⟶ D' := pullback.snd _ _
  let TD := pullback ((Functor.const (Over i₀)).map U₀.ι) w'
  let gD : TD ⟶ D' := pullback.snd _ _
  let YD := pullback ((Functor.const (Over i₀)).map U₀.ι) (pD ≫ w')
  let hD : YD ⟶ XD := pullback.snd _ _
  let eD : YD ⟶ TD := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pD)
    (by rw [pullback.condition, Category.assoc])
  have hX (k : Over i₀) := isPullback_pullback_evaluation ((Functor.const (Over i₀)).map aY) qD' k
  have hT (k : Over i₀) := isPullback_pullback_evaluation ((Functor.const (Over i₀)).map U₀.ι) w' k
  have heD₁ (k : Over i₀) :
      eD.app k ≫ (pullback.fst ((Functor.const (Over i₀)).map U₀.ι) w').app k =
      (pullback.fst ((Functor.const (Over i₀)).map U₀.ι) (pD ≫ w')).app k := by
    rw [← NatTrans.comp_app, pullback.lift_fst]
  have heD₂ (k : Over i₀) : eD.app k ≫ gD.app k = hD.app k ≫ pD.app k := by
    rw [← NatTrans.comp_app, pullback.lift_snd, NatTrans.comp_app]
  have hsq (k : Over i₀) : IsPullback (eD.app k) (hD.app k) (gD.app k) (pD.app k) := by
    refine IsPullback.of_right ?_ (heD₂ k) (hT k)
    rw [heD₁ k]
    simpa using isPullback_pullback_evaluation ((Functor.const (Over i₀)).map U₀.ι) (pD ≫ w') k
  -- the limit cones
  let cX := constPullbackCone aY qD' (c.whisker Φ) r p hℓ' hW.flip.w
  have hXl : IsLimit cX := isLimitConstPullbackCone aY qD' hc' r p hℓ' hW.flip
  let cT := constPullbackCone U₀.ι w' (c.whisker Φ) uU j hw' hUpb.w
  have hTl : IsLimit cT := isLimitConstPullbackCone U₀.ι w' hc' uU j hw' hUpb
  have hwX (k : Over i₀) : cX.π.app k ≫ (pD ≫ w').app k = p ≫ c.π.app i₀ := by
    rw [NatTrans.comp_app, constPullbackCone_π_app_snd_assoc, hw']
  have hYpb : IsPullback (e ≫ uU) h U₀.ι (p ≫ c.π.app i₀) := sq.paste_horiz hUpb
  let cY := constPullbackCone U₀.ι (pD ≫ w') cX (e ≫ uU) h hwX hYpb.w
  have hYl : IsLimit cY := isLimitConstPullbackCone U₀.ι (pD ≫ w') hXl (e ≫ uU) h hwX hYpb
  -- the finiteness conditions
  have hgD (k : Over i₀) : IsOpenImmersion (gD.app k) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hT k) (inferInstanceAs
      (IsOpenImmersion U₀.ι))
  have hqc (k : Over i₀) : QuasiCompact (gD.app k) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hT k) (inferInstanceAs
      (QuasiCompact U₀.ι))
  have hqs (k : Over i₀) : QuasiSeparated (gD.app k) := inferInstance
  have hS (k : Over i₀) : IsAffine (D'.obj k) := inferInstanceAs (IsAffine (D.obj k.left))
  have hcS (k : Over i₀) : CompactSpace (D'.obj k) := inferInstance
  have hqsS (k : Over i₀) : QuasiSeparatedSpace (D'.obj k) := inferInstance
  have hcX (k : Over i₀) : CompactSpace (XD.obj k) := by
    have : QuasiCompact (pD.app k) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) (hX k) (inferInstanceAs
        (QuasiCompact aY))
    exact QuasiCompact.compactSpace_of_compactSpace (pD.app k)
  have hqsX (k : Over i₀) : QuasiSeparatedSpace (XD.obj k) := by
    have : QuasiSeparated (pD.app k) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) (hX k) (inferInstanceAs
        (QuasiSeparated aY))
    exact quasiSeparatedSpace_of_quasiSeparated (pD.app k)
  have haS {k k' : Over i₀} (f : k ⟶ k') : IsAffineHom (D'.map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  have haX {k k' : Over i₀} (f : k ⟶ k') : IsAffineHom (XD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const aY qD' f).flip (haS f)
  have haT {k k' : Over i₀} (f : k ⟶ k') : IsAffineHom (TD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const U₀.ι w' f).flip (haS f)
  have haY {k k' : Over i₀} (f : k ⟶ k') : IsAffineHom (YD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const U₀.ι (pD ≫ w') f).flip (haX f)
  refine Etale.isIso_baseChangeHomologyMap_of_isLimit_of_forall Λ pD gD eD hD hsq
    hc' hXl hTl hYl (p₀ := p) (g₀ := j) (e₀ := e) (h₀ := h) (fun k ↦ ?_) (fun k ↦ ?_)
    (fun k ↦ ?_) (fun k ↦ ?_) sq q (fun k G ↦ ?_) F
  · exact (constPullbackCone_π_app_snd aY qD' (c.whisker Φ) r p hℓ' hW.flip.w k).symm
  · exact (constPullbackCone_π_app_snd U₀.ι w' (c.whisker Φ) uU j hw' hUpb.w k).symm
  · refine (hT k).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, heD₁ k,
        constPullbackCone_π_app_fst U₀.ι w' (c.whisker Φ) uU j hw' hUpb.w k,
        constPullbackCone_π_app_fst U₀.ι (pD ≫ w') cX (e ≫ uU) h hwX hYpb.w k]
    · rw [Category.assoc, Category.assoc, heD₂ k,
        constPullbackCone_π_app_snd U₀.ι w' (c.whisker Φ) uU j hw' hUpb.w k,
        constPullbackCone_π_app_snd_assoc U₀.ι (pD ≫ w') cX (e ≫ uU) h hwX hYpb.w k]
      exact (sq.w_assoc _).trans (congrArg (h ≫ ·)
        (constPullbackCone_π_app_snd aY qD' (c.whisker Φ) r p hℓ' hW.flip.w k).symm)
  · exact (constPullbackCone_π_app_snd U₀.ι (pD ≫ w') cX (e ≫ uU) h hwX hYpb.w k).symm
  · have : LocallyOfFiniteType (qD'.app k) :=
      inferInstanceAs (LocallyOfFiniteType (qD.app k.left))
    have : QuasiSeparatedSpace (((Functor.const (Over i₀)).obj (Spec (.of L))).obj k) :=
      inferInstanceAs (QuasiSeparatedSpace (Spec (.of L)))
    have : QuasiCompact (qD'.app k) := quasiCompact_of_compactSpace _
    exact IH (qD'.app k) aY (gD.app k) (pD.app k)
      ((pullback.fst ((Functor.const (Over i₀)).map aY) qD').app k) (hX k).flip
      (eD.app k) (hD.app k) (hsq k) n hn hΛ (hdim k.left) q G

end AlgebraicGeometry
