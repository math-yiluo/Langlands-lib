/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.FiniteOrbit
public import WeilConjectures.AlgebraicGeometry.AffineFibreProductTransition
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.NormalEtale
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Generic connectedness of pro-étale schemes over normal schemes

Let `Y` be a normal locally Noetherian scheme (its local rings are integrally closed domains)
with generic point `η`. A limit `W = lim Wᵢ` of a cofiltered diagram of affine schemes étale over
`Y` is generically connected relative to `η` (`AlgebraicGeometry.IsGenericallyConnected`,
`AlgebraicGeometry.isGenericallyConnected_of_isLimit`): an open neighbourhood of a diagonal point
of `W ×_Y W` contains the preimage of an open of some `Wᵢ ×_Y Wᵢ` (`W ×_Y W` being the limit of
the `Wᵢ ×_Y Wᵢ`), the stage `Wᵢ` is normal (Stacks 033C), so its local rings are domains and it
is locally irreducible (`AlgebraicGeometry.exists_isOpen_specializes_of_isDomain_stalk`), and
points of an irreducible open of `Wᵢ` lying over `η` are its generic point, `Wᵢ ⟶ Y` having
discrete fibres.

Every weakly étale `f : V ⟶ Y` with `V` quasi-compact admits a surjective submersive morphism
`j : W ⟶ V` from such a `W`, by Stacks 097Z (a weakly étale algebra is ind-étale locally
ind-étale) (`AlgebraicGeometry.exists_isGenericallyConnected_cover_of_isIntegrallyClosed_stalk`;
the regular case is `AlgebraicGeometry.exists_isGenericallyConnected_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C] {J : Type*} [Category J] {D : J ⥤ C} {S X : C}
  (t : D ⟶ (Functor.const J).obj S)

/-- The diagram `j ↦ Dⱼ ×_S Dⱼ` of a diagram `D` over `S`. -/
@[simps]
noncomputable def pullbackDiagramSelf : J ⥤ C where
  obj j := pullback (t.app j) (t.app j)
  map u := pullback.map _ _ _ _ (D.map u) (D.map u) (𝟙 S) (by simp) (by simp)
  map_id j := by ext <;> simp
  map_comp u v := by ext <;> simp

variable {t} (s : (Functor.const J).obj X ⟶ D) (h : X ⟶ S) (hh : ∀ j, s.app j ≫ t.app j = h)

/-- The cone `X ×_S X ⟶ Dⱼ ×_S Dⱼ` over `pullbackDiagramSelf t`. -/
@[simps]
noncomputable def pullbackConeSelf : Cone (pullbackDiagramSelf t) where
  pt := pullback h h
  π :=
    { app j := pullback.map h h _ _ (s.app j) (s.app j) (𝟙 S) (by simp [hh]) (by simp [hh])
      naturality u v w := by
        have hw : s.app u ≫ D.map w = s.app v := by simpa using (s.naturality w).symm
        dsimp
        rw [Category.id_comp]
        refine pullback.hom_ext ?_ ?_ <;> simp [hw] }

/-- The cone over `D` given by the first (`b = false`) or second projections of a cone over
`pullbackDiagramSelf t`. -/
@[simps]
noncomputable def coneOfPullbackDiagramSelf (c : Cone (pullbackDiagramSelf t)) (b : Bool) :
    Cone D where
  pt := c.pt
  π :=
    { app j := c.π.app j ≫ if b then pullback.snd _ _ else pullback.fst _ _
      naturality u v w := by
        have := c.π.naturality w
        dsimp at this ⊢
        rw [Category.id_comp] at this
        rw [Category.id_comp, this]
        cases b <;> simp }

/-- **Fibre products commute with limits**: if `X = lim Dⱼ` over `S` (and the index category is
nonempty), then `X ×_S X = lim (Dⱼ ×_S Dⱼ)`. -/
noncomputable def isLimitPullbackConeSelf [Nonempty J] (hs : IsLimit (Cone.mk X s)) :
    IsLimit (pullbackConeSelf s h hh) where
  lift c := pullback.lift (hs.lift (coneOfPullbackDiagramSelf c false))
    (hs.lift (coneOfPullbackDiagramSelf c true)) (by
      obtain ⟨j⟩ := ‹Nonempty J›
      rw [← hh j]
      have h₁ := hs.fac (coneOfPullbackDiagramSelf c false) j
      have h₂ := hs.fac (coneOfPullbackDiagramSelf c true) j
      simp only [coneOfPullbackDiagramSelf_π_app] at h₁ h₂
      simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      rw [reassoc_of% h₁, reassoc_of% h₂]
      exact c.π.app j ≫= pullback.condition)
  fac c j := by
    refine pullback.hom_ext ?_ ?_
    · have := hs.fac (coneOfPullbackDiagramSelf c false) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        Bool.false_eq_true, ↓reduceIte] at this
      rw [Category.assoc, pullbackConeSelf_π_app, pullback.lift_fst, pullback.lift_fst_assoc, this]
    · have := hs.fac (coneOfPullbackDiagramSelf c true) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        ↓reduceIte] at this
      rw [Category.assoc, pullbackConeSelf_π_app, pullback.lift_snd, pullback.lift_snd_assoc, this]
  uniq c m hm := by
    refine pullback.hom_ext (hs.hom_ext fun j ↦ ?_) (hs.hom_ext fun j ↦ ?_)
    · have h₁ := congrArg (· ≫ pullback.fst _ _) (hm j)
      have h₂ := hs.fac (coneOfPullbackDiagramSelf c false) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        Bool.false_eq_true, ↓reduceIte] at h₂
      simp only [pullbackConeSelf_π_app, Category.assoc,
        pullback.lift_fst] at h₁
      simp only [Category.assoc, pullback.lift_fst_assoc]
      rw [h₁, h₂]
    · have h₁ := congrArg (· ≫ pullback.snd _ _) (hm j)
      have h₂ := hs.fac (coneOfPullbackDiagramSelf c true) j
      simp only [coneOfPullbackDiagramSelf_π_app,
        ↓reduceIte] at h₂
      simp only [pullbackConeSelf_π_app, Category.assoc,
        pullback.lift_snd] at h₁
      simp only [Category.assoc, pullback.lift_snd_assoc]
      rw [h₁, h₂]

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A connected locally Noetherian scheme whose local rings are integral domains is integral:
it is irreducible (`AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`) and reduced. This
applies to connected locally Noetherian normal schemes. -/
theorem isIntegral_of_isDomain_stalk (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X :=
  have := irreducibleSpace_of_isDomain_stalk X h
  have := isReduced_of_isReduced_stalk X
  isIntegral_of_irreducibleSpace_of_isReduced X

/-- A locally Noetherian scheme whose local rings are integral domains is locally irreducible:
every point has an open neighbourhood consisting of specializations of a single point. Indeed
the connected component of the point is open, and irreducible
(`AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`). -/
lemma exists_isOpen_specializes_of_isDomain_stalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    ∃ (O : Set X) (ξ : X), IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O, ξ ⤳ y := by
  let O : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have : ConnectedSpace O := Subtype.connectedSpace isConnected_connectedComponent
  have : IrreducibleSpace O.toScheme := irreducibleSpace_of_isDomain_stalk O fun y ↦
    have := h y.1
    MulEquiv.isDomain _ (O.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨O, O.ι.base (genericPoint O.toScheme), O.isOpen, mem_connectedComponent, ?_⟩
  intro y hy
  let y' : O.toScheme := ⟨y, hy⟩
  have := (genericPoint_specializes y').map O.ι.base.hom.continuous
  simpa only [Scheme.Opens.ι_apply] using this

/-- A regular locally Noetherian scheme is locally irreducible: every point has an open
neighbourhood consisting of specializations of a single point, its local rings being domains
(`AlgebraicGeometry.exists_isOpen_specializes_of_isDomain_stalk`). -/
lemma IsRegular.exists_isOpen_specializes (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    (x : X) : ∃ (O : Set X) (ξ : X), IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O, ξ ⤳ y :=
  exists_isOpen_specializes_of_isDomain_stalk X (fun _ ↦ inferInstance) x

/-- **Generic connectedness of pro-étale limits.** Let `h : W ⟶ Y` be a cofiltered limit of
affine schemes `Dⱼ` over `Y` with locally quasi-finite (e.g. étale) structure maps, and assume
every point of every `Dⱼ` has an open neighbourhood consisting of specializations of a single
point (e.g. `Dⱼ` locally Noetherian with integral local rings, such as `Dⱼ` normal or regular).
Then `h` is generically connected relative to any point `η` of `Y` specializing to every point
(`AlgebraicGeometry.IsGenericallyConnected`). -/
theorem isGenericallyConnected_of_isLimit {W Y : Scheme.{u}} (h : W ⟶ Y) {J : Type u}
    [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}} {t : D ⟶ (Functor.const J).obj Y}
    {s : (Functor.const J).obj W ⟶ D} (hs : IsLimit (Cone.mk W s))
    (hh : ∀ j, s.app j ≫ t.app j = h) [∀ j, IsAffine (D.obj j)]
    [∀ j, LocallyQuasiFinite (t.app j)]
    (hirr : ∀ j (q : D.obj j), ∃ (O : Set (D.obj j)) (ξ : D.obj j), IsOpen O ∧ q ∈ O ∧
      ∀ y ∈ O, ξ ⤳ y)
    {η : Y} (hη : ∀ y, η ⤳ y) : IsGenericallyConnected h η := by
  intro w Ω hΩ hw
  have : Nonempty J := IsCofiltered.nonempty
  have hlim := isLimitPullbackConeSelf s h hh hs
  have : IsAffineHom (𝟙 Y) := inferInstance
  have : ∀ {i j : J} (u : i ⟶ j), IsAffineHom ((pullbackDiagramSelf t).map u) := fun u ↦
    isAffineHom_pullback_map (t.app _) (t.app _) (t.app _) (t.app _) (D.map u) (𝟙 Y) (D.map u)
      (by simp) (by simp)
  obtain ⟨_, ⟨_, ⟨j, V, -, rfl⟩, rfl⟩, hwV, hVΩ⟩ :=
    (isBasis_preimage_isAffineOpen _ _ hlim).exists_subset_of_mem_open hw hΩ
  set sj : W ⟶ D.obj j := s.app j
  set πj := (pullbackConeSelf s h hh).π.app j
  have hΔ : pullback.diagonal h ≫ πj = sj ≫ pullback.diagonal (t.app j) :=
    pullback.hom_ext (by simp [πj, sj]) (by simp [πj, sj])
  have hwV' : (pullback.diagonal (t.app j)).base (sj.base w) ∈ V := by
    rw [← Scheme.Hom.comp_apply, ← hΔ, Scheme.Hom.comp_apply]
    exact hwV
  obtain ⟨O, ξ, hO, hwO, hξ⟩ := hirr j (sj.base w)
  let V' : Set ↥(pullback (t.app j) (t.app j)) := (V : Set ((pullbackDiagramSelf t).obj j))
  have hV' : IsOpen V' := V.isOpen
  refine ⟨sj.base ⁻¹' (O ∩ (pullback.diagonal (t.app j)).base ⁻¹' V'),
    ((hO.inter (hV'.preimage (pullback.diagonal (t.app j)).base.hom.continuous)).preimage
      sj.base.hom.continuous).mem_nhds ⟨hwO, hwV'⟩, ?_⟩
  rintro w₁ ⟨hw₁O, -⟩ a b ha hb haη hbη
  have htξ (q : D.obj j) (hq : q ∈ O) (hqη : (t.app j).base q = η) : (t.app j).base ξ = η :=
    (((hξ q hq).map (t.app j).base.hom.continuous).antisymm (by rw [hqη]; exact hη _)).eq.trans
      hqη
  have hξq (q : D.obj j) (hq : q ∈ O) (hqη : (t.app j).base q = η) : ξ = q :=
    (t.app j).eq_of_specializes_of_apply_eq (hξ q hq) ((htξ q hq hqη).trans hqη.symm)
  have hsη (c : W) (hc : h.base c = η) : (t.app j).base (sj.base c) = η := by
    rw [← Scheme.Hom.comp_apply, hh]
    exact hc
  have haO : sj.base a ∈ O := (ha.map sj.base.hom.continuous).mem_open hO hw₁O
  have hbO : sj.base b ∈ O := (hb.map sj.base.hom.continuous).mem_open hO hwO
  have haξ := hξq _ haO (hsη a haη)
  have hbξ := hξq _ hbO (hsη b hbη)
  obtain ⟨ρ, hρ₁, hρ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := sj) (g := sj) a b
    (haξ.symm.trans hbξ)
  let M : pullback sj sj ⟶ pullback h h :=
    pullback.map sj sj h h (𝟙 _) (𝟙 _) (t.app j) (by simp [sj, hh]) (by simp [sj, hh])
  have hM : M ≫ πj = pullback.fst sj sj ≫ sj ≫ pullback.diagonal (t.app j) := by
    refine pullback.hom_ext ?_ ?_
    · simp [M, πj, sj]
    · simp [M, πj, sj, pullback.condition]
  refine ⟨M.base ρ, hVΩ ?_, ?_, ?_⟩
  · change (M ≫ πj).base ρ ∈ V'
    rw [hM, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hρ₁, ← haξ]
    exact ((hξ _ hwO).map (pullback.diagonal (t.app j)).base.hom.continuous).mem_open hV'
      hwV'
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Category.comp_id, hρ₁]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id, hρ₂]

/-- Generic connectedness is local on the source: it can be checked on an open immersion. -/
lemma IsGenericallyConnectedAt.of_openImmersion {O W Y : Scheme.{u}} (ι : O ⟶ W)
    [IsOpenImmersion ι] (h : W ⟶ Y) {η : Y} {w₀ : O}
    (H : IsGenericallyConnectedAt (ι ≫ h) η w₀) : IsGenericallyConnectedAt h η (ι.base w₀) := by
  intro Ω hΩ hw
  let m : pullback (ι ≫ h) (ι ≫ h) ⟶ pullback h h :=
    pullback.map _ _ _ _ ι ι (𝟙 Y) (by simp) (by simp)
  have hm : pullback.diagonal (ι ≫ h) ≫ m = ι ≫ pullback.diagonal h :=
    pullback.hom_ext (by simp [m]) (by simp [m])
  obtain ⟨U₀, hU₀, hU₀p⟩ := H (m.base ⁻¹' Ω) (hΩ.preimage m.base.hom.continuous) (by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply]
    exact hw)
  have hgen {w₁ : O} {a : W} (ha : a ⤳ ι.base w₁) : ∃ a₀, ι.base a₀ = a ∧ a₀ ⤳ w₁ := by
    obtain ⟨a₀, rfl⟩ : a ∈ Set.range ι.base :=
      ha.mem_open ι.isOpenEmbedding.isOpen_range ⟨w₁, rfl⟩
    exact ⟨a₀, rfl, ι.isOpenEmbedding.isInducing.specializes_iff.mp ha⟩
  refine ⟨ι.base '' U₀, ι.isOpenEmbedding.image_mem_nhds.mpr hU₀, ?_⟩
  rintro _ ⟨w₁, hw₁, rfl⟩ a b ha hb haη hbη
  obtain ⟨a₀, rfl, ha₀⟩ := hgen ha
  obtain ⟨b₀, rfl, hb₀⟩ := hgen hb
  obtain ⟨z, hz, h₁, h₂⟩ := hU₀p w₁ hw₁ a₀ b₀ ha₀ hb₀ haη hbη
  refine ⟨m.base z, hz, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, h₁]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, h₂]

/-- The spectrum of an ind-étale algebra over an affine open of a normal locally Noetherian
scheme `Y` is generically connected over `Y`: it is the limit of a cofiltered diagram of affine
schemes étale over `Y`, which are locally Noetherian with integral local rings (Stacks 033C,
`AlgebraicGeometry.Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain`). -/
lemma isGenericallyConnected_SpecMap_comp_fromSpec_of_isIntegrallyClosed_stalk {Y : Scheme.{u}}
    [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    {U : Y.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{u}} (ψ : Γ(Y, U) ⟶ T)
    (hψ : ψ.hom.IndEtale) {η : Y} (hη : ∀ y, η ⤳ y) :
    IsGenericallyConnected (Spec.map ψ ≫ hU.fromSpec) η := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := proAffineEtale_Spec_iff.mpr hψ
  have (j : J) : IsAffine (D.obj j) := MorphismProperty.ofObjectProperty_top_right_iff.mp
    (hts j).1.2
  have (j : J) : Etale (t.app j) := (hts j).1.1
  let t' : D ⟶ (Functor.const J).obj Y := t ≫ (Functor.const J).map hU.fromSpec
  have ht' (j : J) : t'.app j = t.app j ≫ hU.fromSpec := rfl
  have (j : J) : LocallyQuasiFinite (t'.app j) := by
    rw [ht']
    infer_instance
  refine isGenericallyConnected_of_isLimit _ hs (t := t') (fun j ↦ by
    rw [ht', ← Category.assoc, (hts j).2]) (fun j q ↦ ?_) hη
  have : IsLocallyNoetherian (D.obj j) :=
    LocallyOfFiniteType.isLocallyNoetherian (t.app j ≫ hU.fromSpec)
  exact exists_isOpen_specializes_of_isDomain_stalk _ (fun x ↦
    (Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain
      (t.app j ≫ hU.fromSpec) hY x).1) q

/-- The spectrum of an ind-étale algebra over an affine open of a regular locally Noetherian
scheme `Y` is generically connected over `Y`: regular schemes are normal
(`AlgebraicGeometry.isGenericallyConnected_SpecMap_comp_fromSpec_of_isIntegrallyClosed_stalk`). -/
lemma isGenericallyConnected_SpecMap_comp_fromSpec {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsRegular Y] {U : Y.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{u}} (ψ : Γ(Y, U) ⟶ T)
    (hψ : ψ.hom.IndEtale) {η : Y} (hη : ∀ y, η ⤳ y) :
    IsGenericallyConnected (Spec.map ψ ≫ hU.fromSpec) η :=
  isGenericallyConnected_SpecMap_comp_fromSpec_of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk y⟩) hU ψ hψ hη

/-- **Generically connected covers.** Let `Y` be a normal locally Noetherian scheme, `η` a
point of `Y` specializing to every point, and `f : V ⟶ Y` weakly étale with `V`
quasi-compact. There is a flat surjective submersive morphism `j : W ⟶ V` from an affine
scheme such that `j ≫ f` is generically connected relative to `η`: cover `V` by finitely many
affine opens `Spec B` mapping to affine opens `Spec R` of `Y`, and take `W = ∐ Spec C` for
faithfully flat ind-étale `B`-algebras `C` which are ind-étale over `R` (Stacks 097Z,
`Algebra.WeaklyEtale.exists_indEtale`). -/
theorem exists_isGenericallyConnected_cover_of_isIntegrallyClosed_stalk {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : V ⟶ Y) [WeaklyEtale f] [CompactSpace V] {η : Y} (hη : ∀ y, η ⤳ y) :
    ∃ (W : Scheme.{u}) (j : W ⟶ V), IsAffine W ∧ Flat j ∧ Function.Surjective j.base ∧
      (∀ E : Set V, IsOpen (j.base ⁻¹' E) → IsOpen E) ∧ IsGenericallyConnected (j ≫ f) η := by
  classical
  -- affine opens of `V` mapping into affine opens of `Y`
  have hloc (x : V) : ∃ (U : Y.Opens) (Vx : V.Opens), IsAffineOpen U ∧ IsAffineOpen Vx ∧
      x ∈ Vx ∧ Vx ≤ f ⁻¹ᵁ U := by
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := ⊤) trivial
    obtain ⟨Vx, hVx, hxV, hle⟩ :=
      exists_isAffineOpen_mem_and_subset (X := V) (x := x) (U := f ⁻¹ᵁ U) hxU
    exact ⟨U, Vx, hU, hVx, hxV, hle⟩
  choose U Vx hU hVx hxV hle using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (Vx x : Set V))
    (fun x ↦ (Vx x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  -- Stacks 097Z on each piece
  have hpiece (x : V) : ∃ (T : CommRingCat.{u}) (g : Γ(V, Vx x) ⟶ T), g.hom.FaithfullyFlat ∧
      (f.appLE (U x) (Vx x) (hle x) ≫ g).hom.IndEtale := by
    have hw : (f.appLE (U x) (Vx x) (hle x)).hom.WeaklyEtale :=
      HasRingHomProperty.appLE @WeaklyEtale f inferInstance ⟨U x, hU x⟩ ⟨Vx x, hVx x⟩ (hle x)
    obtain ⟨T, _, g, -, h₂, h₃⟩ := hw.exists_indEtale_comp
    exact ⟨.of T, CommRingCat.ofHom g, h₂, h₃⟩
  choose T g hg₂ hg₃ using hpiece
  let π (x : V) : Spec (T x) ⟶ V := Spec.map (g x) ≫ (hVx x).fromSpec
  have hπf (x : V) : π x ≫ f =
      Spec.map (f.appLE (U x) (Vx x) (hle x) ≫ g x) ≫ (hU x).fromSpec := by
    simp only [π, Spec.map_comp, Category.assoc]
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f (hU x) (hVx x) (hle x)]
  have hflat (x : V) : Flat (Spec.map (g x)) ∧ Surjective (Spec.map (g x)) :=
    (flat_and_surjective_SpecMap_iff _).2 (hg₂ x)
  let W := ∐ fun x : t ↦ Spec (T x.1)
  let j : W ⟶ V := Sigma.desc fun x : t ↦ π x.1
  have hιj (x : t) : Sigma.ι (fun x : t ↦ Spec (T x.1)) x ≫ j = π x.1 := Sigma.ι_comp_desc _ _
  refine ⟨W, j, inferInstance, ?_, fun v ↦ ?_, fun E hE ↦ ?_, fun w ↦ ?_⟩
  · have (x : t) : Flat (π x.1) := by
      have := (hflat x.1).1
      infer_instance
    infer_instance
  · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
    obtain ⟨p, hp⟩ : v ∈ Set.range (hVx x).fromSpec.base := by
      rw [IsAffineOpen.range_fromSpec]
      exact hx
    have := (hflat x).2
    obtain ⟨q, rfl⟩ := (Spec.map (g x)).surjective p
    refine ⟨(Sigma.ι (fun x : t ↦ Spec (T x.1)) ⟨x, hxt⟩).base q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hιj, ← hp, Scheme.Hom.comp_apply]
  · have hcov : E = ⋃ x ∈ t, (hVx x).fromSpec.base '' ((hVx x).fromSpec.base ⁻¹' E) := by
      ext v
      simp only [Set.mem_iUnion, Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
        Set.mem_inter_iff, exists_and_left, exists_prop]
      refine ⟨fun hv ↦ ⟨hv, ?_⟩, fun h ↦ h.1⟩
      obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
      exact ⟨x, hxt, hx⟩
    rw [hcov]
    refine isOpen_biUnion fun x hxt ↦ (hVx x).fromSpec.isOpenEmbedding.isOpenMap _ ?_
    have := (hflat x).1
    have := (hflat x).2
    refine (Flat.isQuotientMap_of_surjective (Spec.map (g x))).isOpen_preimage.mp ?_
    have h₁ : (π x).base ⁻¹' E =
        (Sigma.ι (fun x : t ↦ Spec (T x.1)) ⟨x, hxt⟩).base ⁻¹' (j.base ⁻¹' E) := by
      rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hιj]
    have h₂ := hE.preimage (Sigma.ι (fun x : t ↦ Spec (T x.1)) ⟨x, hxt⟩).base.hom.continuous
    rw [← h₁] at h₂
    rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at h₂
  · obtain ⟨⟨x, q⟩, rfl⟩ := (sigmaMk fun x : t ↦ Spec (T x.1)).surjective w
    rw [sigmaMk_mk]
    refine IsGenericallyConnectedAt.of_openImmersion _ _ ?_
    have : Sigma.ι (fun x : t ↦ Spec (T x.1)) x ≫ j ≫ f =
        Spec.map (f.appLE (U x) (Vx x) (hle x) ≫ g x) ≫ (hU x).fromSpec := by
      rw [reassoc_of% hιj, hπf]
    rw [this]
    exact isGenericallyConnected_SpecMap_comp_fromSpec_of_isIntegrallyClosed_stalk hY (hU x) _
      (hg₃ x) hη q

/-- **Generically connected covers** of a regular locally Noetherian scheme: regular schemes
are normal (`AlgebraicGeometry.exists_isGenericallyConnected_cover_of_isIntegrallyClosed_stalk`).
-/
theorem exists_isGenericallyConnected_cover {Y V : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsRegular Y] (f : V ⟶ Y) [WeaklyEtale f] [CompactSpace V] {η : Y} (hη : ∀ y, η ⤳ y) :
    ∃ (W : Scheme.{u}) (j : W ⟶ V), IsAffine W ∧ Flat j ∧ Function.Surjective j.base ∧
      (∀ E : Set V, IsOpen (j.base ⁻¹' E) → IsOpen E) ∧ IsGenericallyConnected (j ≫ f) η :=
  exists_isGenericallyConnected_cover_of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk y⟩) f hη

end AlgebraicGeometry
