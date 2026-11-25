/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Pro.HypercoverColimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-!
# Continuity of the comparison pullback

Let `S` be a scheme and `F` an étale sheaf on `S` with values in a Grothendieck abelian category.
If `Y = limᵢ Dᵢ` is a cofiltered limit of quasi-compact quasi-separated étale `S`-schemes with
affine transition maps, then the sections of the comparison pullback `ν^* F` over `Y` are the
filtered colimit of the sections over the `Dᵢ`
(`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- If a natural transformation `α : G ⟶ H` is an isomorphism at all objects of a cocone `c`,
then `H.mapCocone c` is a colimit as soon as `G.mapCocone c` is. -/
noncomputable def isColimitMapCoconeOfNatTrans {C D J : Type*} [Category* C] [Category* D]
    [Category* J] (G H : C ⥤ D) (α : G ⟶ H) {K : J ⥤ C} (c : Cocone K)
    [∀ j, IsIso (α.app (K.obj j))] [IsIso (α.app c.pt)] (hc : IsColimit (G.mapCocone c)) :
    IsColimit (H.mapCocone c) := by
  let e : K ⋙ G ≅ K ⋙ H := NatIso.ofComponents (fun j ↦ asIso (α.app (K.obj j)))
    (fun f ↦ α.naturality (K.map f))
  refine (IsColimit.precomposeHomEquiv e _).1 (hc.ofIsoColimit (Cocone.ext (asIso (α.app c.pt))
    fun j ↦ ?_))
  simp [e]

/-- A cone in the pro-étale site over a cofiltered diagram of étale `S`-schemes whose
underlying cone of schemes is a limit is a limit cone. -/
noncomputable def isLimitOfIsLimitMapCone {S : Scheme.{u}}
    {J : Type u} [SmallCategory J] [IsCofiltered J] {K : J ⥤ S.Etale}
    (c : Cone (K ⋙ toProEt S))
    (hc : IsLimit ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c)) : IsLimit c :=
  isLimitOfReflects (ProEt.forget S ⋙ CategoryTheory.Over.forget S) hc

/-- The presheaf pullback (left Kan extension) of a presheaf on the small étale site to the
small pro-étale site sends cofiltered limits of quasi-compact quasi-separated étale
`S`-schemes with affine transition maps to colimits. -/
lemma isColimit_lan_toProEt_mapCocone {S : Scheme.{u}} (F : S.Etaleᵒᵖ ⥤ A)
    {J : Type u} [SmallCategory J] [IsCofiltered J] (K : J ⥤ S.Etale)
    [∀ j, CompactSpace (K.obj j).left] [∀ j, QuasiSeparatedSpace (K.obj j).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (K.map g).left]
    (c : Cone (K ⋙ toProEt S))
    (hc : IsLimit ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c)) :
    Nonempty (IsColimit (((toProEt S).op.lan.obj F).mapCocone c.op)) := by
  have hc₁ : IsLimit c := isLimitOfIsLimitMapCone c hc
  have hcOver : IsLimit ((ProEt.forget S).mapCone c) :=
    isLimitOfReflects (CategoryTheory.Over.forget S)
      (hc.ofIsoLimit (Functor.mapConeMapCone c).symm)
  have hpres (X : S.Etaleᵒᵖ) : PreservesColimit (K.op ⋙ (toProEt S).op)
      (coyoneda.obj (op ((toProEt S).op.obj X))) := by
    have h₁ {i j : J} (f : i ⟶ j) :
        IsAffineHom (((K ⋙ toProEt S) ⋙ ProEt.forget S).map f).left :=
      inferInstanceAs (IsAffineHom (K.map f).left)
    have h₂ (i : J) : CompactSpace (((K ⋙ toProEt S) ⋙ ProEt.forget S).obj i).left :=
      inferInstanceAs (CompactSpace (K.obj i).left)
    have h₃ (i : J) : QuasiSeparatedSpace (((K ⋙ toProEt S) ⋙ ProEt.forget S).obj i).left :=
      inferInstanceAs (QuasiSeparatedSpace (K.obj i).left)
    have h₄ : LocallyOfFinitePresentation ((ProEt.forget S).obj ((toProEt S).obj X.unop)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation X.unop.hom)
    have hyon : IsColimit ((yoneda.obj ((ProEt.forget S).obj ((toProEt S).obj X.unop))).mapCocone
        ((ProEt.forget S).mapCone c).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((toProEt S).obj X.unop)).mapCocone c.op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((toProEt S).obj X.unop))
        (by exact hyon)
    exact preservesColimit_of_preserves_colimit_cocone hc₁.op
      (IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy)
  have : PreservesColimit (K ⋙ toProEt S).op ((toProEt S).op.leftKanExtension F) :=
    inferInstanceAs (PreservesColimit (K.op ⋙ (toProEt S).op) _)
  exact ⟨isColimitOfPreserves ((toProEt S).op.leftKanExtension F) hc₁.op⟩

/-- On objects of the pro-étale site which are pro-(affine étale) over `S`, the presheaf
pullback of an étale sheaf agrees with its sheafification. -/
lemma isIso_toSheafify_lan_app_of_proAffineEtale {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) (Y : S.ProEt) (hY : proAffineEtale Y.hom) :
    IsIso ((toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)).app (op Y)) := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  have h2 : IsIso ((AffineProEt.toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify (AffineProEt.topology S) _ _ A _
      (ProEt.isSheaf_lan_toProEt S A F.obj F.property)
  exact inferInstanceAs (IsIso (((AffineProEt.toProEt S).op.whiskerLeft
    (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))).app
      (op (AffineProEt.mk Y.hom hY))))

/-- The left Kan extension of an étale sheaf and its sheafification on the pro-étale site
send cofiltered limits of affine étale `S`-schemes to colimits. -/
lemma isColimit_comparisonUpperStar_mapCocone_of_isAffine {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A)
    {J : Type u} [SmallCategory J] [IsCofiltered J] (K : J ⥤ S.Etale)
    [∀ j, IsAffine (K.obj j).left] (c : Cone (K ⋙ toProEt S))
    (hc : IsLimit ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c)) :
    Nonempty (IsColimit (((comparisonUpperStar A S).obj F).obj.mapCocone c.op)) := by
  obtain ⟨hL⟩ := isColimit_lan_toProEt_mapCocone A F.obj K c hc
  have hpt : proAffineEtale c.pt.hom :=
    ⟨J, inferInstance, inferInstance, (K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S,
      Functor.whiskerLeft ((K ⋙ toProEt S) ⋙ ProEt.forget S) (Over.forgetCocone S).ι,
      ((ProEt.forget S ⋙ Over.forget S).mapCone c).π, hc, fun j ↦
        ⟨⟨inferInstanceAs (Etale (K.obj j).hom), ⟨inferInstanceAs (IsAffine (K.obj j).left),
          trivial⟩⟩, Over.w ((ProEt.forget S).map (c.π.app j))⟩⟩
  have (j : Jᵒᵖ) : IsIso ((toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)).app
      ((K ⋙ toProEt S).op.obj j)) :=
    isIso_toSheafify_lan_app_of_proAffineEtale A F ((toProEt S).obj (K.obj j.unop))
      (@proAffineEtale.of_isAffine _ _ (inferInstanceAs (IsAffine (K.obj j.unop).left))
        (K.obj j.unop).hom (inferInstanceAs (Etale (K.obj j.unop).hom)))
  have : IsIso ((toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)).app c.op.pt) :=
    isIso_toSheafify_lan_app_of_proAffineEtale A F c.pt hpt
  exact ⟨isColimitMapCoconeOfNatTrans _ _
    (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)) _ hL⟩

section OpenHypercover

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderComposition] {S : Scheme.{u}}

/-- An open subscheme `U` of an object `V` of `P.Over ⊤ S`, as an object of `P.Over ⊤ S`,
when `P` holds for open immersions. -/
noncomputable def overOpens (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsOpenImmersion f → P f)
    (V : P.Over ⊤ S) (U : V.left.Opens) : P.Over ⊤ S :=
  MorphismProperty.Over.mk ⊤ (U.ι ≫ V.hom) (P.comp_mem _ _ (hP _ inferInstance) V.prop)

/-- The inclusion of an open subscheme, as a morphism of `P.Over ⊤ S`. -/
noncomputable def overOpensι (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsOpenImmersion f → P f)
    (V : P.Over ⊤ S) (U : V.left.Opens) : overOpens hP V U ⟶ V :=
  MorphismProperty.Over.homMk U.ι rfl trivial

/-- A pre-`1`-hypercover in `P.Over ⊤ S` whose structure maps are open immersions covering the
base and whose second-level maps are open immersions covering the pairwise intersections is a
`1`-hypercover for any topology in which jointly surjective families of open immersions are
covering. -/
noncomputable def oneHypercoverOfIsOpenImmersion
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsOpenImmersion f → P f)
    (J : GrothendieckTopology (P.Over ⊤ S))
    (hJ : ∀ (V : P.Over ⊤ S) (R : Sieve V) {ι : Type u} (Z : ι → P.Over ⊤ S)
      (g : ∀ i, Z i ⟶ V), (∀ i, IsOpenImmersion (g i).left) →
      (∀ x, ∃ i, x ∈ Set.range (g i).left) → (∀ i, R (g i)) → R ∈ J V)
    {V : P.Over ⊤ S} (E : PreOneHypercover.{u} V) (hf : ∀ k, IsOpenImmersion (E.f k).left)
    (hp : ∀ {k l} (m : E.I₁ k l), IsOpenImmersion (E.p₁ m).left)
    (h₀ : ∀ x, ∃ k, x ∈ Set.range (E.f k).left)
    (h₁ : ∀ k l x, x ∈ Set.range (E.f k).left → x ∈ Set.range (E.f l).left →
      ∃ m : E.I₁ k l, x ∈ Set.range ((E.p₁ m).left ≫ (E.f k).left)) :
    J.OneHypercover V where
  __ := E
  mem₀ := hJ V _ E.X E.f hf h₀ fun k ↦ Sieve.ofArrows_mk _ _ k
  mem₁ a b W p₁ p₂ w := by
    let U (m : E.I₁ a b) : W.left.Opens :=
      (p₁ ≫ E.f a).left ⁻¹ᵁ ((E.p₁ m).left ≫ (E.f a).left).opensRange
    refine hJ W _ (fun m ↦ overOpens hP W (U m)) (fun m ↦ overOpensι hP W (U m))
      (fun m ↦ inferInstanceAs (IsOpenImmersion (U m).ι)) (fun x ↦ ?_) (fun m ↦ ?_)
    · obtain ⟨m, hm⟩ := h₁ a b ((p₁ ≫ E.f a).left x) ⟨p₁.left x, by simp⟩
        ⟨p₂.left x, by rw [w]; simp⟩
      exact ⟨m, ⟨⟨x, hm⟩, rfl⟩⟩
    · have hle : Set.range ((U m).ι ≫ (p₁ ≫ E.f a).left) ⊆
          Set.range ((E.p₁ m).left ≫ (E.f a).left) := by
        rintro _ ⟨x, rfl⟩
        exact x.2
      have := hp m
      have hfa := hf a
      have hfb := hf b
      have hh : IsOpenImmersion.lift _ _ hle ≫ (E.p₁ m).left ≫ (E.f a).left =
          (U m).ι ≫ p₁.left ≫ (E.f a).left :=
        (IsOpenImmersion.lift_fac _ _ hle).trans (by simp)
      let h : overOpens hP W (U m) ⟶ E.Y m := MorphismProperty.Over.homMk
        (IsOpenImmersion.lift _ _ hle) (by
          rw [← MorphismProperty.Over.w (E.p₁ m), ← MorphismProperty.Over.w (E.f a),
            reassoc_of% hh, MorphismProperty.Over.w, MorphismProperty.Over.w]
          rfl) trivial
      have hh' : h.left ≫ (E.p₁ m).left ≫ (E.f a).left =
          (overOpensι hP W (U m)).left ≫ p₁.left ≫ (E.f a).left := hh
      refine ⟨m, h, ?_, ?_⟩
      · refine MorphismProperty.Over.Hom.ext ((cancel_mono (E.f a).left).1 ?_)
        simp only [MorphismProperty.Comma.comp_left, Category.assoc, hh']
      · refine MorphismProperty.Over.Hom.ext ((cancel_mono (E.f b).left).1 ?_)
        have hw := congrArg (fun φ ↦ φ.left) (E.w m)
        have hw' := congrArg (fun φ ↦ φ.left) w
        simp only [MorphismProperty.Comma.comp_left] at hw hw'
        simp only [MorphismProperty.Comma.comp_left, Category.assoc, ← hw, hh', hw']

/-- A sieve on an étale `S`-scheme containing a jointly surjective family of open immersions is
covering for the étale topology. -/
lemma mem_smallEtaleTopology_of_isOpenImmersion (V : S.Etale) (R : Sieve V) {ι : Type u}
    (Z : ι → S.Etale) (g : ∀ i, Z i ⟶ V) (_hg : ∀ i, IsOpenImmersion (g i).left)
    (hcov : ∀ x, ∃ i, x ∈ Set.range (g i).left) (hR : ∀ i, R (g i)) :
    R ∈ smallEtaleTopology S V := by
  refine GrothendieckTopology.superset_covering _ ?_
    ((ofArrows_mem_smallEtaleTopology_iff g).2 (Set.eq_univ_of_forall fun x ↦ ?_))
  · rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
    exact R.downward_closed (hR i) a
  · obtain ⟨i, hi⟩ := hcov x
    exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- A sieve on an object of the pro-étale site containing a jointly surjective family of open
immersions is covering for the pro-étale topology. -/
lemma _root_.AlgebraicGeometry.Scheme.ProEt.mem_topology_of_isOpenImmersion (V : S.ProEt)
    (R : Sieve V) {ι : Type u}
    (Z : ι → S.ProEt) (g : ∀ i, Z i ⟶ V) (hg : ∀ i, IsOpenImmersion (g i).left)
    (hcov : ∀ x, ∃ i, x ∈ Set.range (g i).left) (hR : ∀ i, R (g i)) :
    R ∈ ProEt.topology S V := by
  rw [ProEt.mem_topology_iff]
  refine ⟨.ofArrows Z g, ?_, fun _ _ ⟨i⟩ ↦ hR i⟩
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  exact zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hcov, hg⟩)

end OpenHypercover

/-- A finite cover of a scheme by affine opens, together with finite covers of the pairwise
intersections by affine opens. -/
structure AffineOpenCoverData (X : Scheme.{u}) where
  /-- The index type of the cover. -/
  ι₀ : Type u
  [finite₀ : Finite ι₀]
  /-- The affine opens of the cover. -/
  O : ι₀ → X.Opens
  isAffineOpen_O (k : ι₀) : IsAffineOpen (O k)
  iSup_O : ⨆ k, O k = ⊤
  /-- The index types of the covers of the pairwise intersections. -/
  ι₁ : ι₀ → ι₀ → Type u
  [finite₁ (k l : ι₀) : Finite (ι₁ k l)]
  /-- The affine opens covering the pairwise intersections. -/
  W (k l : ι₀) : ι₁ k l → X.Opens
  isAffineOpen_W (k l : ι₀) (m : ι₁ k l) : IsAffineOpen (W k l m)
  iSup_W (k l : ι₀) : ⨆ m, W k l m = O k ⊓ O l

attribute [instance] AffineOpenCoverData.finite₀ AffineOpenCoverData.finite₁

lemma AffineOpenCoverData.W_le_left {X : Scheme.{u}} (d : AffineOpenCoverData X) {k l : d.ι₀}
    (m : d.ι₁ k l) : d.W k l m ≤ d.O k :=
  (le_iSup (d.W k l) m).trans ((d.iSup_W k l).le.trans inf_le_left)

lemma AffineOpenCoverData.W_le_right {X : Scheme.{u}} (d : AffineOpenCoverData X) {k l : d.ι₀}
    (m : d.ι₁ k l) : d.W k l m ≤ d.O l :=
  (le_iSup (d.W k l) m).trans ((d.iSup_W k l).le.trans inf_le_right)

lemma AffineOpenCoverData.exists_mem_preimage {X Y : Scheme.{u}} (d : AffineOpenCoverData X)
    (π : Y ⟶ X) (y : Y) : ∃ k, y ∈ π ⁻¹ᵁ d.O k := by
  have : π y ∈ ⨆ k, d.O k := d.iSup_O ▸ trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨k, hk⟩

lemma AffineOpenCoverData.exists_mem_preimage_W {X Y : Scheme.{u}} (d : AffineOpenCoverData X)
    (π : Y ⟶ X) {y : Y} {k l : d.ι₀} (hk : y ∈ π ⁻¹ᵁ d.O k) (hl : y ∈ π ⁻¹ᵁ d.O l) :
    ∃ m, y ∈ π ⁻¹ᵁ d.W k l m := by
  have : π y ∈ ⨆ m, d.W k l m := (d.iSup_W k l).symm ▸ ⟨hk, hl⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨m, hm⟩

/-- A compact open of a scheme is a finite union of affine opens. -/
lemma exists_finite_affineOpens_iSup_eq {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) ∧ ⨆ i, V i = U := by
  obtain ⟨Us, hB, hfin, rfl⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact hU
  exact ⟨Us, hfin.to_subtype, Subtype.val, fun i ↦ hB i.2, (sSup_eq_iSup' Us).symm⟩

/-- A quasi-compact quasi-separated scheme admits an `AffineOpenCoverData`. -/
lemma nonempty_affineOpenCoverData (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (AffineOpenCoverData X) := by
  obtain ⟨ι₀, _, O, hO, hOsup⟩ := exists_finite_affineOpens_iSup_eq (⊤ : X.Opens)
    isCompact_univ
  choose ι₁ _ W hW hWsup using fun k l ↦ exists_finite_affineOpens_iSup_eq (O k ⊓ O l)
    (QuasiSeparatedSpace.inter_isCompact _ _ (O k).2 (hO k).isCompact (O l).2 (hO l).isCompact)
  exact ⟨⟨ι₀, O, hO, hOsup, ι₁, W, hW, hWsup⟩⟩

/-- Restrictions of a morphism of schemes to opens commute with inclusions of opens. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Hom.resLE_comp_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : Y.Opens}
    {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') (hU : U ≤ U') (hV : V ≤ V') :
    f.resLE U V e ≫ Y.homOfLE hU = X.homOfLE hV ≫ f.resLE U' V' e' := by
  rw [← cancel_mono U'.ι]
  simp

section Presentation

variable {S : Scheme.{u}} {I : Type u} [SmallCategory I] (K : I ⥤ S.Etale)
  (c : Cone (K ⋙ toProEt S)) (i₀ : I)

/-- Given a diagram `K` of étale `S`-schemes and an open `U` of `K i₀`, the diagram of the
preimages of `U` in the `K j` for `j` over `i₀`. -/
noncomputable def opensEtaleDiagram (U : (K.obj i₀).left.Opens) : Over i₀ ⥤ S.Etale :=
  MorphismProperty.Over.lift' (P := @Etale) (Q := ⊤)
    (opensDiagram ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) i₀ U)
    (opensDiagramι ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) i₀ U ≫
      Functor.whiskerLeft (Over.forget i₀)
      (Functor.whiskerLeft ((K ⋙ toProEt S) ⋙ ProEt.forget S) (Over.forgetCocone S).ι))
    (fun j ↦ inferInstanceAs (Etale (_ ≫ (K.obj j.left).hom))) (fun _ ↦ trivial)

/-- The preimage of an open `U` of `K i₀` in the cone point of `c`, as an object of the
pro-étale site. -/
noncomputable def opensConePt (U : (K.obj i₀).left.Opens) : S.ProEt :=
  overOpens (fun _ _ ↦ inferInstance) c.pt ((c.π.app i₀).left ⁻¹ᵁ U)

variable [IsCofiltered I]
  (hc : IsLimit ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c))

/-- The preimage of an open `U` of `K i₀` in the limit of `K` is the limit of the preimages
of `U` in the `K j`. -/
noncomputable def opensPresentation (U : (K.obj i₀).left.Opens) :
    RelativeLimitPresentation (Over i₀) (toProEt S) (opensConePt K c i₀ U) where
  diag := opensEtaleDiagram K i₀ U
  π :=
    { app j := MorphismProperty.Over.homMk
        ((opensCone ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S)
          ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c) i₀ U).π.app j)
        ((Scheme.Hom.resLE_comp_ι_assoc _ _ (K.obj j.left).hom).trans
          (congrArg (_ ≫ ·) (MorphismProperty.Over.w (c.π.app j.left)))) trivial
      naturality _ _ f := (ProEt.forget S ⋙ Over.forget S).map_injective
        ((Category.id_comp _).trans
          ((opensCone ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S)
            ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c) i₀ U).w f).symm) }
  isLimit := isLimitOfReflects (ProEt.forget S ⋙ Over.forget S)
    (isLimitOpensCone ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) _ hc i₀ U)

/-- The inclusion of the preimages of opens `U ≤ V` of `K i₀` in the cone point of `c`. -/
noncomputable def opensConePtHomOfLE {U V : (K.obj i₀).left.Opens} (h : U ≤ V) :
    opensConePt K c i₀ U ⟶ opensConePt K c i₀ V :=
  MorphismProperty.Over.homMk (Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ h))
    (by simp [opensConePt, overOpens]) trivial

/-- The presentation of the cone point of `c` by the restriction of `K` to the objects
over `i₀`. -/
noncomputable def overPresentation : RelativeLimitPresentation (Over i₀) (toProEt S) c.pt where
  diag := Over.forget i₀ ⋙ K
  π := (c.whisker (Over.forget i₀)).π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm
    (isLimitOfIsLimitMapCone c hc)

/-- The inclusions of the preimages of an open of `K i₀`, as a morphism of presentations. -/
noncomputable def opensPresentationι (U : (K.obj i₀).left.Opens) :
    (opensPresentation K c i₀ hc U).Hom (overPresentation K c i₀ hc) where
  natTrans :=
    { app j := MorphismProperty.Over.homMk
        ((opensDiagramι ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) i₀ U).app j)
        rfl trivial
      naturality _ _ f := (Etale.forget S ⋙ Over.forget S).map_injective
        ((opensDiagramι ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) i₀ U).naturality f) }

/-- The inclusions of the preimages of opens `U ≤ V` of `K i₀`, as a morphism of
presentations. -/
noncomputable def opensPresentationHomOfLE {U V : (K.obj i₀).left.Opens} (h : U ≤ V) :
    (opensPresentation K c i₀ hc U).Hom (opensPresentation K c i₀ hc V) where
  natTrans :=
    { app j := MorphismProperty.Over.homMk
        (Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ h))
        (Scheme.homOfLE_ι_assoc _ _ _) trivial
      naturality _ _ f := by
        have : (opensDiagram ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) i₀ U).map f ≫
            Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ h) =
            Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ h) ≫
              (opensDiagram ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) i₀ V).map f := by
          rw [← cancel_mono (Scheme.Opens.ι _)]
          simp
        exact (Etale.forget S ⋙ Over.forget S).map_injective this }

lemma opensPresentationι_map (U : (K.obj i₀).left.Opens) :
    (opensPresentationι K c i₀ hc U).map =
      overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance)
        c.pt ((c.π.app i₀).left ⁻¹ᵁ U) := by
  refine (overPresentation K c i₀ hc).isLimit.hom_ext fun j ↦ ?_
  rw [RelativeLimitPresentation.Hom.map_π]
  exact (ProEt.forget S ⋙ Over.forget S).map_injective (Scheme.Hom.resLE_comp_ι _ _)

lemma opensPresentationHomOfLE_map {U V : (K.obj i₀).left.Opens} (h : U ≤ V) :
    (opensPresentationHomOfLE K c i₀ hc h).map = opensConePtHomOfLE K c i₀ h := by
  refine (opensPresentation K c i₀ hc V).isLimit.hom_ext fun j ↦ ?_
  rw [RelativeLimitPresentation.Hom.map_π]
  exact (ProEt.forget S ⋙ Over.forget S).map_injective
    (Scheme.Hom.resLE_comp_homOfLE (c.π.app j.left).left _ _
      (by exact Scheme.Hom.preimage_mono _ h) (by exact Scheme.Hom.preimage_mono _ h))

lemma opensPresentationHomOfLE_comp_ι {U V : (K.obj i₀).left.Opens} (h : U ≤ V) :
    (opensPresentationHomOfLE K c i₀ hc h).comp (opensPresentationι K c i₀ hc V) =
      opensPresentationι K c i₀ hc U := by
  refine RelativeLimitPresentation.Hom.ext (NatTrans.ext (funext fun j ↦ ?_))
  exact (Etale.forget S ⋙ Over.forget S).map_injective
    (Scheme.homOfLE_ι _ (Scheme.Hom.preimage_mono (K.map j.hom).left h))

variable {K} in
/-- The pre-`1`-hypercover of the cone point of `c` by the preimages of the opens of an
`AffineOpenCoverData` of `K i₀`. -/
noncomputable def opensPreOneHypercover (d : AffineOpenCoverData (K.obj i₀).left) :
    PreOneHypercover.{u} c.pt where
  I₀ := d.ι₀
  X k := opensConePt K c i₀ (d.O k)
  f _ := overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) c.pt _
  I₁ := d.ι₁
  Y k l m := opensConePt K c i₀ (d.W k l m)
  p₁ _ _ m := opensConePtHomOfLE K c i₀ (d.W_le_left m)
  p₂ _ _ m := opensConePtHomOfLE K c i₀ (d.W_le_right m)
  w _ _ m := MorphismProperty.Over.Hom.ext
    ((Scheme.homOfLE_ι _ (Scheme.Hom.preimage_mono _ (d.W_le_left m))).trans
      (Scheme.homOfLE_ι _ (Scheme.Hom.preimage_mono _ (d.W_le_right m))).symm)

instance (d : AffineOpenCoverData (K.obj i₀).left) : (opensPreOneHypercover c i₀ d).Finite where
  finite₀ := inferInstanceAs (Finite d.ι₀)
  finite₁ k l := inferInstanceAs (Finite (d.ι₁ k l))

/-- The presentation of `opensPreOneHypercover` as a cofiltered limit of pre-`1`-hypercovers
of the `K j` for `j` over `i₀`. -/
noncomputable def opensPreOneHypercoverPresentation (d : AffineOpenCoverData (K.obj i₀).left) :
    (opensPreOneHypercover c i₀ d).RelativeLimitPresentation (Over i₀) (toProEt S) where
  pres := overPresentation K c i₀ hc
  pres₀ k := opensPresentation K c i₀ hc (d.O k)
  pres₁ m := opensPresentation K c i₀ hc (d.W _ _ m)
  f _ := opensPresentationι K c i₀ hc _
  p₁ m := opensPresentationHomOfLE K c i₀ hc (d.W_le_left m)
  p₂ m := opensPresentationHomOfLE K c i₀ hc (d.W_le_right m)
  hf _ := opensPresentationι_map K c i₀ hc _
  hp₁ _ := opensPresentationHomOfLE_map K c i₀ hc _
  hp₂ _ := opensPresentationHomOfLE_map K c i₀ hc _
  w _ := (opensPresentationHomOfLE_comp_ι K c i₀ hc _).trans
    (opensPresentationHomOfLE_comp_ι K c i₀ hc _).symm

variable {K} in
/-- `opensPreOneHypercover` is a `1`-hypercover for the pro-étale topology. -/
noncomputable def opensOneHypercover (d : AffineOpenCoverData (K.obj i₀).left) :
    (ProEt.topology S).OneHypercover c.pt :=
  oneHypercoverOfIsOpenImmersion (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) (ProEt.topology S)
    ProEt.mem_topology_of_isOpenImmersion (opensPreOneHypercover c i₀ d)
    (fun _ ↦ inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)))
    (fun m ↦ inferInstanceAs (IsOpenImmersion
      (Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ (d.W_le_left m)))))
    (fun x ↦ by
      obtain ⟨k, hk⟩ := d.exists_mem_preimage (c.π.app i₀).left x
      exact ⟨k, ⟨x, hk⟩, rfl⟩)
    (fun k l _ hk hl ↦ by
      obtain ⟨⟨x, hk⟩, rfl⟩ := hk
      obtain ⟨⟨y, hl⟩, rfl : y = x⟩ := hl
      obtain ⟨m, hm⟩ := d.exists_mem_preimage_W (c.π.app i₀).left hk hl
      have hcomp : ((opensPreOneHypercover c i₀ d).p₁ m).left ≫
          ((opensPreOneHypercover c i₀ d).f k).left =
          ((c.π.app i₀).left ⁻¹ᵁ d.W k l m).ι :=
        Scheme.homOfLE_ι _ (Scheme.Hom.preimage_mono _ (d.W_le_left m))
      refine ⟨m, ?_⟩
      rw [hcomp]
      exact ⟨⟨y, hm⟩, rfl⟩)

/-- The stages of `opensPreOneHypercoverPresentation` are `1`-hypercovers for the étale
topology. -/
noncomputable def opensPreOneHypercoverPresentationOneHypercover
    (d : AffineOpenCoverData (K.obj i₀).left) (j : Over i₀) :
    (smallEtaleTopology S).OneHypercover (K.obj j.left) :=
  oneHypercoverOfIsOpenImmersion (P := @Etale) (fun _ _ ↦ inferInstance) (smallEtaleTopology S)
    mem_smallEtaleTopology_of_isOpenImmersion
    ((opensPreOneHypercoverPresentation K c i₀ hc d).preOneHypercover j)
    (fun _ ↦ inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)))
    (fun m ↦ inferInstanceAs (IsOpenImmersion
      (Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ (d.W_le_left m)))))
    (fun x ↦ by
      obtain ⟨k, hk⟩ := d.exists_mem_preimage (K.map j.hom).left x
      exact ⟨k, ⟨x, hk⟩, rfl⟩)
    (fun k l _ hk hl ↦ by
      obtain ⟨⟨x, hk⟩, rfl⟩ := hk
      obtain ⟨⟨y, hl⟩, rfl : y = x⟩ := hl
      obtain ⟨m, hm⟩ := d.exists_mem_preimage_W (K.map j.hom).left hk hl
      have hcomp :
          (((opensPreOneHypercoverPresentation K c i₀ hc d).preOneHypercover j).p₁ m).left ≫
            (((opensPreOneHypercoverPresentation K c i₀ hc d).preOneHypercover j).f k).left =
          ((K.map j.hom).left ⁻¹ᵁ d.W k l m).ι :=
        Scheme.homOfLE_ι _ (Scheme.Hom.preimage_mono _ (d.W_le_left m))
      refine ⟨m, ?_⟩
      rw [hcomp]
      exact ⟨⟨y, hm⟩, rfl⟩)

end Presentation

/-- **Continuity of the comparison pullback.** For a cofiltered diagram `K` of quasi-compact
quasi-separated étale `S`-schemes with affine transition maps and a cone `c` over it in the
pro-étale site whose underlying cone of schemes is a limit, the sections of `ν^* F` over the
cone point are the filtered colimit of the sections over the `Kᵢ`. -/
theorem isColimit_comparisonUpperStar_mapCocone {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (K : I ⥤ S.Etale)
    [∀ i, CompactSpace (K.obj i).left] [∀ i, QuasiSeparatedSpace (K.obj i).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (K.map g).left]
    (c : Cone (K ⋙ toProEt S))
    (hc : IsLimit ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c)) :
    Nonempty (IsColimit (((comparisonUpperStar A S).obj F).obj.mapCocone c.op)) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  obtain ⟨d⟩ := nonempty_affineOpenCoverData (K.obj i₀).left
  have : HasFilteredColimitsOfSize.{u, u} A :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  have h₀ (U : (K.obj i₀).left.Opens) (hU : IsAffineOpen U) :
      IsColimit (((comparisonUpperStar A S).obj F).obj.mapCocone
        (opensPresentation K c i₀ hc U).cone.op) := by
    have (j : Over i₀) : IsAffine ((opensPresentation K c i₀ hc U).diag.obj j).left :=
      hU.preimage (K.map j.hom).left
    exact (isColimit_comparisonUpperStar_mapCocone_of_isAffine A F
      (opensPresentation K c i₀ hc U).diag (opensPresentation K c i₀ hc U).cone
      (isLimitOpensCone ((K ⋙ toProEt S) ⋙ ProEt.forget S ⋙ Over.forget S) _ hc i₀ U)).some
  have h := (opensPreOneHypercoverPresentation K c i₀ hc d).isColimitOfIsLimit
    ((comparisonUpperStar A S).obj F).obj
    ((opensOneHypercover c i₀ d).isLimitMultifork ((comparisonUpperStar A S).obj F))
    (fun k ↦ h₀ _ (d.isAffineOpen_O k)) (fun m ↦ h₀ _ (d.isAffineOpen_W _ _ m))
    (fun j ↦ (opensPreOneHypercoverPresentationOneHypercover K c i₀ hc d j).isLimitMultifork
      ((comparisonLowerStar A S).obj ((comparisonUpperStar A S).obj F)))
  exact ⟨(Functor.Final.isColimitWhiskerEquiv (Over.forget i₀).op _) h⟩

end AlgebraicGeometry.ProEtale
