/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality
public import WeilConjectures.TraceFormula.KunnethVerdierOpen
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

/-!

# The exceptional Künneth map under restriction to an open subscheme

Let `j : U ⟶ Y` be an open immersion of separated `k`-schemes of finite type and
`G = 𝟙_X × j : X ⨯ U ⟶ X ⨯ Y`. This file proves `ExceptionalKunnethMapRestriction`
(`WeilConjectures.TraceFormula.KunnethVerdierOpen`): the restriction `LG^* α_Y` of the exceptional
Künneth map is `α_U`, through `LG^* (M ⊠ ω_Y) ≅ M ⊠ ω_U` and `LG^* Rp^! M ≅ Rp_U^! M`.

By the functoriality of `α` in the second factor (`exceptionalKunnethMap_comp_prodMap`), `α_U`
is the transpose along `RG_! ⊣ RG^!` of the trace map `RG_! (M ⊠ ω_U) ⟶ M ⊠ ω_Y` followed by
`α_Y`. For an open immersion the trace map is, through `RG_! ≅ G_!`, the counit of the
restriction adjunction `G_! ⊣ LG^*` at the inverse of `LG^* (M ⊠ ω_Y) ≅ M ⊠ ω_U`: the inverse
projection formula of `G` is the adjoint of the tensor structure of `LG^*`, the inverse
compact-support base change is the base change of extension by zero, and the counit of
`Rj_! ⊣ Rj^!` is that of `j_! ⊣ Lj^*` through `Rj^! ≅ Lj^*`. Since `RG^! ≅ LG^*` is the
conjugate of `RG_! ≅ G_!`, the claim follows. The diagram chases are carried out for abstract
functors (`traceAux_eq_counit_of_lowerShriekIso`, `traceAux_eq_counit_of_restrictionIso`,
`map_comp_restriction_eq_of_trace`).

## Main statements

- `ProEtale.CondensedRing.exceptionalKunnethMapRestriction`.

## The projection formula of an open immersion

The projection formula of an open immersion used below,
`boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison` (blueprint
`prop-sf-pf-coherence`; SGA 4, Exposé XVII, §5), is proved in
`WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion`.

## Implementation notes

The instantiation of the abstract lemmas takes the components of the trace map from the
definition of `exceptionalKunnethProdMapTrace` by unification (`refine` with holes), so that the
kernel only compares syntactically equal terms; elaborating them separately produces terms which
differ in their (auxiliary) proofs, and the kernel then unfolds the six functors.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.LaxMonoidal]

/-- The projection comparison `P (S W ⊗ S N) ⟶ P S W ⊗ N` followed by the counit at `W` is `P`
of the tensor structure of `S` followed by the counit at `W ⊗ N`. -/
@[reassoc]
lemma projectionComparison_comp_counit_app_whiskerRight (W N : D) :
    adj.projectionComparison (S.obj W) N ≫ adj.counit.app W ▷ N =
      P.map (Functor.LaxMonoidal.μ S W N) ≫ adj.counit.app (W ⊗ N) := by
  rw [projectionComparison, homEquiv_counit, Category.assoc, ← adj.counit_naturality,
    ← P.map_comp_assoc, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left, ← comp_whiskerRight_assoc, right_triangle_components]
  simp

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! ### The abstract diagram chases -/

/-- The trace map of `exceptionalKunnethProdMapTrace` along an open immersion, for abstract
functors: `G ≅ G_o` plays `RG_! ≅ G_!` (extension by zero), `G_o ⊣ G_s` the adjunction
`G_! ⊣ LG^*`, `g_l ⊣ g_r` and `j_o ⊣ j_s` the adjunctions `Rj_! ⊣ Rj^!` and `j_! ⊣ Lj^*`, `BC` the
base change of extension by zero and `θ : j_s ⋙ Q_Z ≅ Q ⋙ G_s` the pullback comparison. If the
projection formula `pfG` and the base change `bs` are the ones of extension by zero, then the
trace map is `RG_! ≅ G_!` followed by the counit of `G_! ⊣ LG^*`, through the tensor structure of
`G_s`. -/
lemma traceAux_eq_counit_of_lowerShriekIso {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱]
    [Category 𝒲] [Category 𝒴] [Category 𝒵] [MonoidalCategory 𝒱]
    [MonoidalCategory 𝒲] [BraidedCategory 𝒱] [BraidedCategory 𝒲] {G Go : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱}
    [Gs.LaxMonoidal] (lamG : G ≅ Go) (adjGo : Go ⊣ Gs) (Q : 𝒴 ⥤ 𝒲) (Qz : 𝒵 ⥤ 𝒱)
    {gl : 𝒵 ⥤ 𝒴} {gr : 𝒴 ⥤ 𝒵} (adjg : gl ⊣ gr) {jo : 𝒵 ⥤ 𝒴} {js : 𝒴 ⥤ 𝒵} (adjjo : jo ⊣ js)
    (lamj : gl ≅ jo) (ιj : gr ≅ js) (hιj : ιj = conjugateIsoEquiv adjg adjjo lamj.symm)
    {ωY : 𝒴} {ωU : 𝒵} (d : gr.obj ωY ≅ ωU) (bs : gl ⋙ Q ⟶ Qz ⋙ G) [IsIso bs]
    (BC : Qz ⋙ Go ⟶ jo ⋙ Q) (θ : js ⋙ Qz ≅ Q ⋙ Gs)
    (hbs : bs.app ωU ≫ lamG.hom.app (Qz.obj ωU) ≫ BC.app ωU = Q.map (lamj.hom.app ωU))
    (hBC : BC = Adjunction.exchangeLeft adjjo adjGo θ)
    {B : 𝒱} (pM : 𝒲) (e : B ⟶ Gs.obj pM)
    (hbr : Functor.LaxMonoidal.μ Gs pM (Q.obj ωY) ≫ Gs.map (β_ pM (Q.obj ωY)).hom =
      (β_ (Gs.obj pM) (Gs.obj (Q.obj ωY))).hom ≫ Functor.LaxMonoidal.μ Gs (Q.obj ωY) pM)
    (pfG : G.obj (Qz.obj ωU) ⊗ pM ⟶ G.obj (Qz.obj ωU ⊗ Gs.obj pM)) [IsIso pfG]
    (hpf : pfG ≫ lamG.hom.app _ ≫ adjGo.projectionComparison (Qz.obj ωU) pM =
      lamG.hom.app (Qz.obj ωU) ▷ pM) :
    G.map (β_ B (Qz.obj ωU)).hom ≫ G.map (Qz.obj ωU ◁ e) ≫ inv pfG ≫
        (inv (bs.app ωU) ≫ Q.map (gl.map d.inv ≫ adjg.counit.app ωY)) ▷ pM ≫
        (β_ pM (Q.obj ωY)).inv =
      lamG.hom.app _ ≫ Go.map ((e ⊗ₘ (Qz.map (d.inv ≫ ιj.hom.app ωY) ≫ θ.hom.app ωY)) ≫
        Functor.LaxMonoidal.μ Gs pM (Q.obj ωY)) ≫ adjGo.counit.app _ := by
  set y : Qz.obj ωU ⟶ Gs.obj (Q.obj ωY) := Qz.map (d.inv ≫ ιj.hom.app ωY) ≫ θ.hom.app ωY
  have hcj : jo.map (ιj.hom.app ωY) ≫ adjjo.counit.app ωY =
      lamj.inv.app (gr.obj ωY) ≫ adjg.counit.app ωY := by
    subst hιj
    exact conjugateEquiv_counit adjg adjjo lamj.inv ωY
  have h₁ : inv (bs.app ωU) = lamG.hom.app (Qz.obj ωU) ≫ BC.app ωU ≫ Q.map (lamj.inv.app ωU) := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [reassoc_of% hbs, ← Q.map_comp, Iso.hom_inv_id_app, Q.map_id]
    rfl
  have h₂ : lamj.inv.app ωU ≫ gl.map d.inv ≫ adjg.counit.app ωY =
      jo.map (d.inv ≫ ιj.hom.app ωY) ≫ adjjo.counit.app ωY := by
    rw [Functor.map_comp, Category.assoc, hcj, ← lamj.inv.naturality_assoc]
  have h₃ : BC.app ωU ≫ Q.map (jo.map (d.inv ≫ ιj.hom.app ωY) ≫ adjjo.counit.app ωY) =
      Go.map y ≫ adjGo.counit.app (Q.obj ωY) := by
    have hn := BC.naturality (d.inv ≫ ιj.hom.app ωY)
    simp only [Functor.comp_map] at hn
    have hε := Adjunction.exchangeLeft_app_comp_map_counit_app adjjo adjGo θ ωY
    rw [← hBC] at hε
    rw [Q.map_comp, ← reassoc_of% hn, hε, Go.map_comp, Category.assoc]
  have h₄ : inv pfG ≫ lamG.hom.app (Qz.obj ωU) ▷ pM =
      lamG.hom.app _ ≫ adjGo.projectionComparison (Qz.obj ωU) pM := by
    rw [IsIso.inv_comp_eq, hpf]
  have hbr' : Functor.LaxMonoidal.μ Gs (Q.obj ωY) pM ≫ Gs.map (β_ pM (Q.obj ωY)).inv =
      (β_ (Gs.obj pM) (Gs.obj (Q.obj ωY))).inv ≫ Functor.LaxMonoidal.μ Gs pM (Q.obj ωY) := by
    rw [← cancel_epi (β_ (Gs.obj pM) (Gs.obj (Q.obj ωY))).hom, Iso.hom_inv_id_assoc,
      ← reassoc_of% hbr, ← Gs.map_comp, Iso.hom_inv_id, Gs.map_id, Category.comp_id]
  have hX : inv (bs.app ωU) ≫ Q.map (gl.map d.inv ≫ adjg.counit.app ωY) =
      lamG.hom.app (Qz.obj ωU) ≫ Go.map y ≫ adjGo.counit.app (Q.obj ωY) := by
    rw [h₁, Category.assoc, Category.assoc, ← Q.map_comp, h₂, h₃]
  have inner : (β_ B (Qz.obj ωU)).hom ≫ Qz.obj ωU ◁ e ≫ y ▷ Gs.obj pM ≫
      Functor.LaxMonoidal.μ Gs (Q.obj ωY) pM ≫ Gs.map (β_ pM (Q.obj ωY)).inv =
      (e ⊗ₘ y) ≫ Functor.LaxMonoidal.μ Gs pM (Q.obj ωY) := by
    rw [hbr', ← tensorHom_def'_assoc, ← BraidedCategory.braiding_naturality_assoc,
      Iso.hom_inv_id_assoc]
  rw [hX]
  simp only [comp_whiskerRight, Category.assoc]
  rw [reassoc_of% h₄,
    ← adjGo.projectionComparison_natural_left_assoc,
    adjGo.projectionComparison_comp_counit_app_whiskerRight_assoc, ← adjGo.counit_naturality,
    ← inner]
  simp only [Functor.map_comp, Category.assoc]
  rw [lamG.hom.naturality_assoc, lamG.hom.naturality_assoc]

/-- The transposition behind `exceptionalKunnethMapRestriction`, for abstract adjunctions: let
`G ⊣ R_G` and `G_o ⊣ G_s` with `G ≅ G_o`, so that `R_G ≅ G_s` (the conjugate isomorphism). If
the trace map `tr : G V ⟶ W` is `G ≅ G_o` followed by `G_o` of `ρ⁻¹ : V ≅ G_s W` and the counit,
then `G_s α_Y` corresponds to the transpose `α_U` of `tr ≫ α_Y` through `ρ` and `G_s ≅ R_G`. -/
lemma map_comp_conjugate_eq_of_trace {𝒱 𝒲 : Type*} [Category 𝒱] [Category 𝒲]
    {G Go : 𝒱 ⥤ 𝒲} {RG Gs : 𝒲 ⥤ 𝒱} (adjG : G ⊣ RG) (adjGo : Go ⊣ Gs) (lamG : G ≅ Go)
    {W T : 𝒲} {V T' : 𝒱} (tr : G.obj V ⟶ W) (ρ : Gs.obj W ≅ V) (αY : W ⟶ T)
    (htr : tr = lamG.hom.app V ≫ Go.map ρ.inv ≫ adjGo.counit.app W) (c : RG.obj T ⟶ T')
    (αU : V ⟶ T') (hαU : αU = adjG.homEquiv _ _ (tr ≫ αY) ≫ c) (ρT : Gs.obj T ⟶ T')
    (ι : RG ≅ Gs) (hι : ι = conjugateIsoEquiv adjG adjGo lamG.symm)
    (hρT : ρT = ι.inv.app T ≫ c) :
    Gs.map αY ≫ ρT = ρ.hom ≫ αU := by
  subst hαU htr hρT hι
  have h : adjG.homEquiv V W (lamG.hom.app V ≫ Go.map ρ.inv ≫ adjGo.counit.app W) =
      ρ.inv ≫ (conjugateIsoEquiv adjG adjGo lamG.symm).inv.app W := by
    rw [Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_counit, G.map_comp, Category.assoc]
    rw [conjugateIsoEquiv_apply_inv, Iso.symm_inv]
    erw [conjugateEquiv_counit]
    rw [lamG.hom.naturality_assoc]
  rw [Adjunction.homEquiv_naturality_right, h, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, NatTrans.naturality_assoc]


/-- `map_comp_conjugate_eq_of_trace` with the composition isomorphisms of the exceptional inverse
images written out: `c : R_U ≅ R ⋙ R_G` is `eqToIso p ≪≫ c'` and the identification
`G_s (R M) ≅ R_U M` is `R_G (R M) ≅ G_s (R M)` followed by `c'⁻¹` and `eqToIso q`. -/
lemma map_comp_restriction_eq_of_trace {𝒳 𝒱 𝒲 : Type*} [Category 𝒳] [Category 𝒱]
    [Category 𝒲] {G Go : 𝒱 ⥤ 𝒲} {RG Gs : 𝒲 ⥤ 𝒱} (adjG : G ⊣ RG) (adjGo : Go ⊣ Gs)
    (lamG : G ≅ Go) {W : 𝒲} {V : 𝒱} {RP : 𝒳 ⥤ 𝒲} {RPU RPU' : 𝒳 ⥤ 𝒱} {M : 𝒳}
    (tr : G.obj V ⟶ W) (ρ : Gs.obj W ≅ V) (αY : W ⟶ RP.obj M)
    (htr : tr = lamG.hom.app V ≫ Go.map ρ.inv ≫ adjGo.counit.app W) (cIso : RPU ≅ RP ⋙ RG)
    (cT : RPU' ≅ RP ⋙ RG) (p : RPU = RPU') (hc : cIso = eqToIso p ≪≫ cT) (αU : V ⟶ RPU.obj M)
    (hαU : αU = adjG.homEquiv _ _ (tr ≫ αY) ≫ cIso.inv.app M) (ι : RG ≅ Gs)
    (hι : ι = conjugateIsoEquiv adjG adjGo lamG.symm) (ρT : Gs.obj (RP.obj M) ≅ RPU.obj M)
    (q : RPU'.obj M = RPU.obj M)
    (hρT : ρT = ι.symm.app (RP.obj M) ≪≫ (cT.app M).symm ≪≫ eqToIso q) :
    Gs.map αY ≫ ρT.hom = ρ.hom ≫ αU := by
  refine map_comp_conjugate_eq_of_trace adjG adjGo lamG tr ρ αY htr (cIso.inv.app M) αU hαU
    ρT.hom ι hι ?_
  subst hc hρT
  simp [eqToHom_app]

/-- The inverse of `eqToIso p` is `eqToIso p.symm`. -/
lemma eqToIso_symm_eq {C : Type*} [Category C] {X Y : C} (p : X = Y) :
    (eqToIso p).symm = eqToIso p.symm :=
  Iso.ext rfl

/-- `traceAux_eq_counit_of_lowerShriekIso` for the trace map `exceptionalKunnethProdMapTraceAux`,
with the tensor structure of `G_s` and the comparisons assembled into an isomorphism
`ρ : G_s (F M ⊗ Q ω_Y) ≅ P M ⊗ Q_Z ω_U` (the restriction isomorphism of the external products),
where `c : P ≅ F ⋙ G_s` and `s : Q ⋙ G_s ≅ j_s ⋙ Q_Z` is the inverse of `θ`. -/
lemma traceAux_eq_counit_of_restrictionIso {𝒱 𝒲 𝒮 𝒳 𝒴 𝒵 : Type*} [Category 𝒱]
    [Category 𝒲] [Category 𝒮] [Category 𝒳] [Category 𝒴] [Category 𝒵] [MonoidalCategory 𝒱]
    [MonoidalCategory 𝒲] [BraidedCategory 𝒱] [BraidedCategory 𝒲] {G Go : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱}
    [Gs.Monoidal] (lamG : G ≅ Go) (adjGo : Go ⊣ Gs) (Q : 𝒴 ⥤ 𝒲) (Qz : 𝒵 ⥤ 𝒱)
    {gl : 𝒵 ⥤ 𝒴} {gr : 𝒴 ⥤ 𝒵} (adjg : gl ⊣ gr) {jo : 𝒵 ⥤ 𝒴} {js : 𝒴 ⥤ 𝒵} (adjjo : jo ⊣ js)
    (lamj : gl ≅ jo) (ιj : gr ≅ js) (hιj : ιj = conjugateIsoEquiv adjg adjjo lamj.symm)
    {Ry : 𝒮 ⥤ 𝒴} {Rz : 𝒮 ⥤ 𝒵} (I : 𝒮) (d : gr.obj (Ry.obj I) ≅ Rz.obj I)
    (bs : gl ⋙ Q ⟶ Qz ⋙ G) (ibs : IsIso bs) (BC : Qz ⋙ Go ⟶ jo ⋙ Q) (θ : js ⋙ Qz ≅ Q ⋙ Gs)
    (hbs : bs.app (Rz.obj I) ≫ lamG.hom.app (Qz.obj (Rz.obj I)) ≫ BC.app (Rz.obj I) =
      Q.map (lamj.hom.app (Rz.obj I)))
    (hBC : BC = Adjunction.exchangeLeft adjjo adjGo θ)
    {F : 𝒳 ⥤ 𝒲} {P : 𝒳 ⥤ 𝒱} (c : P ≅ F ⋙ Gs) (M : 𝒳)
    (hbr : Functor.LaxMonoidal.μ Gs (F.obj M) (Q.obj (Ry.obj I)) ≫
        Gs.map (β_ (F.obj M) (Q.obj (Ry.obj I))).hom =
      (β_ (Gs.obj (F.obj M)) (Gs.obj (Q.obj (Ry.obj I)))).hom ≫
        Functor.LaxMonoidal.μ Gs (Q.obj (Ry.obj I)) (F.obj M))
    (pfG : G.obj (Qz.obj (Rz.obj I)) ⊗ F.obj M ⟶ G.obj (Qz.obj (Rz.obj I) ⊗ Gs.obj (F.obj M)))
    (ipfG : IsIso pfG)
    (hpf : pfG ≫ lamG.hom.app _ ≫ adjGo.projectionComparison (Qz.obj (Rz.obj I)) (F.obj M) =
      lamG.hom.app (Qz.obj (Rz.obj I)) ▷ F.obj M)
    (a : F ⋙ Gs ≅ P) (ha : a = c.symm) (s : Q ⋙ Gs ≅ js ⋙ Qz) (hs : θ = s.symm)
    (δ : js.obj (Ry.obj I) ≅ Rz.obj I) (hδ : δ = ιj.symm.app (Ry.obj I) ≪≫ d)
    (ρ : Gs.obj (F.obj M ⊗ Q.obj (Ry.obj I)) ≅ P.obj M ⊗ Qz.obj (Rz.obj I))
    (hρ : ρ = (Functor.Monoidal.μIso Gs (F.obj M) (Q.obj (Ry.obj I))).symm ≪≫
      tensorIso (a.app M) (s.app (Ry.obj I) ≪≫ Qz.mapIso δ)) :
    exceptionalKunnethProdMapTraceAux (B := P.obj M) (B' := Gs.obj (F.obj M)) G Q Qz adjg I d bs ibs
        (c.hom.app M) (F.obj M) pfG ipfG =
      lamG.hom.app _ ≫ Go.map ρ.inv ≫ adjGo.counit.app _ := by
  unfold exceptionalKunnethProdMapTraceAux
  subst ha hs hδ hρ
  rw [traceAux_eq_counit_of_lowerShriekIso lamG adjGo Q Qz adjg adjjo lamj ιj hιj d bs BC s.symm
    hbs hBC (F.obj M) (c.hom.app M) hbr pfG hpf]
  simp

open Scheme

attribute [local instance] boundedConstructibleBraiding

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The trace map of an open immersion -/

attribute [local irreducible] boundedConstructibleLowerShriek boundedConstructibleUpperStar
  boundedConstructibleUpperShriek

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]


/-- The composition isomorphism `L(𝟙 × j)^* Lp_X^* ≅ Lp_X^*`, unfolded. -/
lemma prodMapUpperStarFstIso_eq (j : U ⟶ Y) :
    prodMapUpperStarFstIso (X := X) ℓ j =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)
        prod.fst).symm ≪≫ eqToIso (by rw [prod.map_fst, Category.comp_id]) :=
  rfl

/-- The composition isomorphism along `(𝟙 × j) ≫ p_X = p_X`, unfolded. -/
lemma boundedConstructibleUpperStarCompOfEq_prodMap_id_fst (j : U ⟶ Y) :
    boundedConstructibleUpperStarCompOfEq ℓ (prodMap_id_fst X j) =
      eqToIso (by rw [prodMap_id_fst X j]) ≪≫
        boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)
          prod.fst :=
  rfl

/-- `L(𝟙 × j)^* Lp_X^* ≅ Lp_X^*` is the inverse of the composition isomorphism along
`(𝟙 × j) ≫ p_X = p_X`. -/
lemma prodMapUpperStarFstIso_eq_symm (j : U ⟶ Y) :
    prodMapUpperStarFstIso (X := X) ℓ j =
      (boundedConstructibleUpperStarCompOfEq ℓ (prodMap_id_fst X j)).symm := by
  rw [prodMapUpperStarFstIso_eq, boundedConstructibleUpperStarCompOfEq_prodMap_id_fst,
    Iso.trans_symm, eqToIso_symm_eq]

/-- The composition isomorphism `L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*`, unfolded. -/
lemma prodMapUpperStarSndIso_eq (j : U ⟶ Y) :
    prodMapUpperStarSndIso (X := X) ℓ j =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)
        prod.snd).symm ≪≫ eqToIso (by rw [prod.map_snd]) ≪≫
          boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ prod.snd j :=
  rfl

/-- The pullback comparison of the square `q_U ≫ j = (𝟙 × j) ≫ q`, unfolded. -/
lemma boundedConstructiblePullbackSquareComparison_prodMap_id (j : U ⟶ Y) :
    boundedConstructiblePullbackSquareComparison _ ℓ (isPullback_prodMap_id X j).toCommSq.flip =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ prod.snd j).symm ≪≫
        eqToIso (by rw [(isPullback_prodMap_id X j).w]) ≪≫
          boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)
            prod.snd :=
  rfl

/-- The pullback comparison of the square `q_U ≫ j = (𝟙 × j) ≫ q` is the inverse of
`L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*`. -/
lemma boundedConstructiblePullbackSquareComparison_prodMap_id_eq_symm (j : U ⟶ Y) :
    boundedConstructiblePullbackSquareComparison _ ℓ (isPullback_prodMap_id X j).toCommSq.flip =
      (prodMapUpperStarSndIso (X := X) ℓ j).symm := by
  rw [prodMapUpperStarSndIso_eq, Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, eqToIso_symm_eq, boundedConstructiblePullbackSquareComparison_prodMap_id]

/-- `Rj^! ≅ Lj^*` is the conjugate of `Rj_! ≅ j_!`. -/
lemma boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugate
    {V W : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom] (f : V ⟶ W)
    [IsOpenImmersion f.left] :
    boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ f =
      conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ f)
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).symm := by
  unfold boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl
  rfl

/-- The composition isomorphism of the exceptional inverse images along `(𝟙 × j) ≫ p_X = p_X`,
unfolded. -/
lemma boundedConstructibleUpperShriekCompOfEq_prodMap_id_fst (j : U ⟶ Y) :
    boundedConstructibleUpperShriekCompOfEq ℓ (prodMap_id_fst X j) =
      eqToIso (by rw [prodMap_id_fst X j]) ≪≫
        boundedConstructibleUpperShriekComp_padicAlgCl ℓ (prod.map (𝟙 X) j) prod.fst :=
  rfl

theorem exceptionalKunnethMapRestriction (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ExceptionalKunnethMapRestriction ℓ j M := by
  refine map_comp_restriction_eq_of_trace
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.map (𝟙 X) j))
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ (prod.map (𝟙 X) j))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (prod.map (𝟙 X) j))
    (exceptionalKunnethProdMapTrace ℓ M j) (exceptionalKunnethSourceRestrictionIso ℓ j M)
    (exceptionalKunnethMap ℓ (Y := Y) M) ?_
    (boundedConstructibleUpperShriekCompOfEq ℓ (prodMap_id_fst X j)) _ _
    (boundedConstructibleUpperShriekCompOfEq_prodMap_id_fst ℓ j)
    (exceptionalKunnethMap ℓ (Y := U) M) (exceptionalKunnethMap_comp_prodMap ℓ M j)
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (prod.map (𝟙 X) j))
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugate ℓ (prod.map (𝟙 X) j))
    (exceptionalKunnethTargetRestrictionIso ℓ j M) _ rfl
  · rw [exceptionalKunnethProdMapTrace_eq]
    unfold exceptionalKunnethTraceOfSquare
    refine traceAux_eq_counit_of_restrictionIso
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (prod.map (𝟙 X) j))
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ (prod.map (𝟙 X) j))
      _ _ _ (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j) ?hιj _ _ _ _
      (boundedConstructibleOpenImmersionLowerShriekBaseChange' _ ℓ
        (isPullback_prodMap_id X j).toCommSq)
      (boundedConstructiblePullbackSquareComparison _ ℓ (isPullback_prodMap_id X j).toCommSq.flip)
      ?hbs ?hBC _ _ ?hbr _ _ ?hpf (prodMapUpperStarFstIso ℓ j) ?ha (prodMapUpperStarSndIso ℓ j)
      ?hs (dualizingComplexUpperStarIso ℓ j) ?hδ (exceptionalKunnethSourceRestrictionIso ℓ j M) ?hρ
    case hιj =>
      unfold boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl
      rfl
    case hbs =>
      exact boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ
        (isPullback_prodMap_id X j) (dualizingComplex' ℓ U)
    case hBC =>
      exact boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft _ ℓ
        (isPullback_prodMap_id X j).toCommSq
    case hbr => exact μ_boundedConstructibleUpperStar_braiding ℓ (prod.map (𝟙 X) j) _ _
    case hpf =>
      exact boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison ℓ _ _ _
    case ha => exact prodMapUpperStarFstIso_eq_symm ℓ j
    case hs => exact boundedConstructiblePullbackSquareComparison_prodMap_id_eq_symm ℓ j
    case hδ => rfl
    case hρ => rfl

end AlgebraicGeometry.ProEtale.CondensedRing
