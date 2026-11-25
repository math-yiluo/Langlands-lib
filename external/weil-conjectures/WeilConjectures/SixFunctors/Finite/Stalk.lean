/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# The stalks of a pushforward along a finite morphism

For a finite morphism `f : X ⟶ Y` and a geometric point `y : Spec Ω ⟶ Y` with `Ω`
algebraically closed, the stalk of `f_* G` at `y` is the product of the stalks of `G` at the
finitely many geometric points `t` of `X` over `y`:
`(f_* G)_y ≅ ∏_{t ↦ y} G_t` (`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`).

The stalk `(f_* G)_y` is the colimit of the sections `G (U ×_Y X)` over the pointed étale
neighbourhoods `(U, u)` of `y`. The split neighbourhoods
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd`) are cofinal among them, and over a split
neighbourhood `U ×_Y X` decomposes into pairwise disjoint clopen pieces indexed by the `t`,
so that `G (U ×_Y X) = ∏_t G (piece_t)`. Finite products commute with the filtered colimit
(`A` satisfies AB5), and the colimit of `G (piece_t)` over the split neighbourhoods is the
stalk `G_t`, the pieces being cofinal among the pointed étale neighbourhoods of `t`
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd.initial_pieceFunctor`). The classical argument through the
strict henselization (blueprint remark `lemma-finite-direct-images--1`) is
not the one formalised here.

## Main definitions

- `AlgebraicGeometry.Etale.stalkRestrict`: the canonical map `(f_* G)_y ⟶ G_t` for a
  geometric point `t` of `X` over `y`, restricting a germ at `y` to the point `(u, t)` of
  `U ×_Y X`.
- `AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`: the natural isomorphism
  `(f)_*[A] ⋙ (pointSmallEtale y).sheafFiber ≅ ∏ᶜ fun t ↦ (pointSmallEtale t.1).sheafFiber`,
  whose components are the `stalkRestrict`.

## Main results

- `AlgebraicGeometry.Etale.stalkRestrict_eq_counit` and its indexed form
  `AlgebraicGeometry.Etale.stalkRestrict_eq_counit'`: the map `stalkRestrict` is the stalk of
  the counit `f^* f_* G ⟶ G`, read through the identification
  `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso` of the stalk of `f^* f_* G` at a
  geometric point `t` of `X` with the stalk of `f_* G` at its image. Neither statement is
  about finite morphisms.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom Scheme.Hom.SplitNbhd

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

section Instances

instance : HasColimitsOfShape (SplitNbhd f y)ᵒᵖ A :=
  hasColimitsOfShape_of_essentiallySmall.{u + 1} _ _

instance : EssentiallySmall.{u + 1} (SplitNbhd f y)ᵒᵖ :=
  essentiallySmall_of_small_of_locallySmall _

instance : FinallySmall.{u + 1} (SplitNbhd f y)ᵒᵖ :=
  finallySmall_of_essentiallySmall _

/-- Colimits over the split neighbourhoods of `y` are exact: the category is filtered and
essentially small, and `A` satisfies AB5. -/
instance hasExactColimitsOfShape_splitNbhd_op :
    HasExactColimitsOfShape (SplitNbhd f y)ᵒᵖ A :=
  hasExactColimitsOfShape_of_final _ (FinallySmall.fromFilteredFinalModel.{u + 1} (SplitNbhd f y)ᵒᵖ)

/-- Colimits over the split neighbourhoods of `y` commute with products indexed by the
(finite) geometric fibre. -/
instance preservesLimitsOfShape_discrete_geometricFiber_colim :
    PreservesLimitsOfShape (Discrete (GeometricFiber f y))
      (colim (J := (SplitNbhd f y)ᵒᵖ) (C := A)) :=
  have := HasExactColimitsOfShape.preservesFiniteLimits (J := (SplitNbhd f y)ᵒᵖ) (C := A)
  have : Fintype (GeometricFiber f y) := Fintype.ofFinite _
  preservesLimitsOfShape_of_equiv
    (Discrete.equivalence (Fintype.equivFin (GeometricFiber f y)).symm) colim

end Instances

section StalkRestrict

variable (t : GeometricFiber f y)

omit [IsFinite f] [IsAlgClosed Ω] in
/-- The pointed étale neighbourhood `(U ×_Y X, (u, t))` of the geometric point `t` of `X`
obtained from a pointed étale neighbourhood `(U, u)` of `y`, functorially. -/
@[simps!]
def Etale.baseChangeNbhd : Nbhd y ⥤ (pointSmallEtale t.1).fiber.Elements where
  obj c := Functor.elementsMk _ (f.Etale.obj c.1)
    (CategoryTheory.Over.homMk (basePt f c t) (basePt_snd f c t))
  map g := Functor.Elements.homMk (f.Etale.map g.val)
    (CategoryTheory.Over.OverMorphism.ext (basePt_comp_etale_map_left f g t))
  map_id _ := Functor.Elements.hom_ext (f.Etale.map_id _)
  map_comp _ _ := Functor.Elements.hom_ext (f.Etale.map_comp _ _)

variable (G : Sheaf X.smallEtaleTopology A)

/-- The restriction of germs at `y` of `f_* G` to germs at a geometric point `t` of `X` over
`y`: a section of `G` over `U ×_Y X` is a section over the pointed étale neighbourhood
`(U ×_Y X, (u, t))` of `t` (the restriction of stalks of blueprint
`lemma-finite-direct-images--1`). -/
def Etale.stalkRestrict :
    (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) ⟶
      (pointSmallEtale t.1).sheafFiber.obj G :=
  colimit.pre ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)
    (Etale.baseChangeNbhd f y t).op

omit [IsFinite f] [HasSmallSiteSheafify A] in
/-- `stalkRestrict` on the germ of a section over `(U, u)`: it is the germ of the same section
at the pointed étale neighbourhood `(U ×_Y X, (u, t))` of `t`. -/
@[reassoc (attr := simp)]
lemma Etale.toPresheafFiber_stalkRestrict (c : Nbhd y) :
    (pointSmallEtale y).toPresheafFiber c.1 c.2 ((f)_*[A].obj G).obj ≫
        Etale.stalkRestrict A f y t G =
      (pointSmallEtale t.1).toPresheafFiber (f.Etale.obj c.1)
        ((Etale.baseChangeNbhd f y t).obj c).2 G.obj :=
  colimit.ι_pre ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)
    (Etale.baseChangeNbhd f y t).op (op c)

omit [IsFinite f] [HasSmallSiteSheafify A] in
/-- `stalkRestrict` is natural in the sheaf. -/
@[reassoc]
lemma Etale.stalkRestrict_naturality {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G') :
    Etale.stalkRestrict A f y t G ≫ (pointSmallEtale t.1).sheafFiber.map φ =
      (pointSmallEtale y).sheafFiber.map ((f)_*[A].map φ) ≫ Etale.stalkRestrict A f y t G' := by
  apply (pointSmallEtale y).presheafFiber_hom_ext
  intro U u
  change (pointSmallEtale y).toPresheafFiber U u _ ≫ Etale.stalkRestrict A f y t G ≫
      (pointSmallEtale t.1).presheafFiber.map φ.hom =
    (pointSmallEtale y).toPresheafFiber U u _ ≫
      (pointSmallEtale y).presheafFiber.map ((f)_*[A].map φ).hom ≫ Etale.stalkRestrict A f y t G'
  erw [Etale.toPresheafFiber_stalkRestrict_assoc A f y t G (Functor.elementsMk _ U u),
    GrothendieckTopology.Point.toPresheafFiber_naturality,
    GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
    Etale.toPresheafFiber_stalkRestrict A f y t G' (Functor.elementsMk _ U u)]
  rfl

omit [IsFinite f] in
/-- **The stalk restriction is the counit of `f^* ⊣ f_*` on stalks.** For a geometric point
`s` of `X`, the canonical map `(f_* G)_{s ≫ f} ⟶ G_s` of
`AlgebraicGeometry.Etale.stalkRestrict` is the stalk at `s` of the counit
`f^* f_* G ⟶ G`, read through the identification
`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso` of `(f^* f_* G)_s` with
`(f_* G)_{s ≫ f}`.

This bridges the concrete description of the stalk of a direct image, as a colimit along
base change of pointed étale neighbourhoods, with the adjunction-theoretic description that
the base change map `AlgebraicGeometry.Etale.baseChangeMap` is built from. -/
lemma Etale.stalkRestrict_eq_counit (s : Spec (.of Ω) ⟶ X)
    (G : Sheaf X.smallEtaleTopology A) :
    Etale.stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G =
      (Etale.upperStarCompSheafFiberIso A f s).inv.app ((f)_*[A].obj G) ≫
        (pointSmallEtale s).sheafFiber.map
          ((Etale.upperStarLowerStarAdjunction A f).counit.app G) := by
  -- both sides are maps out of the filtered colimit defining `(f_* G)_{s ≫ f}`
  apply (pointSmallEtale (s ≫ f)).presheafFiber_hom_ext
  intro V u
  change (pointSmallEtale (s ≫ f)).toPresheafFiber V u ((f)_*[A].obj G).obj ≫
      Etale.stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G =
    (pointSmallEtale (s ≫ f)).toPresheafFiber V u ((f)_*[A].obj G).obj ≫
      (Etale.upperStarCompSheafFiberIso A f s).inv.app ((f)_*[A].obj G) ≫
        (pointSmallEtale s).sheafFiber.map
          ((Etale.upperStarLowerStarAdjunction A f).counit.app G)
  -- on the germ of a section over `(V, u)` the left hand side is the germ at `(V ×_Y X, (u, s))`
  rw [Etale.toPresheafFiber_stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G
    (Functor.elementsMk _ V u)]
  -- the right hand side is the three steps of `upperStarCompSheafFiberIso`, in reverse
  simp only [Etale.upperStarCompSheafFiberIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.assoc, ← Functor.map_comp]
  -- the comparison of the constructed pullback with the abstract one absorbs into the counit
  have hc : (Functor.sheafPullbackConstruction.sheafPullbackIso
        (MorphismProperty.Over.pullback @Etale ⊤ f) A
        (Y.smallGrothendieckTopology (P := @Etale))
        (X.smallGrothendieckTopology (P := @Etale))).hom.app ((f)_*[A].obj G) ≫
      (Etale.upperStarLowerStarAdjunction A f).counit.app G =
      (Functor.sheafAdjunctionContinuous (MorphismProperty.Over.pullback @Etale ⊤ f) A
        (Y.smallGrothendieckTopology (P := @Etale))
        (X.smallGrothendieckTopology (P := @Etale))).counit.app G :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ G
  rw [hc, GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  -- what is left is the germ description of `sheafFiberComapIso`, at the transported point
  refine Eq.trans (congrArg
    (fun w ↦ (pointSmallEtale s).toPresheafFiber (f.Etale.obj V) w G.obj) ?_)
    (GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_counit
      (pointSmallEtale s) f.Etale (Hom.coverPreserving_etale f) A G V _).symm
  -- the transported point is `(u, s)`, since its two components are `u` and `s`
  refine CategoryTheory.Over.OverMorphism.ext (Limits.pullback.hom_ext ?_ ?_)
  · exact (basePt_fst f (Functor.elementsMk _ V u) ⟨s, rfl⟩).trans
      (pointSmallEtaleFiberEtaleIso_inv_app_left_fst f s V u).symm
  · exact (basePt_snd f (Functor.elementsMk _ V u) ⟨s, rfl⟩).trans
      (pointSmallEtaleFiberEtaleIso_inv_app_left_snd f s V u).symm

omit [IsFinite f] in
/-- **The stalk restriction is the counit of `f^* ⊣ f_*` on stalks**, in the form indexed by
a geometric point `t` of `X` in the geometric fibre of `f` over `y`. This is
`AlgebraicGeometry.Etale.stalkRestrict_eq_counit` with `y` in place of `t.1 ≫ f`, the two
stalks being identified along `t.2 : t.1 ≫ f = y`. -/
lemma Etale.stalkRestrict_eq_counit' (G : Sheaf X.smallEtaleTopology A) :
    Etale.stalkRestrict A f y t G =
      eqToHom (by rw [t.2]) ≫
        (Etale.upperStarCompSheafFiberIso A f t.1).inv.app ((f)_*[A].obj G) ≫
          (pointSmallEtale t.1).sheafFiber.map
            ((Etale.upperStarLowerStarAdjunction A f).counit.app G) := by
  obtain ⟨t, rfl⟩ := t
  rw [eqToHom_refl, Category.id_comp]
  exact Etale.stalkRestrict_eq_counit A f t G

end StalkRestrict

section StalkFormula

variable (G : Sheaf X.smallEtaleTopology A)

/-- The comparison of the stalk of `f_* G` at `y` with the colimit of the sections of `G` over
`U ×_Y X` for `U` running over the split neighbourhoods of `y`. -/
def Etale.stalkIsoColimitSections :
    colimit (sectionsFunctor f y G) ≅ (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) :=
  Functor.Final.colimitIso (forget f y).op
    ((Functor.Elements.π (pointSmallEtale y).fiber).op ⋙ ((f)_*[A].obj G).obj)

/-- The comparison of the colimit of the sections of `G` over the `t`-th pieces of the split
neighbourhoods of `y` with the stalk of `G` at `t`. -/
def Etale.pieceIsoStalk (t : GeometricFiber f y) :
    colimit (pieceSectionsFunctor f y G t) ≅ (pointSmallEtale t.1).sheafFiber.obj G :=
  Functor.Final.colimitIso (pieceFunctor t).op
    ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)

omit [HasSmallSiteSheafify A] in
set_option backward.isDefEq.respectTransparency.types false in
/-- The components `stalkRestrict` assemble, through the split neighbourhoods, to the
composite of the product decomposition of the sections and the commutation of the colimit
with finite products. -/
lemma Etale.stalkIsoColimitSections_hom_comp_piLift_stalkRestrict :
    (Etale.stalkIsoColimitSections A f y G).hom ≫
        Pi.lift (fun t ↦ Etale.stalkRestrict A f y t G) =
      colim.map (sectionsIsoPi f y G).hom ≫
        (PreservesProduct.iso colim (pieceSectionsFunctor f y G)).hom ≫
        Limits.Pi.map fun t ↦ (Etale.pieceIsoStalk A f y G t).hom := by
  apply colimit.hom_ext
  intro s
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.lift_comp_π, Limits.Pi.map_π, PreservesProduct.iso_hom]
  erw [Etale.stalkIsoColimitSections, Functor.Final.ι_colimitIso_hom_assoc,
    Etale.toPresheafFiber_stalkRestrict, piComparison_comp_π_assoc, colim_map, ι_colimMap_assoc,
    ι_colimMap_assoc, sectionsIsoPi_hom, ← NatTrans.comp_app_assoc, Pi.lift_comp_π,
    Etale.pieceIsoStalk, Functor.Final.ι_colimitIso_hom]
  exact (colimit.w ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)
    (Functor.Elements.homMk
      (x := Functor.elementsMk _ (s.unop.pieceObj t) (s.unop.piecePt t))
      (y := (Etale.baseChangeNbhd f y t).obj s.unop.obj) (s.unop.pieceIncl t)
      (CategoryTheory.Over.OverMorphism.ext (s.unop.piecePt_comp_pieceIncl t))).op).symm

/-- The stalk of `f_* G` at `y` is the product of the stalks of `G` at the geometric points
over `y`, through the restriction maps `stalkRestrict`. -/
instance Etale.isIso_piLift_stalkRestrict :
    IsIso (Pi.lift fun t ↦ Etale.stalkRestrict A f y t G) := by
  have h := Etale.stalkIsoColimitSections_hom_comp_piLift_stalkRestrict A f y G
  rw [← Iso.eq_inv_comp] at h
  rw [h]
  infer_instance

/-- The stalk of `f_* G` at `y` as the product of the stalks of `G` at the geometric points
over `y`, for a single sheaf `G`. -/
def Etale.stalkIsoPi (G : Sheaf X.smallEtaleTopology A) :
    (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) ≅
      ∏ᶜ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber.obj G :=
  asIso (Pi.lift fun t ↦ Etale.stalkRestrict A f y t G)

omit [HasSmallSiteSheafify A] in
@[simp]
lemma Etale.stalkIsoPi_hom (G : Sheaf X.smallEtaleTopology A) :
    (Etale.stalkIsoPi A f y G).hom = Pi.lift fun t ↦ Etale.stalkRestrict A f y t G := rfl

/-- **The geometric stalk formula for a finite direct image** (blueprint
`lemma-finite-direct-images--1`). For a finite morphism
`f : X ⟶ Y` and a geometric point `y` of `Y` with algebraically closed residue field, the
stalk of `f_* G` at `y` is the finite product of the stalks of `G` at the geometric points of
`X` over `y`, naturally in the sheaf `G`. -/
def Etale.lowerStarSheafFiberIsoPi :
    (f)_*[A] ⋙ (pointSmallEtale y).sheafFiber ≅
      ∏ᶜ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber :=
  NatIso.ofComponents
    (fun G ↦ Etale.stalkIsoPi A f y G ≪≫
      (piObjIso (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) G).symm)
    (fun {G G'} φ ↦ by
      rw [← cancel_mono
        (piObjIso (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) G').hom]
      apply Pi.hom_ext
      intro t
      simp only [Functor.comp_map, Iso.trans_hom, Etale.stalkIsoPi_hom, Iso.symm_hom,
        Category.assoc, piObjIso_hom_comp_π]
      rw [NatTrans.naturality, piObjIso_inv_comp_π_assoc, piObjIso_inv_comp_π, Pi.lift_comp_π,
        Pi.lift_comp_π_assoc, Etale.stalkRestrict_naturality])

end StalkFormula

end AlgebraicGeometry

end
