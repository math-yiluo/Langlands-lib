/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.SourceExchangeCoherence

/-!

# The right side of the base-change core of the source exchange

For a proper morphism `f`, the right side of the base-change core of the exceptional Künneth
part of the source exchange, transposed along `Lf^* ⊣ Rf_*`, is the compact-support base change
followed by the unit of `Lr^* ⊣ Rr_!`
(`ProEtale.CondensedRing.sourceExchange_rightTranspose`). The ingredients are the unit of a
composite adjunction `L(r ≫ h)^* ⊣ R(r ≫ h)_!`
(`ProEtale.CondensedRing.upperStarLowerShriekAdjunction_unit_app_comp`) and the description of
the compact-support base change as a mate.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section TransposeAbstract

/-- The unit of a composite adjunction transported along isomorphisms `Sh ≅ Rh`, `Sg ≅ Rg`
and `Sgh ≅ Rgh` compatible with the composition isomorphisms. -/
lemma Adjunction.unit_app_comp_inv_app_of_comp {DX DY DZ : Type*} [Category DX] [Category DY]
    [Category DZ] {Lh : DX ⥤ DY} {Lg : DY ⥤ DZ} {Lgh : DX ⥤ DZ} {Rh : DY ⥤ DX} {Rg : DZ ⥤ DY}
    {Rgh : DZ ⥤ DX} {Sh : DY ⥤ DX} {Sg : DZ ⥤ DY} {Sgh : DZ ⥤ DX} (adjh : Lh ⊣ Rh)
    (adjg : Lg ⊣ Rg) (adjgh : Lgh ⊣ Rgh) (ih : Sh ≅ Rh) (ig : Sg ≅ Rg) (igh : Sgh ≅ Rgh)
    (uc : Lgh ≅ Lh ⋙ Lg) (lc : Rg ⋙ Rh ≅ Rgh) (sc : Sgh ≅ Sg ⋙ Sh) (K : DX)
    (hU : adjgh.unit.app K ≫ lc.inv.app (Lgh.obj K) =
      adjh.unit.app K ≫ Rh.map (adjg.unit.app (Lh.obj K)) ≫ Rh.map (Rg.map (uc.inv.app K)))
    (hL : ∀ P, sc.hom.app P ≫ ih.hom.app (Sg.obj P) ≫ Rh.map (ig.hom.app P) =
      igh.hom.app P ≫ lc.inv.app P) :
    adjgh.unit.app K ≫ igh.inv.app (Lgh.obj K) =
      adjh.unit.app K ≫ ih.inv.app (Lh.obj K) ≫ Sh.map (adjg.unit.app (Lh.obj K)) ≫
        Sh.map (ig.inv.app _) ≫ sc.inv.app _ ≫ Sgh.map (uc.inv.app K) := by
  have hL' (P : DZ) : Rh.map (ig.inv.app P) ≫ ih.inv.app (Sg.obj P) ≫ sc.inv.app P =
      lc.hom.app P ≫ igh.inv.app P := by
    refine (cancel_epi (lc.inv.app P)).1 ?_
    refine (cancel_epi (igh.hom.app P)).1 ?_
    rw [Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app, ← reassoc_of% (hL P)]
    simp only [← Rh.map_comp_assoc, Iso.hom_inv_id_app, Rh.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  have hU' : adjgh.unit.app K = adjh.unit.app K ≫ Rh.map (adjg.unit.app (Lh.obj K)) ≫
      Rh.map (Rg.map (uc.inv.app K)) ≫ lc.hom.app (Lgh.obj K) := by
    rw [← reassoc_of% hU, Iso.inv_hom_id_app, Category.comp_id]
  rw [hU', ← ih.inv.naturality_assoc, ← ih.inv.naturality_assoc, reassoc_of% (hL' _),
    ← igh.inv.naturality, ← lc.hom.naturality_assoc]
  simp only [Functor.comp_map, Category.assoc]

/-- The abstract form of `sourceExchange_rightTranspose`. -/
lemma Adjunction.map_comp_counit_eq_of_mate {CV CW CU CY CX : Type*} [Category CV] [Category CW]
    [Category CU] [Category CY] [Category CX] {hs : CV ⥤ CW} {rs : CW ⥤ CU} {qs : CV ⥤ CU}
    {fs : CY ⥤ CX} {Lh : CW ⥤ CV} {Lr : CU ⥤ CW} {Lq Sq : CU ⥤ CV} {Lπ : CV ⥤ CY}
    {LzX : CW ⥤ CX} {Lrz : CU ⥤ CX} {Lf Sf : CX ⥤ CY} (adjq : qs ⊣ Sq) (adjf : fs ⊣ Sf)
    (adjq' : qs ⊣ Lq) (adjh : hs ⊣ Lh) (adjr : rs ⊣ Lr) (adjf' : fs ⊣ Lf) (σqi : Sq ⟶ Lq)
    (σf : Lf ⟶ Sf) (sq : Lq ⋙ Lπ ⟶ Lrz ⋙ Lf) (sqA : Lh ⋙ Lπ ⟶ LzX ⋙ Lf) (lc : Lr ⋙ Lh ⟶ Lq)
    (lc' : Lr ⋙ LzX ⟶ Lrz) {D : CV} {E' : CU} {K : CX}
    (ex : fs.obj (Lπ.obj D) ⟶ LzX.obj (hs.obj D)) (uc : rs.obj (hs.obj D) ⟶ qs.obj D)
    (φ : qs.obj D ⟶ E') (e : Lrz.obj E' ⟶ K)
    (hε : ∀ x, fs.map (σf.app x) ≫ adjf.counit.app x = adjf'.counit.app x)
    (hη : adjq.unit.app D ≫ σqi.app (qs.obj D) = adjq'.unit.app D)
    (hU : adjq'.unit.app D = adjh.unit.app D ≫ Lh.map (adjr.unit.app (hs.obj D)) ≫
      lc.app (rs.obj (hs.obj D)) ≫ Lq.map uc)
    (hmate : Lπ.map (adjh.unit.app D) ≫ sqA.app (hs.obj D) =
      adjf'.unit.app (Lπ.obj D) ≫ Lf.map ex)
    (hC : Lπ.map (lc.app E') ≫ sq.app E' = sqA.app (Lr.obj E') ≫ Lf.map (lc'.app E')) :
    fs.map (Lπ.map (adjq.homEquiv _ _ φ) ≫ Lπ.map (σqi.app E') ≫ sq.app E' ≫ Lf.map e ≫
        σf.app K) ≫ adjf.counit.app K =
      ex ≫ LzX.map (adjr.unit.app (hs.obj D) ≫ Lr.map (uc ≫ φ)) ≫ lc'.app E' ≫ e := by
  have hcancel : fs.map (Lf.map e) ≫ fs.map (σf.app K) ≫ adjf.counit.app K =
      adjf'.counit.app (Lrz.obj E') ≫ e := by
    rw [hε]; exact adjf'.counit_naturality e
  simp only [Functor.map_comp (fs), Category.assoc]
  rw [hcancel]
  simp only [← Category.assoc]
  refine congrArg (· ≫ e) ?_
  have hn := sqA.naturality (adjr.unit.app (hs.obj D) ≫ Lr.map (uc ≫ φ))
  simp only [Functor.comp_map] at hn
  have key : adjf'.unit.app (Lπ.obj D) ≫
      Lf.map (ex ≫ LzX.map (adjr.unit.app (hs.obj D) ≫ Lr.map (uc ≫ φ)) ≫ lc'.app E') =
      Lπ.map (adjh.unit.app D ≫ Lh.map (adjr.unit.app (hs.obj D) ≫ Lr.map (uc ≫ φ)) ≫
        lc.app E') ≫ sq.app E' := by
    simp only [Functor.map_comp, Category.assoc] at hn ⊢
    rw [← reassoc_of% hmate, hC, reassoc_of% hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  refine (Adjunction.homEquiv_counit adjf' _ _ _).symm.trans ?_
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit adjf', key, Adjunction.homEquiv_unit adjq]
  simp only [← Functor.map_comp, Category.assoc]
  refine congrArg (fun x ↦ Lπ.map x ≫ sq.app E') ?_
  rw [σqi.naturality, reassoc_of% hη, hU]
  have hl := lc.naturality (uc ≫ φ)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hl ⊢
  rw [hl]

end TransposeAbstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Transpose

variable {X Y W U V : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

/-- The unit of `L(r ≫ h)^* ⊣ R(r ≫ h)_!` is the unit of `Lh^* ⊣ Rh_!` followed by the unit of
`Lr^* ⊣ Rr_!` and the composition isomorphisms. -/
lemma upperStarLowerShriekAdjunction_unit_app_comp (r : U ⟶ W) (h : W ⟶ V) [IsProper r.left]
    [IsProper h.left] [IsProper (r ≫ h).left] (D : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (r ≫ h)).unit.app D =
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ h).unit.app D ≫
        (boundedConstructibleLowerShriek ℓ h).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app
            ((boundedConstructibleUpperStar _ ℓ h).obj D)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r h).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (r ≫ h)).map
          ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app D) := by
  have hu := unit_conjugateEquiv
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ h))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ h).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ r))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r h).inv D
  rw [Adjunction.comp_unit_app, Category.assoc] at hu
  have key := Adjunction.unit_app_comp_inv_app_of_comp
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ r)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ h))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ h))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r h)
    (boundedConstructibleLowerStarComp ℓ r h)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r h) D hu
    (fun P ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ r h P)
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  exact key

/-- The composition isomorphisms of `R(r ≫ h)_!` and `R(r ≫ z)_!` are compatible with the
squares `h ≫ π = z ≫ f` and `(r ≫ h) ≫ π = (r ≫ z) ≫ f`. -/
lemma lowerShriek_map_lowerShriekComp_inv_app_comp_squareIso (r : U ⟶ W) (h : W ⟶ V)
    (π : V ⟶ Y) (z : W ⟶ X) (f : X ⟶ Y) (hw : h ≫ π = z ≫ f)
    (w : (r ≫ h) ≫ π = (r ≫ z) ≫ f) (E : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ π).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r h).inv.app E) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app E =
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hw).hom.app
        ((boundedConstructibleLowerShriek ℓ r).obj E) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r z).inv.app E) := by
  have hp := lowerShriekComp_pushforwardSquare ℓ r h r h π z f rfl hw
    (by rw [← Category.assoc, w]) E
  have h₁ := lowerShriek_map_lowerShriekComp_inv_app_comp_inv_app ℓ r h π E
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj] at hp
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc] at hp ⊢
  simp only [reassoc_of% h₁, eqToHom_trans_assoc]
  exact hp

/-- The compact-support base change of a cartesian square `h ≫ π = z ≫ f` with `h` and `f`
proper, read through the units of `Lh^* ⊣ Rh_!` and `Lf^* ⊣ Rf_!`. -/
lemma lowerShriek_map_unit_comp_squareIso_hom_app {f : X ⟶ Y} {π : V ⟶ Y} {z : W ⟶ X}
    {h : W ⟶ V} [IsProper f.left] [IsProper h.left] (hA : IsPullback h z π f)
    (D : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ π).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ h).unit.app D) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hA.w).hom.app _ =
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app _ ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA).app D) := by
  have hm := unit_mateEquiv_symm
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ h)
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hA.w).hom D
  rw [← boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ hA] at hm
  exact hm

variable {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom] (aY : Y ⟶ P) (f : X ⟶ Y) [IsProper f.left] (p₂ : U ⟶ X) (π₁ π₂ : V ⟶ Y)
  (zX : W ⟶ X) (h : W ⟶ V) [IsProper h.left] (r : U ⟶ W) [IsProper r.left]
  (hA : IsPullback h zX π₁ f) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

-- the compactly supported direct images are unfolded in the defeq checks
/-- The right side of the base-change core, transposed along `Lf^* ⊣ Rf_*`. -/
theorem sourceExchange_rightTranspose [IsProper (r ≫ h).left]
    (wq₁ : (r ≫ h) ≫ π₁ = (r ≫ zX) ≫ f) (wq₂ : (r ≫ h) ≫ π₂ = p₂ ≫ f)
    (e : (boundedConstructibleLowerShriek ℓ (r ≫ zX)).obj
      ((boundedConstructibleUpperStar _ ℓ (r ≫ zX)).obj K ⊗
        (boundedConstructibleUpperStar _ ℓ p₂).obj
        ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))) ⟶ K) :
    (boundedConstructibleUpperStar _ ℓ f).map
        ((boundedConstructibleLowerShriek ℓ π₁).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ h)).homEquiv _ _
              ((Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (r ≫ h)) _ _).inv ≫
                (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
                  ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))) ≫
          (boundedConstructibleLowerShriek ℓ π₁).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ h)).inv.app _) ≫
          (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wq₁).hom.app _ ≫
          (boundedConstructibleLowerShriek ℓ f).map e ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA).app _ ≫
      (boundedConstructibleLowerShriek ℓ zX).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app _ ≫
          (boundedConstructibleLowerShriek ℓ r).map
            ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app _ ≫
              (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (r ≫ h)) _ _).inv ≫
              (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
                ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _))))) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r zX).inv.app _ ≫ e := by
  have key := Adjunction.map_comp_counit_eq_of_mate
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ h))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (r ≫ h))
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ h)
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r)
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ h)).inv
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wq₁).hom
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hA.w).hom
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r h).inv
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r zX).inv
    ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hA).app _)
    ((boundedConstructibleUpperStarComp _ ℓ r h).inv.app _)
    ((Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (r ≫ h)) _ _).inv ≫
      (prodUpperStarCounit ℓ wq₁ K ⊗ₘ prodUpperStarCounit ℓ wq₂
        ((boundedConstructibleUpperShriek ℓ (f ≫ aY)).obj (𝟙_ _)))) e
    (fun _ ↦ rfl) rfl (upperStarLowerShriekAdjunction_unit_app_comp ℓ r h _)
    (lowerShriek_map_unit_comp_squareIso_hom_app ℓ hA _)
    (lowerShriek_map_lowerShriekComp_inv_app_comp_squareIso ℓ r h π₁ zX f hA.w wq₁ _)
  exact key

end Transpose

end AlgebraicGeometry.ProEtale.CondensedRing
