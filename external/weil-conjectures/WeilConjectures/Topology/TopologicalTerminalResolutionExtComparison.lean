/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison

/-! # Terminal-section resolution computations and Ext cocycles

Source: Stacks Project, Tags 01FT, 06XR and 01F2, injective-resolution cohomology computation.
(blueprint: lem-sc-topological-terminal-resolution-ext-comparison)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

private noncomputable def freeSectionsEquiv
    {C : Type u} [SmallCategory C] (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (op U) (𝟙 U) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

private noncomputable def sectionsEquiv
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ F).trans
    (freeSectionsEquiv U F.obj)

private noncomputable def sectionsIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) :
    preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
  NatIso.ofComponents (fun F ↦ (sectionsEquiv J U F).toAddCommGrpIso) (by
    intro F G f
    ext a
    change sectionsEquiv J U G (a ≫ f) =
      f.hom.app (op U) (sectionsEquiv J U F a)
    dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    dsimp [freeSectionsEquiv]
    rfl)

private lemma sectionsEquiv_apply
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}] (U : C) (M : Sheaf T AddCommGrpCat.{u})
    (z : (presheafToSheaf T AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ M) :
    sectionsEquiv T U M z = z.hom.app (op U)
      ((toSheafify T (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
        (FreeAbelianGroup.of (𝟙 U))) := by
  rfl

private noncomputable def derivedIso
    {C : Type*} [Category C] [Abelian C] [HasInjectiveResolutions C]
    {H K : C ⥤ AddCommGrpCat.{u}} [H.Additive] [K.Additive]
    (e : H ≅ K) (p : ℕ) : H.rightDerived p ≅ K.rightDerived p where
  hom := NatTrans.rightDerived e.hom p
  inv := NatTrans.rightDerived e.inv p
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

private noncomputable def terminalSectionsIso
    {Z X : TopCat.{u}} (f : Z ⟶ X) :
    TopCat.Sheaf.pushforwardAb f ⋙
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ≅
      sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
        (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents
    (fun M ↦ M.obj.mapIso (eqToIso (congrArg op (Opens.map_top f)))) (by
      intro M N g
      change g.hom.app _ ≫ N.obj.map _ = M.obj.map _ ≫ g.hom.app _
      exact (g.hom.naturality (eqToHom (congrArg op (Opens.map_top f)))).symm)

private lemma class_map
    {K L : CochainComplex AddCommGrpCat.{u} ℕ} (φ : K ⟶ L) (p : ℕ)
    (c : K.cycles p) (d : L.cycles p) (h : φ.f p (K.iCycles p c) = L.iCycles p d) :
    HomologicalComplex.homologyMap φ p (K.homologyπ p c) = L.homologyπ p d := by
  have hc : HomologicalComplex.cyclesMap φ p c = d := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles p)).mp inferInstance
    exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ p) c).trans h
  have hh := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ p) c
  simpa only [ConcreteCategory.comp_apply, hc] using hh

/-- Terminal sections and terminal Ext cohomology admit comparisons compatible
with the homology map of any augmented resolution comparison. No spectral object
or edge map occurs in this statement.

Source: Stacks Project, Tags 01FT, 06XR and 01F2, cohomology of an injective resolution.
(blueprint: lem-sc-topological-terminal-resolution-ext-comparison)

Proof: Sheafification adjunction, the free abelian adjunction, and Yoneda identify
Hom from the free terminal sheaf with sections at the terminal open, additively
and naturally. Apply this identification degreewise to the chosen injective
resolution, then take homology. Ext computed from that resolution gives x in
every degree, natural in the sheaf by resolution comparison and homotopy
independence. The same construction on Z gives the comparison for Z sections.
The generator identity ha identifies sections of f_*M on X with sections of M
on Z; the inverse is restriction along the equality f^{-1}(top)=top. This is an
isomorphism of additive functors. Derive it and compose with the Z comparison to
obtain zc for the composite f_* followed by X sections. The degreewise Hom/section
identifications take s composed with phi to z, because a composed with f_*z is
s composed with phi. Thus the induced homology map sends the represented Ext
class to I.extMk z. The canonical right-derived resolution comparisons in the
formula are precisely the endpoint identifications in this computation.
Naturality of the Hom/section isomorphism and homotopy independence extend the
calculation from chosen resolutions to every I,J and augmented phi.
Empty spaces and degree zero require no separate assumption: Yoneda and the
sheafification adjunction apply there too, and negative resolution degrees are zero.
-/
theorem exists_topological_terminal_resolution_ext_comparison
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)))
    (ha : (∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f))))) :
    let G := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    ∃ x : ∀ n : ℕ, G.rightDerived n ≅
        Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
      ∃ zc : ∀ n : ℕ, (TopCat.Sheaf.pushforwardAb f ⋙ G).rightDerived n ≅
          Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
            (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
    (∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (I : InjectiveResolution F)
        (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
        (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
        (_hφ : J.ι.f 0 ≫ φ.f 0 =
          (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0)) (p : ℕ)
        (s : (presheafToSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
            J.cocomplex.X p)
        (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
        (z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶
            I.cocomplex.X p)
        (hz : z ≫ I.cocomplex.d p (p + 1) = 0)
        (_hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
        (zc p).hom.app F
          ((I.isoRightDerivedObj (TopCat.Sheaf.pushforwardAb f ⋙ G) p).inv
            (HomologicalComplex.homologyMap
              ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) p
              ((J.isoRightDerivedObj G p).hom
                ((x p).inv.app ((TopCat.Sheaf.pushforwardAb f).obj F)
                  (J.extMk s (p + 1) rfl hs))))) =
            I.extMk z (p + 1) rfl hz) := by
  let P := TopCat.Sheaf.pushforwardAb f
  let GX := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let GZ := sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
    (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let AX := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)
  let AZ := (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
    (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)
  let eX := sectionsIso (Opens.grothendieckTopology X) (⊤ : Opens X)
  let eZ := sectionsIso (Opens.grothendieckTopology Z) (⊤ : Opens Z)
  obtain ⟨x, hx⟩ := exists_ext_rightDerived_cocycle_comparison AX GX eX
  obtain ⟨y, hy⟩ := exists_ext_rightDerived_cocycle_comparison AZ GZ eZ
  let t : P ⋙ GX ≅ GZ := terminalSectionsIso f
  refine ⟨x, fun p ↦ derivedIso t p ≪≫ y p, ?_⟩
  intro F I J φ _hφ p s hs z hz hsz
  let K := (GX.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let L := ((P ⋙ GX).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let M := (GZ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let δ : K ⟶ L := (GX.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  let β : L ⟶ M := (NatTrans.mapHomologicalComplex t.hom _).app I.cocomplex
  have hsc : K.d p (p + 1) (eX.hom.app (J.cocomplex.X p) s) = 0 := by
    have h := ConcreteCategory.congr_hom
      (eX.hom.naturality (J.cocomplex.d p (p + 1))) s
    change eX.hom.app _ (s ≫ J.cocomplex.d p (p + 1)) =
      K.d p (p + 1) (eX.hom.app _ s) at h
    rw [hs, map_zero] at h
    exact h.symm
  have hzc : M.d p (p + 1) (eZ.hom.app (I.cocomplex.X p) z) = 0 := by
    have h := ConcreteCategory.congr_hom
      (eZ.hom.naturality (I.cocomplex.d p (p + 1))) z
    change eZ.hom.app _ (z ≫ I.cocomplex.d p (p + 1)) =
      M.d p (p + 1) (eZ.hom.app _ z) at h
    rw [hz, map_zero] at h
    exact h.symm
  let c : K.cycles p := (K.sc p).abCyclesIso.inv
    ⟨eX.hom.app (J.cocomplex.X p) s, by
      change _ = 0
      have hp : (ComplexShape.up ℕ).next p = p + 1 :=
        ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
      change (K.d p ((ComplexShape.up ℕ).next p)).hom
        ((eX.hom.app (J.cocomplex.X p)).hom s) = 0
      rw [hp]
      exact hsc⟩
  let d : M.cycles p := (M.sc p).abCyclesIso.inv
    ⟨eZ.hom.app (I.cocomplex.X p) z, by
      change _ = 0
      have hp : (ComplexShape.up ℕ).next p = p + 1 :=
        ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
      change (M.d p ((ComplexShape.up ℕ).next p)).hom
        ((eZ.hom.app (I.cocomplex.X p)).hom z) = 0
      rw [hp]
      exact hzc⟩
  have hc : K.iCycles p c = eX.hom.app (J.cocomplex.X p) s :=
    (K.sc p).abCyclesIso_inv_apply_iCycles _
  have hd : M.iCycles p d = eZ.hom.app (I.cocomplex.X p) z :=
    (M.sc p).abCyclesIso_inv_apply_iCycles _
  have hgen (N : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
      (w : AZ ⟶ N) :
      t.hom.app N (eX.hom.app (P.obj N) (a ≫ P.map w)) = eZ.hom.app N w := by
    let e := eqToHom (Opens.map_top f)
    have he : eX.hom.app (P.obj N) (a ≫ P.map w) =
        N.obj.map e.op (eZ.hom.app N w) := by
      change sectionsEquiv (Opens.grothendieckTopology X) ⊤ (P.obj N)
        (a ≫ P.map w) = N.obj.map e.op
          (sectionsEquiv (Opens.grothendieckTopology Z) ⊤ N w)
      rw [sectionsEquiv_apply]
      change w.hom.app (op ((Opens.map f).obj ⊤)) (a.hom.app (op ⊤) _) = _
      rw [ha ⊤ (𝟙 _)]
      let q := toSheafify (Opens.grothendieckTopology Z)
        (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ≫ w.hom
      have hq := ConcreteCategory.congr_hom (q.naturality e.op)
        (FreeAbelianGroup.of (𝟙 (⊤ : Opens Z)))
      change w.hom.app (op ((Opens.map f).obj ⊤))
        ((toSheafify (Opens.grothendieckTopology Z)
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
          (op ((Opens.map f).obj ⊤))
          (FreeAbelianGroup.of (eqToHom (Opens.map_top f)))) = _
      exact hq
    rw [he]
    change N.obj.map (eqToHom (congrArg op (Opens.map_top f)))
      (N.obj.map e.op _) = _
    have heop : e.op = (eqToIso (congrArg op (Opens.map_top f))).inv := by
      simp only [e, eqToHom_op, eqToIso.inv]
    rw [heop]
    exact Iso.inv_hom_id_apply (N.obj.mapIso
      (eqToIso (congrArg op (Opens.map_top f)))) _
  have hmap : HomologicalComplex.homologyMap (δ ≫ β) p (K.homologyπ p c) =
      M.homologyπ p d := by
    apply class_map
    rw [hc, hd]
    change t.hom.app (I.cocomplex.X p)
      ((φ.f p).hom.app (op ⊤) (eX.hom.app (J.cocomplex.X p) s)) =
        eZ.hom.app (I.cocomplex.X p) z
    have h := ConcreteCategory.congr_hom (eX.hom.naturality (φ.f p)) s
    change eX.hom.app _ (s ≫ φ.f p) =
      (φ.f p).hom.app (op ⊤) (eX.hom.app _ s) at h
    rw [← h, ← hsz]
    exact hgen _ z
  have hn := hx _ J p s hs c hc
  have hm := hy F I p z hz d hd
  have ht := I.rightDerived_app_eq t.hom p
  change (y p).hom.app F
    ((NatTrans.rightDerived t.hom p).app F
      ((I.isoRightDerivedObj (P ⋙ GX) p).inv
        (HomologicalComplex.homologyMap δ p
          ((J.isoRightDerivedObj GX p).hom
            ((x p).inv.app (P.obj F) (J.extMk s (p + 1) rfl hs)))))) = _
  rw [hn, ht]
  simp only [ConcreteCategory.comp_apply]
  have hcancel := Iso.inv_hom_id_apply (I.isoRightDerivedObj (P ⋙ GX) p)
    (HomologicalComplex.homologyMap δ p (K.homologyπ p c))
  rw [hcancel]
  set_option backward.isDefEq.respectTransparency false in
   change (y p).hom.app F
    ((I.isoRightDerivedObj GZ p).inv
      (HomologicalComplex.homologyMap β p
        (HomologicalComplex.homologyMap δ p (K.homologyπ p c)))) = _
  have hmap' : HomologicalComplex.homologyMap β p
      (HomologicalComplex.homologyMap δ p (K.homologyπ p c)) = M.homologyπ p d := by
    simpa only [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] using hmap
  rw [hmap', ← hm]
  simp only [Iso.hom_inv_id_apply]
  exact Iso.inv_hom_id_apply ((y p).app F) _

end CategoryTheory
