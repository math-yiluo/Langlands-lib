/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.RingTheory.RingPseudoCoherent
import all Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.RingTheory.Nilpotent.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import all WeilConjectures.Algebra.Homology.SurjectiveModuleComplexTowerLimit
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.RingTheory.NilpotentMarkedFreeComplexLift
import all WeilConjectures.RingTheory.PseudoCoherentNilpotentInvariance

/-!
# Pseudo-coherent reconstruction over a tower of nilpotent quotients

Source: Stacks Project, More on Algebra, Tag 0CQF,
lemma-Rlim-pseudo-coherent-gives-pseudo-coherent
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/- The adjunction normalization below works with the given derived categories and adjunctions.
It uses the universal module scalar-extension pair, rather than a ringed-site presentation. -/
private theorem whisker_hom_app {H K : Type*} [Category* H] [Category* K]
    {T : K ⥤ H} {U : H ⥤ K} (adj : T ⊣ U)
    {J : Type*} [Category* J] (G : J ⥤ K) (B : J ⥤ H)
      (a : G ⋙ T ⟶ B) (X : J) :
      ((adj.whiskerRight J).homEquiv G B a).app X =
        adj.homEquiv (G.obj X) (B.obj X) (a.app X) := by
    simp [Adjunction.homEquiv, Adjunction.whiskerRight, whiskeringRight]
private theorem whisker_hom_symm_app {H K : Type*} [Category* H] [Category* K]
    {T : K ⥤ H} {U : H ⥤ K} (adj : T ⊣ U)
    {J : Type*} [Category* J] (G : J ⥤ K) (B : J ⥤ H)
      (a : G ⟶ B ⋙ U) (X : J) :
      (((adj.whiskerRight J).homEquiv G B).symm a).app X =
        (adj.homEquiv (G.obj X) (B.obj X)).symm (a.app X) := by
    simp [Adjunction.homEquiv, Adjunction.whiskerRight, whiskeringRight]

private theorem kan_post_rightAdjoint
    {C D H K : Type*} [Category* C] [Category* D] [Category* H] [Category* K]
    (Q : C ⥤ D) (F : C ⥤ H) (LF : D ⥤ H) (ε : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension ε] (T : K ⥤ H) (U : H ⥤ K) (adj : T ⊣ U) :
    (LF ⋙ U).IsRightKanExtension
      ((associator Q LF U).inv ≫ whiskerRight ε U) := by
  classical
  let lift (G : D ⥤ K) (β : Q ⋙ G ⟶ F ⋙ U) : G ⟶ LF ⋙ U :=
    (adj.whiskerRight D).homEquiv G LF
      (LF.liftOfIsRightKanExtension ε (G ⋙ T)
        ((associator Q G T).inv ≫ ((adj.whiskerRight C).homEquiv _ _).symm β))
  have fac (G : D ⥤ K) (β : Q ⋙ G ⟶ F ⋙ U) :
      whiskerLeft Q (lift G β) ≫
        ((associator Q LF U).inv ≫ whiskerRight ε U) = β := by
    ext X
    have h := LF.liftOfIsRightKanExtension_fac_app ε (G ⋙ T)
      ((associator Q G T).inv ≫ ((adj.whiskerRight C).homEquiv _ _).symm β) X
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_inv_app, Category.id_comp]
    change (lift G β).app (Q.obj X) ≫ U.map (ε.app X) = β.app X
    dsimp only [lift]
    rw [whisker_hom_app adj, ← adj.homEquiv_naturality_right, h]
    simp only [NatTrans.comp_app, associator_inv_app, Category.id_comp, whisker_hom_symm_app adj,
      Functor.comp_obj, Equiv.apply_symm_apply]
  constructor
  refine ⟨IsTerminal.ofUniqueHom
    (fun Z ↦ CostructuredArrow.homMk (lift Z.left Z.hom) (fac Z.left Z.hom)) ?_⟩
  intro Z m
  apply CostructuredArrow.hom_ext
  apply ((adj.whiskerRight D).homEquiv Z.left LF).symm.injective
  apply LF.hom_ext_of_isRightKanExtension ε
  ext X
  apply (adj.homEquiv (Z.left.obj (Q.obj X)) (F.obj X)).injective
  have hm := NatTrans.congr_app m.w X
  have hl := NatTrans.congr_app (fac Z.left Z.hom) X
  have hm' : m.left.app (Q.obj X) ≫ U.map (ε.app X) = Z.hom.app X := by
    simpa [Category.assoc] using hm
  have hl' : (lift Z.left Z.hom).app (Q.obj X) ≫ U.map (ε.app X) =
      Z.hom.app X := by simpa using hl
  change adj.homEquiv _ _
    ((((adj.whiskerRight D).homEquiv Z.left LF).symm m.left).app (Q.obj X) ≫ ε.app X) =
    adj.homEquiv _ _
    ((((adj.whiskerRight D).homEquiv Z.left LF).symm
      (lift Z.left Z.hom)).app (Q.obj X) ≫ ε.app X)
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right,
    whisker_hom_symm_app adj, whisker_hom_symm_app adj, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, hm', hl']

private theorem scalar_universal_normalized
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B)
    [(ModuleCat.extendScalars.{u, u, max u v} φ).Additive]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (adj : L ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory) :
    ∃ ε : DerivedCategory.Qh ⋙ L ⟶
        @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars φ)
          (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive (.up ℤ) ⋙
            DerivedCategory.Qh,
      L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
      ∀ X : HomotopyCategory (ModuleCat.{max u v} A) (.up ℤ),
        adj.unit.app (DerivedCategory.Qh.obj X) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategory.map (ε.app X) =
        DerivedCategory.Qh.map
          (((ModuleCat.extendRestrictScalarsAdj φ).mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app
            (((ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj X) := by
  classical
  let : Algebra A B := φ.toAlgebra
  let F := ModuleCat.extendScalars.{u, u, max u v} φ
  let G := ModuleCat.restrictScalars.{max u v} φ
  let : F.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  obtain ⟨LF, ε₀, hLF, _, _⟩ :=
    ModuleCat.exists_baseDerivedExtension_resolution.{u, u, v, w} A B
  let := hLF
  let : LF.IsRightKanExtension ε₀ := hLF.isRightKanExtension
  let W₁ := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ)
  let W₂ := HomotopyCategory.quasiIso (ModuleCat.{max u v} B) (.up ℤ)
  let β := G.mapDerivedCategoryFactorsh.inv
  let : G.mapDerivedCategory.IsRightDerivedFunctor β W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ G.mapDerivedCategory
      G.mapDerivedCategoryFactorsh
  let : (LF ⋙ G.mapDerivedCategory).IsLeftDerivedFunctor
      ((associator _ _ _).inv ≫ whiskerRight ε₀ G.mapDerivedCategory) W₁ :=
    ⟨kan_post_rightAdjoint _ _ LF ε₀ L G.mapDerivedCategory adj⟩
  let e : DerivedCategory.Qh ⋙ (G.mapDerivedCategory ⋙ LF) ≅
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ LF :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight G.mapDerivedCategoryFactorsh LF
  let : (G.mapDerivedCategory ⋙ LF).IsRightDerivedFunctor
      (whiskerRight β LF ≫ (associator _ _ _).hom) W₂ := by
    have := Functor.isRightDerivedFunctor_of_inverts W₂ (G.mapDerivedCategory ⋙ LF) e
    exact this
  let ah := (ModuleCat.extendRestrictScalarsAdj φ).mapHomotopyCategory (.up ℤ)
  let d := ah.derived W₁ W₂ ε₀ β
  let i := adj.leftAdjointUniq d
  let ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    whiskerLeft DerivedCategory.Qh i.hom ≫ ε₀
  refine ⟨ε, ?_, ?_⟩
  · constructor
    exact Functor.isRightKanExtension_of_iso i.symm ε₀ ε (by ext X; simp [ε])
  · intro X
    change adj.unit.app _ ≫ G.mapDerivedCategory.map (i.hom.app _ ≫ ε₀.app X) = _
    rw [G.mapDerivedCategory.map_comp, ← Category.assoc,
      Adjunction.unit_leftAdjointUniq_hom_app]
    exact ah.derivedη_fac_app W₁ ε₀ β X

private theorem scalar_chain_unit
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) [(ModuleCat.extendScalars.{u, u, max u v} φ).Additive]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (adj : L ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory) :
    ∃ ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh,
      L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
      ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
        adj.unit.app (DerivedCategory.Q.obj P) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategory.map
            (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).unit.app P)
        := by
  obtain ⟨ε, hε, hn⟩ := scalar_universal_normalized φ L adj
  refine ⟨ε, hε, ?_⟩
  intro P
  have h := hn ((HomotopyCategory.quotient _ _).obj P)
  have hr : (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) =
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change (ModuleCat.restrictScalars φ).mapDerivedCategory.map (𝟙 _) ≫ _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    simp
  have h' := congrArg (fun t ↦ t ≫
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.hom.app
      (((ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P))) h
  simp only [Category.assoc, Iso.inv_hom_id_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h'
  change adj.unit.app (DerivedCategory.Q.obj P) ≫
    (ModuleCat.restrictScalars φ).mapDerivedCategory.map
      (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      𝟙 _ at h'
  rw [hr, Category.comp_id] at h'
  exact h'

/- Transport marked lifting from A / ker(phi) to the specified quotient ring B. -/
private theorem marked_lift_surjective
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) (hs : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ))
    [(ModuleCat.extendScalars.{u, u, max u v} φ).Additive]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : DerivedCategory.IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} B) ℤ)
    (b : ℤ) (hb : F.IsStrictlyLE b)
    (hf : ∀ i, Module.Free B (F.X i) ∧ Module.Finite B (F.X i))
    (α : L.obj K ≅ DerivedCategory.Q.obj F) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
      (β : DerivedCategory.Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧ (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      L.map β.hom ≫ α.hom =
        ε.app ((HomotopyCategory.quotient _ _).obj P) ≫ DerivedCategory.Q.map θ.hom := by
  classical
  let I := RingHom.ker φ
  let e := RingHom.quotientKerEquivOfSurjective hs
  let H := ModuleCat.restrictScalars.{max u v} e.toRingHom
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (A ⧸ I))
  let D := H.mapDerivedCategory
  let G := ModuleCat.extendScalars.{u, u, max u v} φ
  let G₀ := ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)
  have : G₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
  let c : (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ D ≅
      G₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    associator _ _ _ ≪≫ isoWhiskerLeft _ H.mapDerivedCategoryFactorsh ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (quotient_scalar_iso φ hs) (.up ℤ)) _
  let η := (associator DerivedCategory.Qh L D).inv ≫ whiskerRight ε D
  let ε₀ := η ≫ c.hom
  have hKan : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
  have hKan₀ := kan_postcompose_equivalence DerivedCategory.Qh _ D L ε
  have : (L ⋙ D).IsLeftDerivedFunctor ε₀
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) := by
    constructor
    exact (Functor.isRightKanExtension_iff_of_iso₂ η ε₀ c (Iso.refl _) (by
      simp [ε₀])).1 hKan₀
  let F₀ := (H.mapHomologicalComplex (.up ℤ)).obj F
  have hF₀ : ∀ i, Module.Free (A ⧸ I) (F₀.X i) ∧ Module.Finite (A ⧸ I) (F₀.X i) := by
    intro i
    have := (hf i).1
    have := (hf i).2
    let : Module (A ⧸ I) (F.X i) := (F₀.X i).isModule
    let bF := Module.Free.chooseBasis B (F.X i)
    let b₀ : Module.Basis (Module.Free.ChooseBasisIndex B (F.X i)) (A ⧸ I) (F₀.X i) :=
      bF.mapCoeffs e.symm (by intro a x; change e (e.symm a) • x = a • x; simp)
    exact ⟨Module.Free.of_basis b₀, Module.Finite.of_basis b₀⟩
  have hunits (x : I) : IsUnit (1 + (x : A)) := by
    apply IsNilpotent.isUnit_one_add
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have hx := Ideal.pow_mem_pow x.property n
    rw [hn] at hx
    simpa using hx
  obtain ⟨P, β, θ₀, hPb, hP, hmark⟩ :=
    DerivedCategory.exists_marked_finiteFree_lift_of_nilpotent I
      (by obtain ⟨n, hn⟩ := hn; exact ⟨n + 1, by omega, by
            rw [pow_succ, hn, zero_mul]⟩)
      hunits (L ⋙ D) ε₀ K hK F₀ b
      ((CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff F H b).2 hb) hF₀
      (D.mapIso α ≪≫ H.mapDerivedCategoryFactors.app F)
  let cc := Functor.mapHomologicalComplexCompIso (quotient_scalar_iso φ hs) (.up ℤ)
  let θ : (G.mapHomologicalComplex (.up ℤ)).obj P ≅ F :=
    (H.mapHomologicalComplex (.up ℤ)).preimageIso (cc.app P ≪≫ θ₀)
  refine ⟨P, β, θ, hPb, hP, ?_⟩
  have hc : c.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (cc.hom.app P) := by
    dsimp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      associator_hom_app, associator_inv_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app]
    simp only [Category.id_comp]
    change H.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (cc.hom.app P)) = _
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change (D.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ _ = _
    erw [D.map_id, DerivedCategory.Qh.map_id]
    simp only [Category.id_comp, Category.comp_id]
    have h := DerivedCategory.quotientCompQhIso_hom_naturality (cc.hom.app P)
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
    exact congrArg (fun f ↦ _ ≫ f) (by
      simpa only [Category.id_comp, Category.comp_id] using h)
  have hθ : (H.mapHomologicalComplex (.up ℤ)).map θ.hom =
      cc.hom.app P ≫ θ₀.hom := by
    exact (H.mapHomologicalComplex (.up ℤ)).map_preimage _
  apply D.map_injective
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app F)).1
  have hnat : D.map (DerivedCategory.Q.map θ.hom) ≫
      H.mapDerivedCategoryFactors.hom.app F =
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map θ.hom) :=
    H.mapDerivedCategoryFactors.hom.naturality θ.hom
  simp only [D.map_comp, Category.assoc]
  rw [hnat, hθ, DerivedCategory.Q.map_comp]
  dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom] at hmark
  have hleft : D.map (L.map
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).inv.app P)) = 𝟙 _ := by
    change D.map (L.map (𝟙 _)) = _
    simp
  have hright : DerivedCategory.Qh.map
      ((G₀.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} (A ⧸ I))).hom.app _ =
      𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
    simp
  have hmark' : D.map (L.map β.hom) ≫ D.map α.hom ≫
      H.mapDerivedCategoryFactors.hom.app F =
      D.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        c.hom.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Q.map θ₀.hom := by
    have hm := hmark
    have hr := hright
    change DerivedCategory.Qh.map
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomotopyCategoryFactors
          (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} (A ⧸ I))).hom.app _ =
        𝟙 _ at hr
    rw [← Category.assoc (DerivedCategory.Qh.map
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app P)) _ (DerivedCategory.Q.map θ₀.hom), hr] at hm
    dsimp only [ε₀, η, NatTrans.comp_app, associator_inv_app,
      whiskerRight_app] at hm
    rw [hleft] at hm
    erw [Category.id_comp, Category.id_comp, Category.id_comp] at hm
    simpa only [Functor.comp_obj, F₀, Iso.app_hom, Category.assoc] using hm
  rw [hc] at hmark'
  simpa only [Category.assoc] using hmark'

private theorem scalar_unit_surjective
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hs : Function.Surjective φ) (P : ModuleCat.{max u v} A) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj φ).unit.app P) := by
  let : Algebra A B := φ.toAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b p =>
    obtain ⟨a, rfl⟩ := hs b
    refine ⟨a • p, ?_⟩
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    change (1 : B) ⊗ₜ[A] (a • p) = (algebraMap A B a) ⊗ₜ[A] p
    rw [TensorProduct.tmul_smul]
    exact congrArg (fun b : B ↦ b ⊗ₜ[A] p) ((Algebra.smul_def a (1 : B)).trans (mul_one _))
  | add x y hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ _ _⟩

private theorem scalar_chain_transpose
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) [(ModuleCat.extendScalars.{u, u, max u v} φ).Additive]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (adj : L ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
        adj.unit.app (DerivedCategory.Q.obj P) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategory.map
            (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).unit.app P))
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : CochainComplex (ModuleCat.{max u v} B) ℤ)
    (θ : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ F) :
    adj.homEquiv _ _
      (ε.app ((HomotopyCategory.quotient _ _).obj P) ≫ DerivedCategory.Q.map θ) =
    DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).homEquiv P F θ) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app F := by
  let G := ModuleCat.restrictScalars φ
  let ac := (ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app F)).1
  change (adj.unit.app (DerivedCategory.Q.obj P) ≫
    G.mapDerivedCategory.map (ε.app _ ≫ DerivedCategory.Q.map θ)) ≫
      G.mapDerivedCategoryFactors.hom.app F =
    (DerivedCategory.Q.map (ac.homEquiv P F θ) ≫
      G.mapDerivedCategoryFactors.inv.app F) ≫ G.mapDerivedCategoryFactors.hom.app F
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
  have hn : G.mapDerivedCategory.map (DerivedCategory.Q.map θ) ≫
      G.mapDerivedCategoryFactors.hom.app F =
      G.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map θ) :=
    G.mapDerivedCategoryFactors.hom.naturality θ
  calc
    _ = (adj.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map (ε.app _) ≫
        G.mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map θ) := by
      rw [hn]
      simp only [Category.assoc]
    _ = DerivedCategory.Q.map (ac.unit.app P) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map θ) :=
      congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map θ)) (hε P)
    _ = _ := by
      change DerivedCategory.Q.map (ac.unit.app P) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map θ) =
          DerivedCategory.Q.map (ac.unit.app P ≫
            (G.mapHomologicalComplex (.up ℤ)).map θ) ≫ 𝟙 _
      exact (DerivedCategory.Q.map_comp _ _).symm.trans (Category.comp_id _).symm

private theorem reconstruction_step
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) (hs : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ))
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (adj : L ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (E : DerivedCategory (ModuleCat.{max u v} B))
    (t : K ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj E)
    (ht : IsIso ((adj.homEquiv K E).symm t))
    (hK : DerivedCategory.IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} B) ℤ) (b : ℤ)
    (hb : F.IsStrictlyLE b)
    (hf : ∀ i, Module.Free B (F.X i) ∧ Module.Finite B (F.X i))
    (βF : DerivedCategory.Q.obj F ≅ E) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
      (β : DerivedCategory.Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ≅ F)
      (a : P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj F),
      P.IsStrictlyLE b ∧ (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ i, Function.Surjective (a.f i)) ∧
      (∀ i, (ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ (θ.hom.f i) = a.f i) ∧
      DerivedCategory.Q.map a = β.hom ≫ t ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map βF.inv ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app F := by
  have : (ModuleCat.extendScalars.{u, u, max u v} φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  obtain ⟨ε, hε, hu⟩ := scalar_chain_unit φ L adj
  let := hε
  let α := asIso ((adj.homEquiv K E).symm t) ≪≫ βF.symm
  obtain ⟨P, β, θ, hPb, hPf, hm⟩ := marked_lift_surjective φ hs hn L ε K hK F b hb hf α
  let ac := (ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)
  let a := ac.homEquiv P F θ.hom
  refine ⟨P, β, θ, a, hPb, hPf, ?_, ?_, ?_⟩
  · intro i
    change Function.Surjective (fun x ↦ (θ.hom.f i)
      ((ModuleCat.extendRestrictScalarsAdj φ).unit.app (P.X i) x))
    exact ((ModuleCat.epi_iff_surjective (θ.hom.f i)).1 inferInstance).comp
      (scalar_unit_surjective φ hs (P.X i))
  · intro i
    rfl
  · have ha := scalar_chain_transpose φ L adj ε hu P F θ.hom
    have hα : adj.homEquiv K (DerivedCategory.Q.obj F) α.hom =
        t ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map βF.inv := by
      dsimp [α]
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have he : β.hom ≫ t ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map βF.inv =
        DerivedCategory.Q.map a ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app F := by
      calc
        _ = adj.homEquiv _ _ (L.map β.hom ≫ α.hom) := by
          rw [adj.homEquiv_naturality_left, hα]
        _ = _ := by
          erw [hm]
          exact ha
    have he' := congrArg (fun f ↦ f ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app F) he
    have hEnd : (DerivedCategory.Q.map a ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app F) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app F =
        DerivedCategory.Q.map a := by
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
    simpa only [Category.assoc] using hEnd.symm.trans he'.symm

/- Choose the initial bounded finite-free model and lift it recursively with its marking. -/
private theorem compatible_complex_tower
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hs : ∀ n, Function.Surjective (φ n))
    (hn : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adj : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (E : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, E (n + 1) ⟶ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (E n))
    (ht : ∀ n, IsIso (((adj n).homEquiv (E (n + 1)) (E n)).symm (t n)))
    (hpc : DerivedCategory.IsPseudoCoherent (E 0)) :
    ∃ (P : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (β : ∀ n, DerivedCategory.Q.obj (P n) ≅ E n)
      (a : ∀ n, P (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (P n))
      (θ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (P (n + 1)) ≅ P n),
      (∀ n, (P n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((P n).X i) ∧ Module.Finite (R n) ((P n).X i)) ∧
      (∀ n i, Function.Surjective ((a n).f i)) ∧
      (∀ n i, (ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv _ _
        ((θ n).hom.f i) = (a n).f i) ∧
      (∀ n, DerivedCategory.Q.map (a n) = (β (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (β n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (P n)) := by
  classical
  have hp (n : ℕ) : DerivedCategory.IsPseudoCoherent (E n) := by
    induction n with
    | zero => exact hpc
    | succ n ih =>
      have : (ModuleCat.extendScalars.{u, u, max u v} (φ n)).Additive :=
        (ModuleCat.extendRestrictScalarsAdj (φ n)).left_adjoint_additive
      obtain ⟨ε, hε, _⟩ := scalar_chain_unit (φ n) (L n) (adj n)
      let := hε
      apply (DerivedCategory.isPseudoCoherent_iff_of_surjective_nilpotent_kernel
        (φ n) (hs n) (hn n) (L n) ε (E (n + 1))).mp
      obtain ⟨F, b, hb, hf, ⟨β⟩⟩ := ih
      exact ⟨F, b, hb, hf, ⟨β ≪≫ (asIso (((adj n).homEquiv _ _).symm (t n))).symm⟩⟩
  obtain ⟨F, b, hb, hf, ⟨β₀⟩⟩ := hpc
  let D (n : ℕ) :=
    Σ P : CochainComplex (ModuleCat.{max u v} (R n)) ℤ,
      {β : DerivedCategory.Q.obj P ≅ E n // P.IsStrictlyLE b ∧
        ∀ i, Module.Free (R n) (P.X i) ∧ Module.Finite (R n) (P.X i)}
  let d₀ : D 0 := ⟨F, β₀, hb, hf⟩
  have step (n : ℕ) (d : D n) :=
    reconstruction_step (φ n) (hs n) (hn n) (L n) (adj n) (E (n + 1)) (E n)
      (t n) (ht n) (hp (n + 1)) d.1 b d.2.property.1 d.2.property.2 d.2.val
  let next (n : ℕ) (d : D n) : D (n + 1) :=
    ⟨(step n d).choose, (step n d).choose_spec.choose,
      (step n d).choose_spec.choose_spec.choose_spec.choose_spec.1,
      (step n d).choose_spec.choose_spec.choose_spec.choose_spec.2.1⟩
  let d : ∀ n, D n := fun n ↦ Nat.rec d₀ next n
  let θ (n : ℕ) := (step n (d n)).choose_spec.choose_spec.choose
  let a (n : ℕ) := (step n (d n)).choose_spec.choose_spec.choose_spec.choose
  refine ⟨(fun n ↦ (d n).1), b, (fun n ↦ (d n).2.val), a, θ,
    (fun n ↦ (d n).2.property.1), (fun n ↦ (d n).2.property.2), ?_, ?_, ?_⟩
  · intro n
    exact (step n (d n)).choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
  · intro n
    exact (step n (d n)).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
  · intro n
    exact (step n (d n)).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2

/- Nilpotent Nakayama, followed by the Orzech property, controls lifted finite bases. -/
private theorem surjective_of_nilpotent_scalarExtension
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hs : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ))
    (P Q : ModuleCat.{max u v} A) (f : P ⟶ Q)
    (hf : Function.Surjective ((ModuleCat.extendScalars φ).map f)) :
    Function.Surjective f := by
  let H := ModuleCat.restrictScalars.{max u v}
    (RingHom.quotientKerEquivOfSurjective hs).toRingHom
  let c := quotient_scalar_iso φ hs
  have : Epi ((ModuleCat.extendScalars φ).map f) := (ModuleCat.epi_iff_surjective _).2 hf
  have h : Epi ((ModuleCat.extendScalars (Ideal.Quotient.mk (RingHom.ker φ))).map f) := by
    have he : (ModuleCat.extendScalars (Ideal.Quotient.mk (RingHom.ker φ))).map f =
        c.inv.app P ≫ H.map ((ModuleCat.extendScalars φ).map f) ≫ c.hom.app Q := by
      simpa [c, H] using (c.hom.naturality f |> congrArg (fun g ↦ c.inv.app P ≫ g)).symm
    rw [he]
    infer_instance
  exact surjective_of_extendScalars_nilpotent (RingHom.ker φ) hn P Q f
    ((ModuleCat.epi_iff_surjective _).1 h)

private theorem bijective_of_nilpotent_scalarExtension
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hs : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ))
    (P Q : ModuleCat.{max u v} A) [Module.Finite A P] [Module.Projective A Q]
    (f : P ⟶ Q) [IsIso ((ModuleCat.extendScalars φ).map f)] : Function.Bijective f := by
  let F := ModuleCat.extendScalars.{u, u, max u v} φ
  have hfs : Function.Surjective f := surjective_of_nilpotent_scalarExtension φ hs hn P Q f
    ((ModuleCat.epi_iff_surjective (F.map f)).1 inferInstance)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f.hom LinearMap.id hfs
  let g' : Q ⟶ P := ModuleCat.ofHom g
  have hgf : g' ≫ f = 𝟙 Q := by ext x; exact DFunLike.congr_fun hg x
  have hFg : F.map g' ≫ F.map f = 𝟙 _ := by rw [← F.map_comp, hgf, F.map_id]
  have hfg : F.map (f ≫ g') = 𝟙 _ := by
    rw [F.map_comp]
    apply (cancel_mono (F.map f)).1
    simp only [Category.assoc, hFg, Category.comp_id, Category.id_comp]
  have hfgs : Function.Surjective (f ≫ g') :=
    surjective_of_nilpotent_scalarExtension φ hs hn P P (f ≫ g')
      (by rw [hfg]; exact Function.surjective_id)
  have hi := OrzechProperty.injective_of_surjective_endomorphism (g.comp f.hom) hfgs
  exact ⟨fun x y h ↦ hi (congrArg g h), hfs⟩

private theorem lift_basis
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hs : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ))
    (P : ModuleCat.{max u v} A) [Module.Free A P] [Module.Finite A P]
    (Q : ModuleCat.{max u v} B)
    (θ : (ModuleCat.extendScalars φ).obj P ≅ Q)
    (a : P ⟶ (ModuleCat.restrictScalars φ).obj Q)
    (ha : (ModuleCat.extendRestrictScalarsAdj φ).homEquiv P Q θ.hom = a)
    (has : Function.Surjective a)
    {ι : Type (max u v)} [Finite ι] (b : Module.Basis ι B Q) :
    ∃ c : Module.Basis ι A P, ∀ j, a (c j) = b j := by
  classical
  let := Fintype.ofFinite ι
  let : Algebra A B := φ.toAlgebra
  let V := ModuleCat.of A (ι → A)
  let e := Pi.basisFun A ι
  let x : ι → P := fun j ↦ (has (b j)).choose
  have hx (j : ι) : a (x j) = b j := (has (b j)).choose_spec
  let f : V ⟶ P := ModuleCat.ofHom (e.constr A x)
  let eb := e.baseChange B
  let g := b.repr.symm.toLinearMap.comp eb.repr.toLinearMap
  have hfg : ((ModuleCat.extendScalars φ).map f) ≫ θ.hom = ModuleCat.ofHom g := by
    apply ModuleCat.hom_ext
    apply eb.ext
    intro j
    change θ.hom ((LinearMap.baseChange B (e.constr A x)) (eb j)) = g (eb j)
    simp only [eb, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      Module.Basis.constr_basis]
    have hh := ConcreteCategory.congr_hom ha (x j)
    change θ.hom ((1 : B) ⊗ₜ[A] x j) = _ at hh
    rw [hh, hx]
    rw [← Module.Basis.baseChange_apply]
    change b j = b.repr.symm (eb.repr (eb j))
    rw [eb.repr_self]
    simpa only [one_smul] using (b.repr_symm_single j (1 : B)).symm
  have hg : IsIso (ModuleCat.ofHom g) := by
    let eg := eb.repr ≪≫ₗ b.repr.symm
    exact eg.toModuleIso.isIso_hom
  have hfi : IsIso ((ModuleCat.extendScalars φ).map f) := by
    have : IsIso (((ModuleCat.extendScalars φ).map f) ≫ θ.hom) := by
      rw [hfg]
      exact hg
    exact IsIso.of_isIso_comp_right _ θ.hom
  have hbij := bijective_of_nilpotent_scalarExtension φ hs hn V P f
  let c := e.map (LinearEquiv.ofBijective f.hom hbij)
  refine ⟨c, ?_⟩
  intro j
  change a (f (e j)) = b j
  change a ((e.constr A x) (e j)) = b j
  rw [Module.Basis.constr_basis]
  exact hx j

private theorem compatible_bases
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hs : ∀ n, Function.Surjective (φ n))
    (hn : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (P : ∀ n, ModuleCat.{max u v} (R n))
    (hp : ∀ n, Module.Free (R n) (P n) ∧ Module.Finite (R n) (P n))
    (θ : ∀ n, (ModuleCat.extendScalars (φ n)).obj (P (n + 1)) ≅ P n)
    (a : ∀ n, P (n + 1) ⟶ (ModuleCat.restrictScalars (φ n)).obj (P n))
    (ha : ∀ n, (ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv _ _ (θ n).hom = a n)
    (has : ∀ n, Function.Surjective (a n)) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι)
      (b : ∀ n, Module.Basis ι (R n) (P n)), ∀ n j, a n (b (n + 1) j) = b n j := by
  classical
  have := (hp 0).1
  have := (hp 0).2
  let ι := Module.Free.ChooseBasisIndex (R 0) (P 0)
  let b₀ := Module.Free.chooseBasis (R 0) (P 0)
  let next (n : ℕ) (b : Module.Basis ι (R n) (P n)) := by
    have := (hp (n + 1)).1
    have := (hp (n + 1)).2
    exact (lift_basis (φ n) (hs n) (hn n) (P (n + 1)) (P n)
      (θ n) (a n) (ha n) (has n) b).choose
  let b : ∀ n, Module.Basis ι (R n) (P n) :=
    fun n ↦ Nat.rec (motive := fun n ↦ Module.Basis ι (R n) (P n)) b₀ next n
  refine ⟨ι, inferInstance, b, ?_⟩
  intro n j
  have := (hp (n + 1)).1
  have := (hp (n + 1)).2
  exact (lift_basis (φ n) (hs n) (hn n) (P (n + 1)) (P n)
    (θ n) (a n) (ha n) (has n) (b n)).choose_spec j

private theorem transpose_isIso_of_bases
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : ModuleCat.{max u v} A) (Q : ModuleCat.{max u v} B)
    (a : P ⟶ (ModuleCat.restrictScalars φ).obj Q)
    {ι : Type (max u v)} (c : Module.Basis ι A P) (b : Module.Basis ι B Q)
    (h : ∀ j, a (c j) = b j) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv P Q).symm a) := by
  let : Algebra A B := φ.toAlgebra
  let cb := c.baseChange B
  let e := cb.repr ≪≫ₗ b.repr.symm
  have he : ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv P Q).symm a =
      ModuleCat.ofHom e.toLinearMap := by
    apply ModuleCat.hom_ext
    apply cb.ext
    intro j
    rw [Module.Basis.baseChange_apply]
    have heq := ConcreteCategory.congr_hom
      ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv P Q |>.apply_symm_apply a) (c j)
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at heq
    erw [heq]
    rw [h]
    rw [← Module.Basis.baseChange_apply]
    change b j = b.repr.symm (cb.repr (cb j))
    rw [cb.repr_self]
    simpa only [one_smul] using (b.repr_symm_single j (1 : B)).symm
  rw [he]
  exact e.toModuleIso.isIso_hom

/- The limit object is constructed as compatible tuples; only its basis is chosen later. -/
private def compatibleSubmodule
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (V : ∀ n, ModuleCat.{max u v} (R n))
    (a : ∀ n, V (n + 1) ⟶ (ModuleCat.restrictScalars (φ n)).obj (V n)) :
    Submodule A (∀ n, (ModuleCat.restrictScalars (q n)).obj (V n)) where
  carrier := {x | ∀ n, a n (x (n + 1)) = x n}
  zero_mem' := by intro n; exact map_zero _
  add_mem' := by
    intro x y hx hy n
    exact ((a n).hom.map_add _ _).trans (congrArg₂ (· + ·) (hx n) (hy n))
  smul_mem' := by
    intro c x hx n
    change a n ((q (n + 1) c) • x (n + 1)) = (q n c) • x n
    have h := (a n).hom.map_smul (q (n + 1) c) (x (n + 1))
    change a n ((q (n + 1) c) • x (n + 1)) =
      (φ n (q (n + 1) c)) • a n (x (n + 1)) at h
    rw [h, hx]
    exact congrArg (fun r : R n ↦ r • (x n : V n)) (RingHom.congr_fun (hq n) c).symm

private theorem basis_transition_coords
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : ModuleCat.{max u v} A) (Q : ModuleCat.{max u v} B)
    (a : P ⟶ (ModuleCat.restrictScalars φ).obj Q)
    {ι : Type (max u v)} [Finite ι]
    (c : Module.Basis ι A P) (b : Module.Basis ι B Q)
    (h : ∀ j, a (c j) = b j) (x : P) (j : ι) :
    b.equivFun (a x) j = φ (c.equivFun x j) := by
  classical
  let := Fintype.ofFinite ι
  conv_lhs => rw [← c.sum_equivFun x]
  simp only [_root_.map_sum]
  have hs (k : ι) : a (c.equivFun x k • c k) = φ (c.equivFun x k) • b k := by
    exact ((a.hom).map_smul _ _).trans (congrArg (φ (c.equivFun x k) • ·) (h k))
  simp only [hs, _root_.map_smul]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self]
  simp

/- Use the universal property of the inverse-limit ring separately on each basis coordinate. -/
private theorem compatible_module_free
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! z : A, ∀ n, q n z = x n)
    (V : ∀ n, ModuleCat.{max u v} (R n))
    (a : ∀ n, V (n + 1) ⟶ (ModuleCat.restrictScalars (φ n)).obj (V n))
    {ι : Type (max u v)} [Finite ι]
    (b : ∀ n, Module.Basis ι (R n) (V n))
    (hb : ∀ n j, a n (b (n + 1) j) = b n j) :
    ∃ c : Module.Basis ι A (compatibleSubmodule R φ A q hq V a),
      ∀ n j, (c j).val n = b n j := by
  classical
  let := Fintype.ofFinite ι
  let S := compatibleSubmodule R φ A q hq V a
  have sep (x y : A) (h : ∀ n, q n x = q n y) : x = y := by
    have hcompat (n : ℕ) : φ n (q (n + 1) y) = q n y := by
      exact (RingHom.congr_fun (hq n) y).symm
    obtain ⟨z, hz, hu⟩ := hlim (fun n ↦ q n y) hcompat
    exact (hu x h).trans (hu y (fun n ↦ rfl)).symm
  let f : (ι → A) →ₗ[A] S :=
    { toFun := fun x ↦ ⟨fun n ↦ (b n).equivFun.symm (fun j ↦ q n (x j)), by
        intro n
        apply (b n).equivFun.injective
        funext j
        rw [basis_transition_coords (φ n) (V (n + 1)) (V n) (a n)
          (b (n + 1)) (b n) (hb n), LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
        exact (RingHom.congr_fun (hq n) (x j)).symm⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext n
        apply (b n).equivFun.injective
        change (b n).equivFun ((b n).equivFun.symm (fun j ↦ q n (x j + y j))) =
          (b n).equivFun ((b n).equivFun.symm (fun j ↦ q n (x j)) +
            (b n).equivFun.symm (fun j ↦ q n (y j)))
        simp only [_root_.map_add, LinearEquiv.apply_symm_apply]
        funext j
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        funext n
        apply (b n).equivFun.injective
        change (b n).equivFun ((b n).equivFun.symm (fun j ↦ q n (c * x j))) =
          (b n).equivFun ((q n c) • (b n).equivFun.symm (fun j ↦ q n (x j)))
        rw [LinearEquiv.apply_symm_apply, _root_.map_smul, LinearEquiv.apply_symm_apply]
        funext j
        exact map_mul (q n) _ _ }
  have hi : Function.Injective f := by
    intro x y h
    funext j
    apply sep
    intro n
    have h' := congrArg (fun z : S ↦ (b n).equivFun (z.val n) j) h
    simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] using h'
  have hs : Function.Surjective f := by
    intro x
    have hc (j : ι) (n : ℕ) :
        φ n ((b (n + 1)).equivFun (x.val (n + 1)) j) = (b n).equivFun (x.val n) j := by
      rw [← basis_transition_coords (φ n) (V (n + 1)) (V n) (a n)
        (b (n + 1)) (b n) (hb n), x.property n]
    let y : ι → A := fun j ↦ (hlim (fun n ↦ (b n).equivFun (x.val n) j) (hc j)).choose
    refine ⟨y, Subtype.ext ?_⟩
    funext n
    apply (b n).equivFun.injective
    funext j
    dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk]
    rw [LinearEquiv.apply_symm_apply]
    exact (hlim _ (hc j)).choose_spec.1 n
  let e := LinearEquiv.ofBijective f ⟨hi, hs⟩
  let c := (Pi.basisFun A ι).map e
  refine ⟨c, ?_⟩
  intro n j
  have hc : (c j).val n =
      (b n).equivFun.symm (fun k ↦ q n ((Pi.basisFun A ι) j k)) := rfl
  rw [hc]
  apply (b n).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext k
  by_cases h : j = k
  · subst k; simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h]

/- Differentials and projections are coordinatewise, so the limit complex is explicit. -/
private noncomputable def compatibleComplex
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (P : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
    (a : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (P n)) :
    CochainComplex (ModuleCat.{max u v} A) ℤ where
  X i := ModuleCat.of A (compatibleSubmodule R φ A q hq (fun n ↦ (P n).X i)
    (fun n ↦ (a n).f i))
  d i j := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨fun n ↦ (P n).d i j (x.val n), by
        intro n
        have h := ConcreteCategory.congr_hom ((a n).comm i j).symm (x.val (n + 1))
        change (a n).f j ((P (n + 1)).d i j (x.val (n + 1))) =
          (P n).d i j ((a n).f i (x.val (n + 1))) at h
        exact h.trans (congrArg ((P n).d i j) (x.property n))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext n
        exact ((P n).d i j).hom.map_add _ _
      map_smul' := by
        intro c x
        apply Subtype.ext
        funext n
        exact ((P n).d i j).hom.map_smul (q n c) _ }
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact ConcreteCategory.congr_hom ((P n).shape i j h) (x.val n)
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact ConcreteCategory.congr_hom ((P n).d_comp_d i j k) (x.val n)

private noncomputable def compatibleProjection
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (P : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
    (a : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (P n))
    (n : ℕ) : compatibleComplex R φ A q hq P a ⟶
      ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (P n) where
  f i := ModuleCat.ofHom
    (X := (compatibleComplex R φ A q hq P a).X i)
    (Y := (ModuleCat.restrictScalars (q n)).obj ((P n).X i))
    { toFun := fun x ↦ (x.val n :
        (ModuleCat.restrictScalars (q n)).obj ((P n).X i))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  comm' _ _ _ := rfl

private noncomputable def compatibleComplex_isLimit
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (P : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
    (a : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (P n)) :
    let T := Functor.ofOpSequence (fun n ↦
      ((ModuleCat.restrictScalars (q (n + 1))).mapHomologicalComplex (.up ℤ)).map (a n) ≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
        (.up ℤ)).inv.app (P n))
    IsLimit (Cone.mk (F := T) (compatibleComplex R φ A q hq P a)
      (NatTrans.ofOpSequence (compatibleProjection R φ A q hq P a)
        (by
          intro n
          ext i : 2
          apply LinearMap.ext
          intro x
          dsimp only [Functor.const_obj_map]
          rw [Functor.ofOpSequence_map_homOfLE_succ]
          exact (x.property n).symm))) := by
  dsimp only
  refine HomologicalComplex.isLimitOfEval _ _ (fun i ↦ ?_)
  refine ⟨fun s ↦ ModuleCat.ofHom
    { toFun := fun x ↦ ⟨fun n ↦ s.π.app (Opposite.op n) x, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }, ?_, ?_⟩
  · intro n
    have h := ConcreteCategory.congr_hom (s.w (homOfLE n.le_succ).op) x
    simp only [Functor.comp_map, HomologicalComplex.eval_map,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h
  · intro x y
    apply Subtype.ext
    funext n
    exact (s.π.app (Opposite.op n)).hom.map_add _ _
  · intro c x
    apply Subtype.ext
    funext n
    exact (s.π.app (Opposite.op n)).hom.map_smul _ _
  · intro s j
    rfl
  · intro s m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact ConcreteCategory.congr_hom (hm (Opposite.op n)) x

private theorem compatibleComplex_properties
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hs : ∀ n, Function.Surjective (φ n))
    (hn : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! z : A, ∀ n, q n z = x n)
    (P : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
    (a : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (P n))
    (θ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
      (P (n + 1)) ≅ P n)
    (b : ℤ) (hbound : ∀ n, (P n).IsStrictlyLE b)
    (hfree : ∀ n i, Module.Free (R n) ((P n).X i) ∧ Module.Finite (R n) ((P n).X i))
    (has : ∀ n i, Function.Surjective ((a n).f i))
    (ha : ∀ n i, (ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv _ _
      ((θ n).hom.f i) = (a n).f i) :
    let C := compatibleComplex R φ A q hq P a
    let p := compatibleProjection R φ A q hq P a
    C.IsStrictlyLE b ∧ (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      ∀ n, IsIso
        ((((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex (.up ℤ)).homEquiv
          C (P n)).symm (p n)) := by
  classical
  dsimp only
  constructor
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun x y ↦ Subtype.ext (funext fun n ↦ ?_)⟩
    have h := (P n).isZero_of_isStrictlyLE b i hi
    have := ModuleCat.isZero_iff_subsingleton.mp h
    exact @Subsingleton.elim ((P n).X i) _ _ _
  · have hbases (i : ℤ) := compatible_bases R φ hs hn (fun n ↦ (P n).X i)
        (fun n ↦ hfree n i)
        (fun n ↦ (HomologicalComplex.eval _ _ i).mapIso (θ n))
        (fun n ↦ (a n).f i) (fun n ↦ ha n i) (fun n ↦ has n i)
    have hcb (i : ℤ) : ∃ (ι : Type (max u v)) (_ : Fintype ι)
        (c : Module.Basis ι A ((compatibleComplex R φ A q hq P a).X i))
        (b : ∀ n, Module.Basis ι (R n) ((P n).X i)),
          ∀ n j, (c j).val n = b n j := by
      obtain ⟨ι, hι, b, hb⟩ := hbases i
      let := hι
      obtain ⟨c, hc⟩ := compatible_module_free R φ A q hq hlim
        (fun n ↦ (P n).X i) (fun n ↦ (a n).f i) b hb
      exact ⟨ι, hι, c, b, hc⟩
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨ι, hι, c, b, hc⟩ := hcb i
      let := hι
      exact ⟨Module.Free.of_basis c, Module.Finite.of_basis c⟩
    · intro n
      have hi (i : ℤ) : IsIso
          (((((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex (.up ℤ)).homEquiv
            (compatibleComplex R φ A q hq P a) (P n)).symm
              (compatibleProjection R φ A q hq P a n)).f i) := by
        obtain ⟨ι, hι, c, b, hc⟩ := hcb i
        let := hι
        exact transpose_isIso_of_bases (q n)
          ((compatibleComplex R φ A q hq P a).X i) ((P n).X i)
          ((compatibleProjection R φ A q hq P a n).f i) c (b n) (hc n)
      exact HomologicalComplex.Hom.isIso_of_components _

namespace ModuleCat
/- Reuse the kernel/one-minus-shift argument from SurjectiveModuleComplexTowerLimit,
with an arbitrary supplied derived-category universe instead of its standard universe. -/
private theorem surjective_tower_triangle
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ht : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((T.map (homOfLE n.le_succ).op).f i))
    (c : Cone T) (hc : IsLimit c)
    [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (Opposite.op n)))] :
    ∃ δ, IsDerivedLimitTriangle
      (fun n ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op))
      (DerivedCategory.Q.obj c.pt)
      (Pi.lift (fun n ↦ DerivedCategory.Q.map (c.π.app (Opposite.op n)))) δ := by
  classical
  let L := c
  let K := fun n : ℕ ↦ T.obj (Opposite.op n)
  let B : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hB : IsLimit B := productIsProduct K
  let s : B.pt ⟶ B.pt := towerProductShift
    (fun n ↦ T.map (homOfLE n.le_succ).op)
  have hs (n : ℕ) : s ≫ B.proj n =
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := Pi.lift_comp_π _ _
  have hT (n : ℕ) (i : ℤ) : Epi ((T.map (homOfLE n.le_succ).op).f i) :=
    (ModuleCat.epi_iff_surjective _).2 (ht n i)
  let S := ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hB s hs L)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hB s hs
    hc
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
      rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      exact epi_one_sub (F := T ⋙ HomologicalComplex.eval _ _ i)
        (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hB) (s.f i)
        (fun n ↦ (HomologicalComplex.comp_f _ _ i).symm.trans
          ((congrArg (fun φ ↦ φ.f i) (hs n)).trans (HomologicalComplex.comp_f _ _ i)))
        (fun n ↦ hT n i)
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  have : CountableAB4Star (ModuleCat.{max u v} A) := module_countableAB4Star A
  obtain ⟨hD, hQ, _⟩ := derivedCategory_countableProducts_core (ModuleCat.{max u v} A)
  have hQB : IsLimit (DerivedCategory.Q.mapCone B) := (hQ ℕ K).some
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K B) hQB
  let : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (K n)) := inferInstance
  let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op)
  let p : DerivedCategory.Q.obj L.pt ⟶ ∏ᶜ K₀ :=
    Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (L.π.app (Opposite.op n)))
  let E : DerivedCategory.Q.obj B.pt ≅ ∏ᶜ K₀ :=
    hQFan.conePointUniqueUpToIso (productIsProduct K₀)
  have hE (n : ℕ) : E.hom ≫ Pi.π K₀ n = DerivedCategory.Q.map (B.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct K₀) ⟨n⟩
  have hπ (n : ℕ) : p ≫ Pi.π K₀ n =
      DerivedCategory.Q.map (L.π.app (Opposite.op n)) := Pi.lift_comp_π _ _
  have hi : DerivedCategory.Q.map S.f ≫ E.hom = p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hπ]
    exact congrArg DerivedCategory.Q.map (hB.fac _ ⟨n⟩)
  have hu (n : ℕ) : S.g ≫ B.proj n = B.proj n -
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := by
    change (𝟙 B.pt - s) ≫ B.proj n = _
    rw [Preadditive.sub_comp, Category.id_comp, hs]
  have htrans : DerivedCategory.Q.map S.g ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism f₀ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hu, Functor.map_sub]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, hE, f₀]
    rw [Functor.map_comp, ← Category.assoc, hE]
  let δ := DerivedCategory.triangleOfSESδ hS
  refine ⟨E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g) δ)
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) (E.inv ≫ δ))
      (Iso.refl _) E E (by simpa using hi) htrans (by simp))).mp
    (DerivedCategory.triangleOfSES_distinguished hS)

end ModuleCat

/- Compare the two one-minus-shift triangles using the product of the marked isomorphisms. -/
private theorem compare_derived_limits
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K K' : ℕ → C} [HasProduct K] [HasProduct K']
    (f : ∀ n, K (n + 1) ⟶ K n) (f' : ∀ n, K' (n + 1) ⟶ K' n)
    (e : ∀ n, K n ≅ K' n)
    (he : ∀ n, (e (n + 1)).hom ≫ f' n = f n ≫ (e n).hom)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hL : IsDerivedLimitTriangle f L p δ)
    (E : C) (pE : E ⟶ ∏ᶜ K') (δE : ∏ᶜ K' ⟶ E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle f' E pE δE) :
    ∃ β : L ≅ E, ∀ n, p ≫ Pi.π K n ≫ (e n).hom = β.hom ≫ pE ≫ Pi.π K' n := by
  let v : ∏ᶜ K ≅ ∏ᶜ K' :=
    { hom := Limits.Pi.map (fun n ↦ (e n).hom)
      inv := Limits.Pi.map (fun n ↦ (e n).inv)
      hom_inv_id := by ext n; simp
      inv_hom_id := by ext n; simp }
  have hv : towerTransitionEndomorphism f ≫ v.hom =
      v.hom ≫ towerTransitionEndomorphism f' :=
    (towerTransitionEndomorphism_natural_backward f f' (fun n ↦ (e n).hom) he).symm
  let T := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ
  let T' := Pretriangulated.Triangle.mk pE (towerTransitionEndomorphism f') δE
  obtain ⟨a, ha, ha'⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    T T' hL hE v.hom v.hom hv
  have hi : IsIso a := Pretriangulated.isIso₁_of_isIso₂₃
    (Pretriangulated.Triangle.homMk T T' a v.hom v.hom ha hv ha') hL hE
      v.isIso_hom v.isIso_hom
  refine ⟨asIso a, ?_⟩
  intro n
  have h := congrArg (fun g ↦ g ≫ Pi.π K' n) ha
  simpa [v, T, T', Category.assoc] using h

namespace DerivedCategory

section ReconstructionHelpers

variable
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{max u v} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ)
include hχ in
omit [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))] in
private theorem reconstruction_transition_compatible
    (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
    (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
    (uₙ : ∀ n, Pₙ (n + 1) ⟶
      ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
    (hmₙ : ∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n))
    (n : ℕ) :
    (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.inv.app
        (Pₙ (n + 1)) ≫
      (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (βₙ (n + 1)).hom ≫
      (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
      (χ n).inv.app (Eₙ n) =
    Q.map
      (((ModuleCat.restrictScalars (q (n + 1))).mapHomologicalComplex (.up ℤ)).map (uₙ n) ≫
        (NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).inv.app (Pₙ n)) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom := by
  let F := ModuleCat.restrictScalars (φ n)
  let G := ModuleCat.restrictScalars (q (n + 1))
  let H := ModuleCat.restrictScalars (q n)
  let ν := (NatIso.mapHomologicalComplex
    (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
    (.up ℤ)).app (Pₙ n)
  let j := (χ n).app (Q.obj (Pₙ n)) ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app (Pₙ n)) ≪≫
    G.mapDerivedCategoryFactors.app
      ((F.mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
  let k := H.mapDerivedCategoryFactors.app (Pₙ n) ≪≫ Q.mapIso ν
  have hjk : j = k := Iso.ext (hχ n (Pₙ n))
  have hc := congrArg Iso.inv hjk
  dsimp only [j, k, Iso.trans_inv, Functor.mapIso_inv] at hc
  have hm : (βₙ (n + 1)).hom ≫ t n = Q.map (uₙ n) ≫
      F.mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
        F.mapDerivedCategory.map (βₙ n).hom := by
    rw [hmₙ n]
    dsimp only [F]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map_comp,
      Iso.inv_hom_id]
    erw [(ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map_id, Category.comp_id]
  rw [← Category.assoc (G.mapDerivedCategory.map (βₙ (n + 1)).hom)
    (G.mapDerivedCategory.map (t n)) _]
  erw [← G.mapDerivedCategory.map_comp, hm]
  simp only [Functor.map_comp, Category.assoc]
  erw [(χ n).inv.naturality (βₙ n).hom]
  have hnG := G.mapDerivedCategoryFactors.inv.naturality (uₙ n)
  dsimp only [Functor.comp_map] at hnG
  erw [reassoc_of% hnG.symm]
  simp only [Category.assoc, Iso.app_inv] at hc
  erw [reassoc_of% hc]
  simp only [ν, Iso.app_inv]
  dsimp only [G, H]

include R φ hsurj hnil A q hq hlim L adjφ M adjq χ hχ Eₙ t hred hpc E pE δ hE

/-- The compatible finite-free models and all chain-level compatibility clauses.
Source: Stacks Project, More on Algebra, Tag 0CQF.
(auxiliary; not a blueprint node).

Proof plan: inductively apply marked finite-free lifting across each nilpotent quotient, preserving
one common upper cutoff and the transition marking. Lift compatible bases degree by degree, so
all terms become coordinatewise finite free and every transition is coordinate reduction. Form
the termwise inverse-limit complex and use the surjective tower limit theorem to identify its
localized object and projections with the supplied derived limit. Finally apply bounded-flat
K-flatness, derived change of rings, and the normalized coefficient adjunction to establish the
projection and transition comparison equations.
-/
theorem reconstruction_models :
    ∃ (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (β : Q.obj P ≅ E)
      (p : ∀ n, P ⟶
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θ : ∀ n, ((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P ≅ Pₙ n)
      (η : ∀ n, P ⟶ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P))
      (γ : ∀ n, (M n).obj (Q.obj P) ≅
        Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P)),
      (∀ n, (Pₙ n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧ Module.Finite (R n) ((Pₙ n).X i)) ∧
      (∀ n i, Function.Surjective ((uₙ n).f i)) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i)) = (uₙ n).f i) ∧
      (∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n)) ∧
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y) ∧
      (∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n) ∧
      (∀ n, Q.map (p n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
        β.hom ≫ pE ≫ Pi.π _ n) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i) ((θ n).hom.f i)) = (p n).f i) ∧
      (∀ n i, (η n).f i = (ModuleCat.extendRestrictScalarsAdj (q n)).unit.app (P.X i)) ∧
      (∀ n, (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (η n)) ∧
      (∀ n, (γ n).hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
        (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
  classical
  obtain ⟨Pₙ, b, βₙ, uₙ, θₙ, hbₙ, hfₙ, hsₙ, haₙ, hmₙ⟩ :=
    compatible_complex_tower R φ hsurj hnil L adjφ Eₙ t hred hpc
  let P := compatibleComplex R φ A q hq Pₙ uₙ
  let p := compatibleProjection R φ A q hq Pₙ uₙ
  obtain ⟨hb, hf, hθ⟩ := compatibleComplex_properties R φ hsurj hnil A q hq hlim
    Pₙ uₙ θₙ b hbₙ hfₙ hsₙ haₙ
  let θ (n : ℕ) := asIso
    ((((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex (.up ℤ)).homEquiv
      P (Pₙ n)).symm (p n))
  have hβ : ∃ β : Q.obj P ≅ E, ∀ n, Q.map (p n) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
      β.hom ≫ pE ≫ Pi.π _ n := by
    let T := Functor.ofOpSequence (fun n ↦
      ((ModuleCat.restrictScalars (q (n + 1))).mapHomologicalComplex (.up ℤ)).map (uₙ n) ≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
        (.up ℤ)).inv.app (Pₙ n))
    let c : Cone T := Cone.mk P (NatTrans.ofOpSequence p (by
      intro n
      ext i : 2
      apply LinearMap.ext
      intro x
      dsimp only [Functor.const_obj_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (x.property n).symm))
    have hc : IsLimit c := compatibleComplex_isLimit R φ A q hq Pₙ uₙ
    have hT (n : ℕ) (i : ℤ) : Function.Surjective
        ((T.map (homOfLE n.le_succ).op).f i) := by
      dsimp only [T]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact hsₙ n i
    have : CountableAB4Star (ModuleCat.{max u v} A) := ModuleCat.module_countableAB4Star A
    obtain ⟨hD, _, _⟩ := derivedCategory_countableProducts_core.{0} (ModuleCat.{max u v} A)
    have : HasProduct (fun n : ℕ ↦ Q.obj (T.obj (Opposite.op n))) := by
      let := hD
      infer_instance
    obtain ⟨δP, hδP⟩ := ModuleCat.surjective_tower_triangle A T hT c hc
    let e (n : ℕ) : Q.obj (T.obj (Opposite.op n)) ≅
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n) :=
      ((ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.app (Pₙ n)).symm ≪≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.mapIso (βₙ n)
    have he (n : ℕ) : (e (n + 1)).hom ≫
        ((ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
          (χ n).inv.app (Eₙ n)) = Q.map (T.map (homOfLE n.le_succ).op) ≫ (e n).hom := by
      dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      dsimp only [T]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      simpa only [Category.assoc, Iso.app_inv] using
        reconstruction_transition_compatible R φ A q hq χ hχ Eₙ t Pₙ βₙ uₙ hmₙ n
    obtain ⟨β, hβ⟩ := compare_derived_limits
      (fun n ↦ Q.map (T.map (homOfLE n.le_succ).op))
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) e he (Q.obj P) _ δP hδP E pE δ hE
    refine ⟨β, ?_⟩
    intro n
    simpa only [Pi.lift_comp_π_assoc, e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, c, NatTrans.ofOpSequence_app, Iso.app_inv] using hβ n
  obtain ⟨β, hβ⟩ := hβ
  have hscalar (n : ℕ) : ∃ γ : (M n).obj (Q.obj P) ≅
      Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P),
      (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map γ.hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex
          (.up ℤ)).unit.app P) ∧
      (γ.hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
        (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
    have : (ModuleCat.extendScalars.{u, u, max u v} (q n)).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (q n)).left_adjoint_additive
    obtain ⟨ε, hε, hu⟩ := scalar_chain_unit (q n) (M n) (adjq n)
    let := hε
    have hi := counit_isIso_of_boundedAbove_free (q n) (M n) ε P b hb
      (fun i ↦ (hf i).1)
    let γ : (M n).obj (Q.obj P) ≅
        Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) :=
      asIso (ε.app ((HomotopyCategory.quotient _ _).obj P))
    refine ⟨γ, hu P, ?_⟩
    apply ((adjq n).homEquiv _ _).injective
    rw [(adjq n).homEquiv_naturality_left, Equiv.apply_symm_apply]
    have htr := scalar_chain_transpose (q n) (M n) (adjq n) ε hu P (Pₙ n) (θ n).hom
    have ht : (((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex
        (.up ℤ)).homEquiv P (Pₙ n)) (θ n).hom = p n :=
      Equiv.apply_symm_apply _ _
    rw [ht] at htr
    rw [show γ.hom = ε.app ((HomotopyCategory.quotient _ _).obj P) from rfl,
      ← Category.assoc, (adjq n).homEquiv_naturality_right]
    erw [htr]
    simpa only [Category.assoc] using hβ n
  choose γ hγ hlast using hscalar
  let η (n : ℕ) := ((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex
    (.up ℤ)).unit.app P
  refine ⟨Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ,
    hbₙ, hfₙ, hsₙ, haₙ, hmₙ, hb, hf, ?_, ?_, hβ, ?_, ?_, hγ, hlast⟩
  · intro n i y
    exact y.property n
  · intro i x hx
    refine ⟨⟨x, hx⟩, fun n ↦ rfl, ?_⟩
    intro y hy
    exact Subtype.ext (funext hy)
  · intro n i
    have h := congrArg (fun f ↦ f.f i)
      ((((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex
        (.up ℤ)).homEquiv P (Pₙ n)).apply_symm_apply (p n))
    exact h
  · intro n i
    rfl

end ReconstructionHelpers

end DerivedCategory
