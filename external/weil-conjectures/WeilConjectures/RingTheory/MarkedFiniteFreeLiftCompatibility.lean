/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.Algebra.Homology.AcyclicLift
import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeCokernel
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeProperties
import WeilConjectures.AlgebraicGeometry.ComplexLiftStrictMap
import WeilConjectures.AlgebraicGeometry.ProjectiveClassReducedSplitting
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import all WeilConjectures.RingTheory.StablyFreeComplexLift

@[expose] public section
set_option autoImplicit false
universe u v w w'
open CategoryTheory
namespace DerivedCategory

open CategoryTheory.Limits CochainComplex

private theorem isIso_neg_hom {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso (-f) := by
  refine ⟨⟨-inv f, ?_, ?_⟩⟩ <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem counit_iso_on_kProjective
    {R : Type u} [CommRing R]
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory.{w'} D]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (E : ModuleCat.{max u v} R ⥤ D) [E.Additive]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory D)
    (ε : Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) [P.IsKProjective] :
    IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) := by
  classical
  let C := ModuleCat.{max u v} R
  let H := HomotopyCategory.quotient C (.up ℤ)
  let G := E.mapHomotopyCategory (.up ℤ) ⋙ (Qh : _ ⥤ DerivedCategory D)
  let S : Set (HomotopyCategory C (.up ℤ)) :=
    {X | ∃ K : CochainComplex C ℤ, K.IsKProjective ∧ H.obj K = X}
  have hres (X : HomotopyCategory C (.up ℤ)) :
      ∃ (Y : HomotopyCategory C (.up ℤ)) (s : Y ⟶ X),
        Y ∈ S ∧ HomotopyCategory.quasiIso C (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, s, hs, F, ι, step, hz, hm, hc, he, hsp, hq⟩ :=
      exists_large_filtered_free_resolution K
    refine ⟨H.obj Y, H.map s, ⟨Y, ?_, rfl⟩, ?_⟩
    · exact isKProjective_of_filtered_free Y F ι step hz hm hc he hsp hq
    · exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  have hinv (X Y : HomotopyCategory C (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ S) (hY : Y ∈ S)
      (hs : HomotopyCategory.quasiIso C (.up ℤ) s) : IsIso (G.map s) := by
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨K', hK', rfl⟩ := hY
    obtain ⟨f, rfl⟩ := H.map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hh := (IsKProjective.quasiIso_iff f).1 hf
    have : IsIso (H.map f) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences f).2 hh
    exact G.map_isIso _
  obtain ⟨_, L₀, ε₀, hL₀, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory D) G S hres hinv
  let := hL₀
  have := hcomp (H.obj P) ⟨P, inferInstance, rfl⟩
  let e := Functor.leftDerivedNatIso L₀ L ε₀ ε
    (HomotopyCategory.quasiIso C (.up ℤ)) (Iso.refl G)
  have he := Functor.leftDerivedNatTrans_app L₀ L ε₀ ε
    (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 G) (H.obj P)
  change e.hom.app (Qh.obj (H.obj P)) ≫ ε.app (H.obj P) = ε₀.app (H.obj P) ≫ 𝟙 _ at he
  rw [← isIso_comp_left_iff (e.hom.app (Qh.obj (H.obj P))), he, Category.comp_id]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cone_marking_homotopy
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    (S : ShortComplex (CochainComplex C ℤ))
    {F : CochainComplex D ℤ}
    (δ : F ⟶ (E.mapHomologicalComplex (.up ℤ)).obj S.X₁)
    (e : (E.mapHomologicalComplex (.up ℤ)).obj S.X₂ ≅ mappingCone δ)
    (eB : (E.mapHomologicalComplex (.up ℤ)).obj S.X₃ ≅ F⟦(1 : ℤ)⟧)
    (hf : (E.mapHomologicalComplex (.up ℤ)).map S.f ≫ e.hom = mappingCone.inr δ)
    (hg : (E.mapHomologicalComplex (.up ℤ)).map S.g ≫ eB.hom =
      e.hom ≫ (mappingCone.triangle δ).mor₃) :
    Nonempty (Homotopy
      ((E.mapHomologicalComplex (.up ℤ)).map (mappingCone.triangle S.f).mor₃ ≫
        ((E.mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app S.X₁)
      (-((E.mapHomologicalComplex (.up ℤ)).map (mappingCone.descShortComplex S) ≫
        eB.hom ≫ δ⟦(1 : ℤ)⟧'))) := by
  classical
  let G := E.mapHomologicalComplex (.up ℤ)
  let ec := mappingCone.mapHomologicalComplexIso S.f E
  let m := mappingCone.map (G.map S.f) (mappingCone.inr δ) (𝟙 _) e.hom
    (by simpa only [Category.id_comp] using hf)
  let u := ec.hom ≫ m
  let r := mappingCone.rotateHomotopyEquiv δ
  have hp : u ≫ r.inv = G.map (mappingCone.descShortComplex S) ≫ eB.hom := by
    rw [← mappingCone.mapHomologicalComplexIso_hom_descShortComplex E S]
    dsimp only [u]
    simp only [Category.assoc]
    congr 1
    simp only [mappingCone.descShortComplex, ShortComplex.map_f, ShortComplex.map_g]
    ext n
    apply mappingCone.ext_from (G.map S.f) (n + 1) n rfl
    · dsimp only [m, r, G, mappingCone.map, mappingCone.rotateHomotopyEquiv]
      simp only [HomologicalComplex.comp_f,
        mappingCone.inl_v_desc_f_assoc, mappingCone.inl_v_desc_f,
        HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
        HomologicalComplex.id_f, Category.id_comp,
        HomComplex.Cochain.zero_v, zero_comp]
    · dsimp only [m, r, G, mappingCone.map, mappingCone.rotateHomotopyEquiv]
      simp only [HomologicalComplex.comp_f, Category.assoc,
        mappingCone.inr_f_desc_f_assoc, mappingCone.inr_f_desc_f]
      exact (congrArg (fun k ↦ k.f n) hg).symm
  have hq : u ≫ (mappingCone.triangle (mappingCone.inr δ)).mor₃ =
      G.map (mappingCone.triangle S.f).mor₃ ≫ (G.commShiftIso 1).hom.app S.X₁ := by
    have hm := (mappingCone.triangleMap (G.map S.f) (mappingCone.inr δ)
      (𝟙 _) e.hom (by simpa only [Category.id_comp] using hf)).comm₃.symm
    change m ≫ (mappingCone.triangle (mappingCone.inr δ)).mor₃ =
      (mappingCone.triangle (G.map S.f)).mor₃ ≫ (𝟙 _)⟦(1 : ℤ)⟧' at hm
    dsimp only [mappingCone.triangle_obj₁, mappingCone.triangle_obj₃] at hm ⊢
    have hm' : m ≫ (mappingCone.triangle (mappingCone.inr δ)).mor₃ =
        (mappingCone.triangle (G.map S.f)).mor₃ := by
      have hid : (𝟙 (G.obj S.X₁))⟦(1 : ℤ)⟧' = 𝟙 _ :=
        (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (1 : ℤ)).map_id _
      exact hm.trans ((congrArg (fun a ↦
        (mappingCone.triangle (G.map S.f)).mor₃ ≫ a) hid).trans (Category.comp_id _))
    dsimp only [u]
    rw [Category.assoc, hm']
    exact (mappingCone.map_δ S.f E).symm
  have H : Homotopy (u ≫ (mappingCone.triangle (mappingCone.inr δ)).mor₃)
      ((u ≫ r.inv) ≫ r.hom ≫ (mappingCone.triangle (mappingCone.inr δ)).mor₃) := by
    simpa only [Category.assoc, Category.id_comp] using
      (((r.homotopyInvHomId.compRight
        (mappingCone.triangle (mappingCone.inr δ)).mor₃).compLeft u).symm)
  rw [hq, hp] at H
  dsimp only [r] at H
  refine ⟨?_⟩
  simpa only [Category.assoc, mappingCone.rotateHomotopyEquiv_comm₃,
    Preadditive.comp_neg, Preadditive.neg_comp] using H

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem unshift_marking
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w'} D] (E : C ⥤ D) [E.Additive]
    {X Y B : CochainComplex C ℤ} {F : CochainComplex D ℤ}
    (q : X ⟶ Y⟦(1 : ℤ)⟧) (t : X ⟶ B)
    (eB : (E.mapHomologicalComplex (.up ℤ)).obj B ≅ F⟦(1 : ℤ)⟧)
    (δ : F ⟶ (E.mapHomologicalComplex (.up ℤ)).obj Y)
    (H : Homotopy
      ((E.mapHomologicalComplex (.up ℤ)).map q ≫
        ((E.mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app Y)
      (-((E.mapHomologicalComplex (.up ℤ)).map t ≫ eB.hom ≫ δ⟦(1 : ℤ)⟧'))) :
    let G := E.mapHomologicalComplex (.up ℤ)
    let k := -(q⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).hom.app Y)
    let θ := (G.commShiftIso (-1)).app B ≪≫
      (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso eB ≪≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).app F
    Q.map (G.map k) = Q.map (G.map (t⟦(-1 : ℤ)⟧')) ≫ Q.map θ.hom ≫ Q.map δ := by
  classical
  dsimp only
  let G := E.mapHomologicalComplex (.up ℤ)
  let z := (shiftFunctorCompIsoId (CochainComplex D ℤ) (1 : ℤ) (-1 : ℤ) (by decide))
  have h := Q_map_eq_of_homotopy D
    (((H.shift (-1)).compLeft ((G.commShiftIso (-1)).hom.app X)).compRight
      (z.hom.app (G.obj Y)))
  have hleft : G.map (-(q⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).hom.app Y)) =
      -((G.commShiftIso (-1)).hom.app X ≫
        (G.map q ≫ (G.commShiftIso 1).hom.app Y)⟦(-1 : ℤ)⟧' ≫
          z.hom.app (G.obj Y)) := by
    simp only [Functor.map_neg, Functor.map_comp,
      G.map_shiftFunctorCompIsoId_hom_app, Category.assoc,
      ← Functor.commShiftIso_hom_naturality_assoc]
    rfl
  have hright :
      (G.commShiftIso (-1)).hom.app X ≫
        (G.map t ≫ eB.hom ≫ δ⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ z.hom.app (G.obj Y) =
      G.map (t⟦(-1 : ℤ)⟧') ≫
        ((G.commShiftIso (-1)).hom.app B ≫ eB.hom⟦(-1 : ℤ)⟧' ≫ z.hom.app F) ≫ δ := by
    have hz : δ⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' ≫ z.hom.app (G.obj Y) =
        z.hom.app F ≫ δ := z.hom.naturality δ
    simp only [Functor.map_comp, Category.assoc,
      ← Functor.commShiftIso_hom_naturality_assoc]
    rw [hz]
  rw [hleft]
  calc
    _ = Q.map ((G.commShiftIso (-1)).hom.app X ≫
        (G.map t ≫ eB.hom ≫ δ⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ z.hom.app (G.obj Y)) := by
      simpa only [Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp,
        neg_neg, Category.assoc] using congrArg Neg.neg h
    _ = Q.map (G.map (t⟦(-1 : ℤ)⟧') ≫
        ((G.commShiftIso (-1)).hom.app B ≫ eB.hom⟦(-1 : ℤ)⟧' ≫ z.hom.app F) ≫ δ) :=
      congrArg Q.map hright
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc, Iso.trans_hom, Functor.mapIso_hom]
      rfl

private noncomputable def complexCounit
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (E : C ⥤ D) [E.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ Qh) :
    Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ Q :=
  Functor.whiskerRight (quotientCompQhIso C).inv L ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).hom Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ)) (quotientCompQhIso D).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedVariables false in
/-- The remaining comparison step upgrades unmarked lifting data to the prescribed marking.
Source: Stacks Project, More on Algebra, Tag 0BCA, the cone-coordinate homotopy.
(auxiliary; not a blueprint node)
The universal counit is invertible on the bounded projective representative supplied by
`hdata`. Represent the inverse of the prescribed derived marking by a map from `F` to
its reduction. Lift its acyclic cone, lift the cone inclusion strictly, and take the
cokernel shifted by minus one. The projective class splitting lemma gives finite stably
free terms; their free reductions make them free, and Nakayama gives the exact bound.
Mathlib's cone rotation homotopy identifies the reduced roof with the prescribed map,
with the minus sign absorbed into the roof. Naturality of the counit proves the marking.
-/
theorem exists_marking_compatible_finiteFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F)
    (hdata : ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i))) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      L.map β.hom ≫ α.hom =
        L.map ((quotientCompQhIso (ModuleCat.{max u v} R)).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        Qh.map ((@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _
          (ModuleCat.extendScalars (Ideal.Quotient.mk I))
          (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
          (.up ℤ)).hom.app P) ≫
        (quotientCompQhIso (ModuleCat.{max u v} (R ⧸ I))).hom.app _ ≫
        Q.map θ.hom := by
  classical
  let C := ModuleCat.{max u v} R
  let D := ModuleCat.{max u v} (R ⧸ I)
  let E := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let : E.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
  let G := E.mapHomologicalComplex (.up ℤ)
  let τ := complexCounit E L ε
  obtain ⟨P₀, β₀, θ₀, hPbound, hPterms⟩ := hdata
  let := hPbound
  let := hFbound
  have hproj₀ (i : ℤ) : Projective (P₀.X i) := by
    have := (hPterms i).1
    exact (P₀.X i).projective_of_categoryTheory_projective
  let := hproj₀
  let := CochainComplex.isKProjective_of_projective P₀ b
  have hprojF (i : ℤ) : Projective (F.X i) := by
    have := (hFterms i).1
    exact (F.X i).projective_of_categoryTheory_projective
  let := hprojF
  let := CochainComplex.isKProjective_of_projective F b
  have hcounit := counit_iso_on_kProjective E L ε P₀
  have hτ : IsIso (τ.app P₀) := by
    dsimp [τ, complexCounit]
    infer_instance
  let c : L.obj (Q.obj P₀) ≅ Q.obj (G.obj P₀) := asIso (τ.app P₀)
  let a : Q.obj (G.obj P₀) ≅ Q.obj F := c.symm ≪≫ L.mapIso β₀ ≪≫ α
  obtain ⟨δ, hδ⟩ := IsKProjective.exists_Q_map_eq F (G.obj P₀) a.inv
  have : IsIso (Q.map δ) := by rw [hδ]; infer_instance
  have : QuasiIso δ := (isIso_Q_map_iff_quasiIso D δ).mp inferInstance
  let Pclass : Set C := {M | Module.Finite R M ∧ Module.IsStablyFree R M}
  have hproj (M : C) (hM : M ∈ Pclass) : Projective M := by
    have := hM.2
    have : Module.Projective R M := Module.instProjectiveOfIsStablyFree R M
    exact M.projective_of_categoryTheory_projective
  have hclosed := fun (M N T : C) (e : Nonempty (T ≅ ModuleCat.of R (M × N))) ↦
    finite_stablyFree_class_closed M N T e
  have hsurj (M N : C) (f : M ⟶ N) (_ : M ∈ Pclass) (hN : N ∈ Pclass)
      (hf : Function.Surjective (E.map f)) : Function.Surjective f := by
    have := hN.1
    exact ModuleCat.surjective_of_extendScalars_mod_ideal I hunits M N f hf
  have h₀ (i : ℤ) : P₀.X i ∈ Pclass := by
    have := (hPterms i).1
    exact ⟨(hPterms i).2, inferInstance⟩
  have hterms (i : ℤ) : ∃ M : C, M ∈ Pclass ∧ Nonempty (F.X i ≅ E.obj M) :=
    ⟨P₀.X i, h₀ i, ⟨((HomologicalComplex.eval D (.up ℤ) i).mapIso θ₀).symm⟩⟩
  obtain ⟨hCbound, hCacyclic, hCterms⟩ :=
    AlgebraicGeometry.complex_lift_cone_properties R I Pclass F P₀ hclosed
      ⟨b, hPbound⟩ h₀ ⟨b, hFbound⟩ hterms δ
  have hsummand (M N T : C) (hM : M ∈ Pclass) (hT : T ∈ Pclass)
      (e : Nonempty (T ≅ ModuleCat.of R (M × N))) : N ∈ Pclass :=
    ((hclosed M N T e).mp ⟨hM, hT⟩).2
  obtain ⟨A, hAbound, hAacyclic, hAterms, ⟨e⟩⟩ :=
    exists_acyclic_lift_mod_ideal R I (fun M ↦ M ∈ Pclass)
      hproj hsummand hsurj (mappingCone δ) hCbound hCacyclic hCterms
  obtain ⟨f, hf⟩ := AlgebraicGeometry.exists_complex_lift_strict_map R I P₀ A
    ⟨b, hPbound⟩ hproj₀ (mappingCone δ) hCacyclic e (mappingCone.inr δ)
  let T := mappingCone.triangleRotateShortComplex δ
  have hT : T.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i ↦ (mappingCone.triangleRotateShortComplexSplitting δ i).shortExact)
  let ec : cokernel T.f ≅ T.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel T.f) hT.gIsCokernel
  let em : cokernel (G.map f) ≅ cokernel T.f :=
    cokernel.mapIso (G.map f) T.f (Iso.refl _) e (by
      change G.map f ≫ e.hom = 𝟙 _ ≫ mappingCone.inr δ
      simpa only [Category.id_comp] using hf)
  let eB : G.obj (cokernel f) ≅ F⟦(1 : ℤ)⟧ :=
    PreservesCokernel.iso G f ≪≫ em ≪≫ ec
  have hg : G.map (cokernel.π f) ≫ eB.hom = e.hom ≫ T.g := by
    dsimp [eB, em, ec]
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    simp only [Category.assoc, cokernel.π_desc_assoc]
    congr 1
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel T.f) hT.gIsCokernel WalkingParallelPair.one
  let S := ShortComplex.cokernelSequence f
  have hsplit := (AlgebraicGeometry.complex_lift_cone_cokernel R I F P₀ A δ e f hf).2
  have hdegree (i : ℤ) :
      (S.map (HomologicalComplex.eval C (.up ℤ) i)).ShortExact ∧ S.X₃.X i ∈ Pclass := by
    exact AlgebraicGeometry.projective_class_reduced_splitting R I Pclass
      hproj hclosed hsurj (S.map (HomologicalComplex.eval C (.up ℤ) i))
      ((ShortComplex.cokernelSequence_exact f).map (HomologicalComplex.eval C (.up ℤ) i))
      (by exact (HomologicalComplex.eval C (.up ℤ) i).map_epi S.g)
      (h₀ i) (hAterms i) (hsplit i)
      ⟨P₀.X (i + 1), h₀ (i + 1),
        ⟨(HomologicalComplex.eval D (.up ℤ) i).mapIso eB ≪≫
          (F.shiftFunctorObjXIso 1 i (i + 1) rfl) ≪≫
          ((HomologicalComplex.eval D (.up ℤ) (i + 1)).mapIso θ₀).symm⟩⟩
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun i ↦ (hdegree i).1)
  obtain ⟨H⟩ := cone_marking_homotopy E S δ e eB hf hg
  have hzero : IsZero (Q.obj A) := by
    let : Zero (CochainComplex C ℤ) := HasZeroObject.zero' _
    have hq : QuasiIso (0 : (0 : CochainComplex C ℤ) ⟶ A) := by
      constructor
      intro i
      exact (quasiIsoAt_iff_exactAt _ i (HomologicalComplex.ExactAt.of_isZero
        ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)))).2 (hAacyclic i)
    exact (Q.map_isZero (isZero_zero _)).of_iso
      (asIso (Q.map (0 : (0 : CochainComplex C ℤ) ⟶ A))).symm
  have hconn : IsIso (triangleOfSESδ hS) :=
    ((triangleOfSES hS).isZero₂_iff_isIso₃ (triangleOfSES_distinguished hS)).1 hzero
  let q : mappingCone f ⟶ P₀⟦(1 : ℤ)⟧ := (mappingCone.triangle f).mor₃
  let t : mappingCone f ⟶ cokernel f := mappingCone.descShortComplex S
  have ht : QuasiIso t := mappingCone.quasiIso_descShortComplex hS
  have hq : IsIso (Q.map q) := by
    have hh : Q.map q ≫ (Q.commShiftIso 1).hom.app P₀ = Q.map t ≫ triangleOfSESδ hS :=
      (descShortComplex_triangleOfSESδ hS).symm
    have : IsIso (Q.map q ≫ (Q.commShiftIso 1).hom.app P₀) := by
      rw [hh]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp this
  have hq' : QuasiIso q := (isIso_Q_map_iff_quasiIso C q).mp hq
  let k : (mappingCone f)⟦(-1 : ℤ)⟧ ⟶ P₀ := -(q⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).hom.app P₀)
  let ℓ : (mappingCone f)⟦(-1 : ℤ)⟧ ⟶ (cokernel f)⟦(-1 : ℤ)⟧ := t⟦(-1 : ℤ)⟧'
  have hk : IsIso (Q.map k) := by
    have hcomp : IsIso (Q.map (q⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).hom.app P₀)) := by
      rw [Q.map_comp]
      infer_instance
    change IsIso (Q.map (-_))
    rw [Q.map_neg]
    exact isIso_neg_hom _
  have hℓ : IsIso (Q.map ℓ) := by dsimp [ℓ]; infer_instance
  let β : Q.obj (S.X₃⟦(-1 : ℤ)⟧) ≅ K :=
    (asIso (Q.map ℓ)).symm ≪≫ asIso (Q.map k) ≪≫ β₀
  let θ : G.obj (S.X₃⟦(-1 : ℤ)⟧) ≅ F :=
    (G.commShiftIso (-1)).app S.X₃ ≪≫
      (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso eB ≪≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).app F
  have hcompare : Q.map (G.map k) = Q.map (G.map ℓ) ≫ Q.map θ.hom ≫ Q.map δ :=
    unshift_marking E q t eB δ H
  have hmark₀ : (L.map β₀.hom ≫ α.hom) ≫ Q.map δ = τ.app P₀ := by
    rw [hδ]
    dsimp [a, c]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp_assoc,
      β₀.hom_inv_id, L.map_id, Category.id_comp]
  let P := S.X₃⟦(-1 : ℤ)⟧
  have hfinite (i : ℤ) : Module.Finite R (P.X i) := (hdegree (i + -1)).2.1
  have hsf (i : ℤ) : Module.IsStablyFree R (P.X i) := (hdegree (i + -1)).2.2
  have hfree (i : ℤ) : Module.Free R (P.X i) := by
    have := hfinite i
    have := hsf i
    have := (hFterms i).1
    let ei : E.obj (P.X i) ≅ F.X i := (HomologicalComplex.eval D (.up ℤ) i).mapIso θ
    have : Module.Free (R ⧸ I) (E.obj (P.X i)) :=
      Module.Free.of_equiv ei.symm.toLinearEquiv
    exact ModuleCat.free_of_free_extendScalars_mod_ideal I hunits (P.X i)
  have hbound : P.IsStrictlyLE b := by
    apply (isStrictlyLE_iff _ _).mpr
    intro i hi
    let ei : E.obj (P.X i) ≅ F.X i := (HomologicalComplex.eval D (.up ℤ) i).mapIso θ
    have hz : IsZero (E.obj (P.X i)) :=
      (F.isZero_of_isStrictlyLE b i hi).of_iso ei
    let : Zero C := HasZeroObject.zero' C
    have : Subsingleton (E.obj (P.X i)) := ModuleCat.subsingleton_of_isZero hz
    have := hfinite i
    have hred : Function.Surjective (E.map (0 : (0 : C) ⟶ P.X i)) :=
      fun y ↦ ⟨0, Subsingleton.elim _ _⟩
    have : Epi (0 : (0 : C) ⟶ P.X i) := (ModuleCat.epi_iff_surjective _).mpr
      (ModuleCat.surjective_of_extendScalars_mod_ideal I hunits 0 (P.X i) 0 hred)
    exact IsZero.of_epi_zero (0 : C) (P.X i)
  refine ⟨P, β, θ, hbound, fun i ↦ ⟨hfree i, hfinite i⟩, ?_⟩
  have hmark : L.map β.hom ≫ α.hom = τ.app P ≫ Q.map θ.hom := by
    apply (cancel_epi (L.map (Q.map ℓ))).mp
    apply (cancel_mono (Q.map δ)).mp
    have hnatk : L.map (Q.map k) ≫ τ.app P₀ =
        τ.app _ ≫ Q.map (G.map k) := τ.naturality k
    have hnatℓ : L.map (Q.map ℓ) ≫ τ.app P =
        τ.app _ ≫ Q.map (G.map ℓ) := τ.naturality ℓ
    have hil : Q.map ℓ ≫ (asIso (Q.map ℓ)).inv = 𝟙 _ :=
      (asIso (Q.map ℓ)).hom_inv_id
    calc
      _ = L.map (Q.map k) ≫ τ.app P₀ := by
        dsimp only [β, Iso.trans_hom, Iso.symm_hom, asIso_hom]
        rw [L.map_comp, L.map_comp]
        simp only [Category.assoc]
        rw [← L.map_comp_assoc, hil, L.map_id,
          Category.id_comp]
        have hm : L.map β₀.hom ≫ α.hom ≫ Q.map δ = τ.app P₀ := by
          simpa only [Category.assoc] using hmark₀
        simp only [hm]
      _ = τ.app _ ≫ Q.map (G.map k) := hnatk
      _ = τ.app _ ≫ Q.map (G.map ℓ) ≫ Q.map θ.hom ≫ Q.map δ := by
        rw [hcompare]
      _ = _ := by
        rw [← Category.assoc, ← Category.assoc, ← hnatℓ]
        simp only [Category.assoc]
  simpa [τ, complexCounit, Category.assoc] using hmark

end DerivedCategory
