/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingSourceModelFactors
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement

/-! # Left-route normalization of the source-shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
This computes the left composite on K-injective Hom models.
(blueprint: lem-pod-reindexing-source-left-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses

set_option allowUnsafeReducibility true in
attribute [local reducible] homComplex CochainComplex.shiftFunctor

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

@[reassoc]
private theorem map_pair_comp {D : Type*} [Category D] (H : Dᵒᵖ × D ⥤ D)
    {A B C U V W : D} (f : B ⟶ A) (f' : C ⟶ B) (g : U ⟶ V) (g' : V ⟶ W) :
    H.map (Prod.mkHom f.op g) ≫ H.map (Prod.mkHom f'.op g') =
      H.map (Prod.mkHom (f' ≫ f).op (g ≫ g')) := by
  rw [← H.map_comp]
  rfl

private theorem map_pair_id {D : Type*} [Category D] (H : Dᵒᵖ × D ⥤ D)
    (A B : D) : H.map (Prod.mkHom (𝟙 A).op (𝟙 B)) = 𝟙 _ := by
  exact H.map_id (op A, B)

private theorem source_shift_normalization_inv {D : Type*} [Category D] (G : D ⥤ D)
    {A B C T U : D} (e : A ≅ B) (S : G.obj T ≅ U) (q : A ⟶ G.obj C)
    (x : C ⟶ T) (y : T ⟶ C) (k : B ⟶ U) (hxy : x ≫ y = 𝟙 C)
    (h : q ≫ G.map x ≫ S.hom = e.hom ≫ k) :
    k ≫ S.inv ≫ G.map y = e.inv ≫ q := by
  have h' := congrArg (fun z ↦ e.inv ≫ z ≫ S.inv ≫ G.map y) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    ← G.map_comp, hxy, G.map_id, Category.comp_id] using h'.symm

private theorem source_model_tail {D : Type*} [Category D] (G : D ⥤ D)
    (H : Dᵒᵖ × D ⥤ D) {A B L M R J K O₀ O₁ O₂ : D}
    (eI : J ≅ K) (d : B ⟶ A) (t : R ⟶ B) (p : L ⟶ M)
    (u : O₀ ⟶ H.obj (op A, K)) (v : O₁ ⟶ H.obj (op B, K))
    (k : H.obj (op L, K) ⟶ O₂) (q : O₀ ⟶ O₁)
    (sK : H.obj (op R, K) ⟶ G.obj (H.obj (op M, K)))
    (sJ : H.obj (op R, J) ⟶ G.obj (H.obj (op M, J))) (z : O₁ ⟶ G.obj O₂)
    (hm : u ≫ H.map (Prod.mkHom d.op (𝟙 K)) = q ≫ v)
    (ht : H.map (Prod.mkHom (𝟙 R).op eI.inv) ≫ sJ =
      sK ≫ G.map (H.map (Prod.mkHom (𝟙 M).op eI.inv)))
    (hn : v ≫ H.map (Prod.mkHom t.op (𝟙 K)) ≫ sK ≫
      G.map (H.map (Prod.mkHom p.op (𝟙 K)) ≫ k) = z) :
    u ≫ H.map (Prod.mkHom (t ≫ d).op eI.inv) ≫ sJ ≫
      G.map (H.map (Prod.mkHom p.op eI.hom) ≫ k) = q ≫ z := by
  have hsplit : H.map (Prod.mkHom (t ≫ d).op eI.inv) =
      H.map (Prod.mkHom d.op (𝟙 K)) ≫ H.map (Prod.mkHom t.op (𝟙 K)) ≫
        H.map (Prod.mkHom (𝟙 R).op eI.inv) := by
    simp only [map_pair_comp, Category.id_comp]
  have hout : H.map (Prod.mkHom (𝟙 M).op eI.inv) ≫
      H.map (Prod.mkHom p.op eI.hom) ≫ k = H.map (Prod.mkHom p.op (𝟙 K)) ≫ k := by
    rw [map_pair_comp_assoc, Category.comp_id, eI.inv_hom_id]
  rw [hsplit]
  simp only [Category.assoc]
  rw [reassoc_of% hm, reassoc_of% ht, ← G.map_comp, hout, hn]

private theorem source_model_naturality {D : Type*} [Category D] (H : Dᵒᵖ × D ⥤ D)
    {A B C U V W P P' P'' I J T R : D} (e : A ≅ B) (i : A ⟶ C)
    (c : C ⟶ H.obj (op P', I)) (c₀ : A ⟶ H.obj (op P, I))
    (u : B ⟶ U) (v : U ⟶ V) (k : V ⟶ H.obj (op W, J))
    (f : P ⟶ W) (j : J ⟶ I) (r : P' ⟶ P) (t : P'' ⟶ P')
    (s : H.obj (op P'', I) ⟶ T) (o : T ⟶ R) (z : V ⟶ R)
    (hnat : i ≫ c = c₀ ≫ H.map (Prod.mkHom r.op (𝟙 I)))
    (hmodel : c₀ = e.hom ≫ u ≫ v ≫ k ≫ H.map (Prod.mkHom f.op j))
    (htail : k ≫ H.map (Prod.mkHom (t ≫ r ≫ f).op j) ≫ s ≫ o = z) :
    e.inv ≫ i ≫ c ≫ H.map (Prod.mkHom t.op (𝟙 I)) ≫ s ≫ o = u ≫ v ≫ z := by
  rw [reassoc_of% hnat, hmodel]
  simp only [Category.assoc, e.inv_hom_id_assoc, map_pair_comp_assoc, Category.comp_id]
  rw [htail]

private theorem model_inv (W : Scheme.{u})
    [EssentiallySmall.{u + 1} W.ProEt] (s : Option ℕ)
    (P I : K l E W s) [I.IsKInjective] :
    (podReindexingHomModel l E W s P I).inv =
      @ringedSiteOrdinaryHomComparison.{u + 1, u, u, u + 2} _ _
        (ProEt.topology W) _ _ (podReindexingRing l E W s)
        (HasDerivedCategory.standard.{u + 1, u + 2} _) P I := by
  simp only [podReindexingHomModel,
    ringedSiteOrdinaryHomComparison, ringedSiteHomComplexMap, op_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

attribute [local irreducible] podReindexingHomModel podReindexingCoefficient
  Padic Padic.coefficientExtensionIntegers

-- The explicit model transports require many dependent functor-map equalities.
/-- The left route of the source-shift square on localized Hom models.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.

Proof:

1. Write F for the derived reindexing, K for its complex functor, Q for localization, alpha for
sourceModelInput, beta for sourceModelOutput, and kappa for the recorded Hom model. Alpha is F of
kappa_(P[a],I)^(-1) followed by the Hom map of Q shift(a)^(-1) in the opposite source. Naturality
of c.derived along that source map reduces its component at ((QP)[a],QI) to its component at
(Q(P[a]),QI).

2. Apply Comparison.derived_model at (P[a],I). Cancel F(kappa_(P[a],I)^(-1)) against its
F(kappa_(P[a],I)) factor. The composite now starts with the localization factor at Hom(P[a],I),
followed by Q(c.chain(P[a],I)), then the target ordinary-to-derived Hom model and its
localization-factor transports.

3. Apply LeftNormalization on X to source F(QP), representative KP, and representative isomorphism
(localizationFactors(P)).symm. Use uniqueness of LeftFormula to identify its chain reindexing with
the given eX. Invert the normalization equation. Naturality in the target moves
localizationFactors(I) through sourceShift.inv. Naturality of the ordinary Hom comparison in the
source moves the map of (complexShift(a)).inv through the Hom model.

4. The shift compatibility of localizationFactors(P) identifies F(Q shift(a)) followed by F
shift(a) with localization of complexShift(a) followed by Q shift(a). Cancel the resulting inverse
pairs and beta. What remains, in order, is localizationFactors(Hom(P[a],I)), Q of c.chain(P[a],I)
followed by Hom((complexShift(a)).inv,id) followed by eX.inv, and Q shift(-a) at Hom(KP,KI). This
is the asserted left normal form.

This calculates one route, independently of the chain square and of the other route.
(blueprint: lem-pod-reindexing-source-left-normalization) -/
theorem source_left_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (a : ℤ)
    [I.IsKInjective] [CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I)]
    (eX : (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I))⟦-a⟧ ≅
      hom l E X s (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧)
        ((podReindexingComplexFunctor l E g s).obj I))
    (hX : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology X) (podReindexingRing l E X s)
      ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) a eX) :
    (sourceModelInput l E g s P I a).hom ≫
      (c.derived.hom.app (op (((podReindexingQ l E Y s).obj P)⟦a⟧), ((podReindexingQ l E Y s).obj
          I)) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app
          ((podReindexingQ l E Y s).obj P)).op
          (𝟙 ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj I)))) ≫
      (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj P)) a).inv.app
          ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj I))) ≫
      (sourceModelOutput l E g s P I a).hom =
    (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s (P⟦a⟧) I) ≫
      (podReindexingQ l E X s).map
        ((c.chain (P⟦a⟧) I).hom ≫
          ((podReindexingHom l E X s).map
            ((complexShift l E g s a).inv.app P).op).app
              ((podReindexingComplexFunctor l E g s).obj I) ≫ eX.inv) ≫
      ((podReindexingQ l E X s).commShiftIso (-a)).hom.app
        (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I)) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let F := podReindexingDerivedFunctor l E g s
  let Q := podReindexingQ l E X s
  let KY := podReindexingComplexFunctor l E g s
  let H := podReindexingDerivedHom l E X s
  let f := podReindexingDerivedFactors l E g s
  let KP := KY.obj P
  let KI := KY.obj I
  let M := F.obj ((podReindexingQ l E Y s).obj P)
  let S := CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s) M a
  have hn := (CategoryTheory.RingedHomUniverses.leftShift_existsUnique.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s)).exists.choose_spec
    M KP KI (f.app P).symm a
  obtain ⟨e, he, hn⟩ := hn
  have heq : e = eX :=
    CategoryTheory.RingedHomUniverses.leftFormula_unique
      (ProEt.topology X) (podReindexingRing l E X s) KP KI a e eX he hX
  subst e
  rw [← model_inv l E X s KP KI, ← model_inv l E X s (KP⟦a⟧) KI] at hn
  change (Q.commShiftIso (-a)).hom.app (hom l E X s KP KI) ≫
      ((podReindexingHomModel l E X s KP KI).inv ≫
        H.map (Prod.mkHom (f.hom.app P).op (𝟙 (Q.obj KI))))⟦-a⟧' ≫
        S.hom.app (Q.obj KI) =
      Q.map eX.hom ≫ (podReindexingHomModel l E X s (KP⟦a⟧) KI).inv ≫
        H.map (Prod.mkHom ((f.hom.app P)⟦a⟧' ≫
          (Q.commShiftIso a).inv.app KP).op (𝟙 (Q.obj KI))) at hn
  have hc : (podReindexingHomModel l E X s KP KI).inv ≫
      H.map (Prod.mkHom (f.hom.app P).op (𝟙 (Q.obj KI))) ≫
      H.map (Prod.mkHom (f.inv.app P).op (𝟙 (Q.obj KI))) ≫
      (podReindexingHomModel l E X s KP KI).hom = 𝟙 _ := by
    simp only [map_pair_comp_assoc, Iso.inv_hom_id_app, Category.comp_id, map_pair_id]
    erw [Category.id_comp]
    exact (podReindexingHomModel l E X s KP KI).inv_hom_id
  have hn' := (source_shift_normalization_inv (shiftFunctor _ (-a)) (Q.mapIso eX)
    (S.app (Q.obj KI)) ((Q.commShiftIso (-a)).hom.app (hom l E X s KP KI))
    ((podReindexingHomModel l E X s KP KI).inv ≫
      H.map (Prod.mkHom (f.hom.app P).op (𝟙 (Q.obj KI))))
    (H.map (Prod.mkHom (f.inv.app P).op (𝟙 (Q.obj KI))) ≫
      (podReindexingHomModel l E X s KP KI).hom)
    ((podReindexingHomModel l E X s (KP⟦a⟧) KI).inv ≫
      H.map (Prod.mkHom ((f.hom.app P)⟦a⟧' ≫
        (Q.commShiftIso a).inv.app KP).op (𝟙 (Q.obj KI))))
    (by simpa only [Category.assoc] using hc) hn).symm
  have hs := NatTrans.shift_app_comm f.hom a P
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hs
  change F.map (((podReindexingQ l E Y s).commShiftIso a).hom.app P) ≫
      (F.commShiftIso a).hom.app ((podReindexingQ l E Y s).obj P) ≫
      (f.hom.app P)⟦a⟧' =
    f.hom.app (P⟦a⟧) ≫ Q.map ((complexShift l E g s a).hom.app P) ≫
      (Q.commShiftIso a).hom.app KP at hs
  have hs' : (F.commShiftIso a).inv.app ((podReindexingQ l E Y s).obj P) ≫
      F.map (((podReindexingQ l E Y s).commShiftIso a).inv.app P) ≫
      f.hom.app (P⟦a⟧) =
    (f.hom.app P)⟦a⟧' ≫ (Q.commShiftIso a).inv.app KP ≫
      Q.map ((complexShift l E g s a).inv.app P) := by
    apply (cancel_mono (Q.map ((complexShift l E g s a).hom.app P) ≫
      (Q.commShiftIso a).hom.app KP)).mp
    simp only [Category.assoc]
    rw [← hs]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id_app,
      ← Q.map_comp_assoc]
    erw [Q.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
    erw [F.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  have hnmap := (CategoryTheory.RingedHomUniverses.ordinaryComparison.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s)).naturality
      (Prod.mkHom (((complexShift l E g s a).inv.app P).op) (𝟙 KI))
  have hm : (podReindexingHomModel l E X s (KY.obj (P⟦a⟧)) KI).inv ≫
      H.map (Prod.mkHom (Q.map ((complexShift l E g s a).inv.app P)).op
        (𝟙 (Q.obj KI))) =
    Q.map (((podReindexingHom l E X s).map
      ((complexShift l E g s a).inv.app P).op).app KI) ≫
      (podReindexingHomModel l E X s (KP⟦a⟧) KI).inv := by
    rw [model_inv, model_inv]
    simpa only [CategoryTheory.RingedHomUniverses.ordinaryComparison_app,
      CategoryTheory.RingedHomUniverses.ordinaryBifunctor, Functor.comp_map,
      Functor.comp_obj, Functor.prod_map, Functor.op_map, Quiver.Hom.unop_op,
      H, Q, KY, KP, KI, podReindexingQ, podReindexingHom, podReindexingDerivedHom,
      homComplex,
      Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id]
      using hnmap.symm
  have ht := S.inv.naturality (f.inv.app I)
  change H.map (Prod.mkHom (𝟙 (M⟦a⟧)).op (f.inv.app I)) ≫
      S.inv.app (F.obj ((podReindexingQ l E Y s).obj I)) =
    S.inv.app (Q.obj KI) ≫
      (H.map (Prod.mkHom (𝟙 M).op (f.inv.app I)))⟦-a⟧' at ht
  have htail : (podReindexingHomModel l E X s (KY.obj (P⟦a⟧)) KI).inv ≫
      H.map (Prod.mkHom
        ((F.commShiftIso a).inv.app ((podReindexingQ l E Y s).obj P) ≫
          F.map (((podReindexingQ l E Y s).commShiftIso a).inv.app P) ≫
          f.hom.app (P⟦a⟧)).op (f.inv.app I)) ≫
      S.inv.app (F.obj ((podReindexingQ l E Y s).obj I)) ≫
      (sourceModelOutput l E g s P I a).hom =
    Q.map (((podReindexingHom l E X s).map
      ((complexShift l E g s a).inv.app P).op).app KI) ≫
      Q.map eX.inv ≫ (Q.commShiftIso (-a)).hom.app (hom l E X s KP KI) := by
    rw [hs']
    simpa only [Category.assoc, sourceModelOutput, Functor.mapIso_hom, Iso.trans_hom,
      Iso.prod_hom, Iso.op_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv] using
      source_model_tail (D := podReindexingDerived l E X s) (shiftFunctor _ (-a)) H
      (K := Q.obj KI) (L := Q.obj KP) (M := M) (R := M⟦a⟧) (f.app I)
      (Q.map ((complexShift l E g s a).inv.app P))
      ((f.hom.app P)⟦a⟧' ≫ (Q.commShiftIso a).inv.app KP) (f.inv.app P)
      (podReindexingHomModel l E X s (KY.obj (P⟦a⟧)) KI).inv
      (podReindexingHomModel l E X s (KP⟦a⟧) KI).inv
      (podReindexingHomModel l E X s KP KI).hom
      (Q.map (((podReindexingHom l E X s).map
        ((complexShift l E g s a).inv.app P).op).app KI))
      (S.inv.app (Q.obj KI)) (S.inv.app (F.obj ((podReindexingQ l E Y s).obj I)))
      (Q.map eX.inv ≫ (Q.commShiftIso (-a)).hom.app (hom l E X s KP KI)) hm ht
      (by simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv] using hn'.symm)
  have hnat := c.derived.hom.naturality
    (Prod.mkHom (((podReindexingQ l E Y s).commShiftIso a).inv.app P).op
      (𝟙 ((podReindexingQ l E Y s).obj I)))
  have hmodel := (c.derived_model (P⟦a⟧) I inferInstance).choose_spec
  change F.map ((podReindexingDerivedHom l E Y s).map
      (Prod.mkHom (((podReindexingQ l E Y s).commShiftIso a).inv.app P).op
        (𝟙 ((podReindexingQ l E Y s).obj I)))) ≫
      c.derived.hom.app (op (((podReindexingQ l E Y s).obj P)⟦a⟧),
        (podReindexingQ l E Y s).obj I) =
    c.derived.hom.app (op ((podReindexingQ l E Y s).obj (P⟦a⟧)),
      (podReindexingQ l E Y s).obj I) ≫
      H.map (Prod.mkHom (F.map
        (((podReindexingQ l E Y s).commShiftIso a).inv.app P)).op
        (F.map (𝟙 ((podReindexingQ l E Y s).obj I)))) at hnat
  simp only [F.map_id] at hnat
  have hcalc := source_model_naturality H
    (F.mapIso (podReindexingHomModel l E Y s (P⟦a⟧) I))
    (F.map ((podReindexingDerivedHom l E Y s).map
      (Prod.mkHom (((podReindexingQ l E Y s).commShiftIso a).inv.app P).op
        (𝟙 ((podReindexingQ l E Y s).obj I)))))
    (c.derived.hom.app (op (((podReindexingQ l E Y s).obj P)⟦a⟧),
      (podReindexingQ l E Y s).obj I))
    (c.derived.hom.app (op ((podReindexingQ l E Y s).obj (P⟦a⟧)),
      (podReindexingQ l E Y s).obj I))
    (f.hom.app (hom l E Y s (P⟦a⟧) I)) (Q.map (c.chain (P⟦a⟧) I).hom)
    (podReindexingHomModel l E X s (KY.obj (P⟦a⟧)) KI).inv
    (f.hom.app (P⟦a⟧)) (f.inv.app I)
    (F.map (((podReindexingQ l E Y s).commShiftIso a).inv.app P))
    ((F.commShiftIso a).inv.app ((podReindexingQ l E Y s).obj P))
    (S.inv.app (F.obj ((podReindexingQ l E Y s).obj I)))
    (sourceModelOutput l E g s P I a).hom
    (Q.map (((podReindexingHom l E X s).map
      ((complexShift l E g s a).inv.app P).op).app KI) ≫
      Q.map eX.inv ≫ (Q.commShiftIso (-a)).hom.app (hom l E X s KP KI))
    hnat (by simpa only [Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc] using hmodel) htail
  simpa only [sourceModelInput, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.trans_hom, Iso.symm_hom,
    Iso.prod_hom, Iso.op_hom, Iso.app_inv, Iso.refl_hom,
    CategoryTheory.Functor.map_comp, Category.assoc] using hcalc

end WeilConjectures.PodReindexingCoherence
