/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
public import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Shift compatibility of the Roos scalar/tower chain comparison

For functors `K : S ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ)` whose Roos complexes carry shift
structures described by signed coordinate equations (`RoosShiftInl`, `RoosShiftInr`), the
Roos chain comparison `scalarRoosChain` induced by an additive functor and a comparison of
towers commutes with the shifts, as soon as the corresponding square of products of shifts
commutes (`scalarRoosChain_commShift`); the latter follows from level squares
(`scalarRoos_productSquare`).

This is the chain-level step of the proof of `rationalPullbackTransitionShift`.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph.
(blueprint: lem-sf-rational-pullback-transition-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor

section RoosCoordinates
variable {A S : Type*} [Category A] [Abelian A] [HasCountableProducts A]
  [Category S] [HasShift S ℤ] (K : S ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))
  [(K ⋙ integralOperationsRoosFunctor).CommShift ℤ]
  (p : ∀ (X : S) (m : ℤ), (∏ᶜ fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≅
    (∏ᶜ fun n ↦ (K.obj X).obj (op n))⟦m⟧)

/-- The first-inclusion coordinate equation of a shift on a Roos functor. -/
def RoosShiftInl : Prop :=
  ∀ (X : S) (m j : ℤ),
    (CochainComplex.mappingCocone.inl (scalarRoosBoundary (K.obj (X⟦m⟧)))).v j j
        (by omega) ≫
      (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X).f j =
    (p X m).hom.f j ≫
      (CochainComplex.mappingCocone.inl (scalarRoosBoundary (K.obj X))).v (j + m) (j + m)
        (by omega) ≫
      (CochainComplex.shiftFunctorObjXIso ((K ⋙ integralOperationsRoosFunctor).obj X)
        m j (j + m) rfl).inv

/-- The second-inclusion coordinate equation of a shift on a Roos functor. -/
def RoosShiftInr : Prop :=
  ∀ (X : S) (m i j : ℤ) (h : i + 1 = j),
    (CochainComplex.mappingCocone.inr (scalarRoosBoundary (K.obj (X⟦m⟧)))).1.v i j h ≫
      (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X).f j =
    m.negOnePow • ((p X m).hom.f i ≫
      (CochainComplex.mappingCocone.inr (scalarRoosBoundary (K.obj X))).1.v (i + m) (j + m)
        (by omega) ≫
      (CochainComplex.shiftFunctorObjXIso ((K ⋙ integralOperationsRoosFunctor).obj X)
        m j (j + m) rfl).inv)

/-- The first projection of a Roos shift is the product shift. -/
theorem roosShift_fst (hl : RoosShiftInl K p) (hr : RoosShiftInr K p) (X : S) (m : ℤ) :
    ((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K.obj X)))⟦m⟧' =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary (K.obj (X⟦m⟧))) ≫ (p X m).hom := by
  ext j
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  apply SignedCoconeShift.cocone_ext_from _ j
  · rw [← Category.assoc]
    erw [hl X m j]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc]
    erw [Category.id_comp, CochainComplex.mappingCocone.inl_v_fst_f,
      ← Category.assoc, CochainComplex.mappingCocone.inl_v_fst_f]
    simp
  · rw [← Category.assoc]
    erw [hr X m (j - 1) j (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc, Linear.units_smul_comp]
    erw [Category.id_comp, CochainComplex.mappingCocone.inr_v_fst_f,
      ← Category.assoc, CochainComplex.mappingCocone.inr_v_fst_f]
    simp

/-- The second projection of a Roos shift is the signed product shift. -/
theorem roosShift_snd (hl : RoosShiftInl K p) (hr : RoosShiftInr K p) (X : S) (m j : ℤ) :
    (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X).f j ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v (j + m) (j - 1 + m)
          (by omega) =
      m.negOnePow • ((CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (K.obj (X⟦m⟧)))).v j (j - 1) (by omega) ≫ (p X m).hom.f (j - 1)) := by
  apply SignedCoconeShift.cocone_ext_from _ j
  · rw [← Category.assoc]
    erw [hl X m j]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc, Linear.comp_units_smul]
    erw [Category.id_comp, CochainComplex.mappingCocone.inl_v_snd_v,
      ← Category.assoc, CochainComplex.mappingCocone.inl_v_snd_v]
    simp
  · rw [← Category.assoc]
    erw [hr X m (j - 1) j (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
    erw [Category.id_comp, CochainComplex.mappingCocone.inr_v_snd_v,
      ← Category.assoc, CochainComplex.mappingCocone.inr_v_snd_v]
    simp

end RoosCoordinates

section ScalarRoosShift
variable {A B S S' : Type*} [Category A] [Abelian A] [HasCountableProducts A]
  [Category B] [Abelian B] [HasCountableProducts B]
  [Category S] [HasShift S ℤ] [Category S'] [HasShift S' ℤ]
  (K : S ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ)) (K' : S' ⥤ (ℕᵒᵖ ⥤ CochainComplex B ℤ))
  (G : S ⥤ S') [G.CommShift ℤ] (O : A ⥤ B) [O.Additive]
  [eC : (K ⋙ integralOperationsRoosFunctor).CommShift ℤ]
  [eC' : (K' ⋙ integralOperationsRoosFunctor).CommShift ℤ]
  (p : ∀ (X : S) (m : ℤ), (∏ᶜ fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≅
    (∏ᶜ fun n ↦ (K.obj X).obj (op n))⟦m⟧)
  (p' : ∀ (X : S') (m : ℤ), (∏ᶜ fun n ↦ (K'.obj (X⟦m⟧)).obj (op n)) ≅
    (∏ᶜ fun n ↦ (K'.obj X).obj (op n))⟦m⟧)
  (α : K ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (O.mapHomologicalComplex (.up ℤ)) ⟶
    G ⋙ K')

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- Naturality of the components of the Roos scalar/tower chain comparison. -/
theorem scalarRoosChain_naturality {X Y : S} (a : X ⟶ Y) :
    ((K ⋙ integralOperationsRoosFunctor) ⋙ O.mapHomologicalComplex (.up ℤ)).map a ≫
        (scalarRoosMap O (K.obj Y) ≫ integralOperationsRoosMap (α.app Y)) =
      (scalarRoosMap O (K.obj X) ≫ integralOperationsRoosMap (α.app X)) ≫
        (G ⋙ (K' ⋙ integralOperationsRoosFunctor)).map a :=
  (scalarRoosTransformation K K' G O α).naturality a

/-- The Roos scalar/tower chain comparison as a transformation of composite functors. -/
noncomputable def scalarRoosChain :
    (K ⋙ integralOperationsRoosFunctor) ⋙ O.mapHomologicalComplex (.up ℤ) ⟶
      G ⋙ (K' ⋙ integralOperationsRoosFunctor) where
  app X := scalarRoosMap O (K.obj X) ≫ integralOperationsRoosMap (α.app X)
  naturality _ _ a := scalarRoosChain_naturality K K' G O α a

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- The first coordinate of the Roos chain comparison. -/
theorem scalarRoosChain_fst (X : S) :
    (scalarRoosChain K K' G O α).app X ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary (K'.obj (G.obj X))) =
      (O.mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K.obj X))) ≫
        piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ (α.app X).app (op n)) := by
  dsimp only [scalarRoosChain]
  rw [Category.assoc]
  erw [(scalarRoosTowerCoordinates (α.app X)).1]
  rw [← Category.assoc]
  erw [(scalarRoosCoordinates O (K.obj X)).1]
  rw [Category.assoc]

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- The second coordinate of the Roos chain comparison, after a product projection. -/
theorem scalarRoosChain_snd_π (X : S) (k q : ℤ) (h : k + -1 = q) (n : ℕ) :
    ((scalarRoosChain K K' G O α).app X).f k ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (K'.obj (G.obj X)))).v k q h ≫
        (Limits.Pi.π (fun n ↦ (K'.obj (G.obj X)).obj (op n)) n).f q =
      O.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v k q h ≫
        (Limits.Pi.π (fun n ↦ (K.obj X).obj (op n)) n).f q) ≫ ((α.app X).app (op n)).f q := by
  dsimp only [scalarRoosChain]
  rw [HomologicalComplex.comp_f, Category.assoc]
  erw [reassoc_of% ((scalarRoosTowerCoordinates (α.app X)).2 k q h)]
  have hπ := congrArg (fun z ↦ z.f q) (Limits.Pi.map_π (fun n ↦ (α.app X).app (op n)) n)
  simp only [HomologicalComplex.comp_f] at hπ
  have hs : (scalarRoosMap O (K.obj X)).f k ≫
      (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (K.obj X ⋙ O.mapHomologicalComplex (.up ℤ)))).v k q h ≫
      (Limits.Pi.π (fun n ↦ (O.mapHomologicalComplex (.up ℤ)).obj ((K.obj X).obj (op n))) n).f q =
      O.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v k q h ≫
        (Limits.Pi.π (fun n ↦ (K.obj X).obj (op n)) n).f q) :=
    (scalarRoosMap_existsUnique O (K.obj X)).exists.choose_spec.2 k q h n
  erw [hπ]
  exact (reassoc_of% hs) (((α.app X).app (op n)).f q)

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- The second coordinate of the Roos chain comparison. -/
theorem scalarRoosChain_snd (X : S) (k q : ℤ) (h : k + -1 = q) :
    ((scalarRoosChain K K' G O α).app X).f k ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (K'.obj (G.obj X)))).v k q h =
      O.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v k q h) ≫
        (piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n))).f q ≫
        (Limits.Pi.map (fun n ↦ (α.app X).app (op n))).f q := by
  apply (isLimitOfHasProductOfPreservesLimit (HomologicalComplex.eval B (.up ℤ) q)
    (fun n ↦ (K'.obj (G.obj X)).obj (op n))).hom_ext
  rintro ⟨n⟩
  simp only [Fan.mk_π_app, HomologicalComplex.eval_map, Category.assoc]
  rw [scalarRoosChain_snd_π]
  have hπ := congrArg (fun z ↦ z.f q) (Limits.Pi.map_π (fun n ↦ (α.app X).app (op n)) n)
  have hc := congrArg (fun z ↦ z.f q) (piComparison_comp_π (O.mapHomologicalComplex (.up ℤ))
    (fun n ↦ (K.obj X).obj (op n)) n)
  simp only [HomologicalComplex.comp_f] at hπ hc
  erw [hπ, reassoc_of% hc, O.map_comp_assoc]
  rfl

/-- The Roos chain comparison commutes with Roos shifts satisfying the signed coordinate
equations, given the product square. -/
theorem scalarRoosChain_commShift (hl : RoosShiftInl K p) (hr : RoosShiftInr K p)
    (hl' : RoosShiftInl K' p') (hr' : RoosShiftInr K' p')
    (hprod : ∀ (X : S) (m : ℤ),
      (O.mapHomologicalComplex (.up ℤ)).map (p X m).hom ≫
        ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
        (piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n)) ≫
          Limits.Pi.map (fun n ↦ (α.app X).app (op n)))⟦m⟧' =
      piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ (α.app (X⟦m⟧)).app (op n)) ≫
        Limits.Pi.map (fun n ↦ (K'.map ((G.commShiftIso m).hom.app X)).app (op n)) ≫
        (p' (G.obj X) m).hom) :
    NatTrans.CommShift (scalarRoosChain K K' G O α) ℤ := by
  constructor
  intro m
  ext X j
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Functor.commShiftIso_comp_hom_app, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  have H : ((O.mapHomologicalComplex (.up ℤ)).map
        (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X) ≫
      ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
      ((scalarRoosChain K K' G O α).app X)⟦m⟧') ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K'.obj (G.obj X))))⟦m⟧' =
      ((scalarRoosChain K K' G O α).app (X⟦m⟧) ≫
        (K' ⋙ integralOperationsRoosFunctor).map ((G.commShiftIso m).hom.app X) ≫
        ((K' ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app (G.obj X)) ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K'.obj (G.obj X))))⟦m⟧' := by
    simp only [Category.assoc, ← Functor.map_comp, scalarRoosChain_fst]
    rw [Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc,
      ← Functor.map_comp_assoc, roosShift_fst K p hl hr X m, Functor.map_comp_assoc, hprod,
      roosShift_fst K' p' hl' hr' (G.obj X) m]
    have ht := (scalarRoosTowerCoordinates (K'.map ((G.commShiftIso m).hom.app X))).1
    erw [reassoc_of% ht]
    erw [reassoc_of% (scalarRoosChain_fst K K' G O α (X⟦m⟧))]
  erw [Category.comp_id]
  apply CochainComplex.mappingCocone.ext_to (scalarRoosBoundary (K'.obj (G.obj X))) (j + m)
    (j - 1 + m) (by omega)
  · have h := congrArg (fun z ↦ z.f j) H
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.assoc] at h
    erw [Category.id_comp] at h
    simpa only [Category.assoc] using h
  · simp only [Category.assoc]
    rw [scalarRoosChain_snd, roosShift_snd K' p' hl' hr' (G.obj X) m j, Linear.comp_units_smul,
      Linear.comp_units_smul]
    have ht := (scalarRoosTowerCoordinates (K'.map ((G.commShiftIso m).hom.app X))).2 j (j - 1)
      (by omega)
    erw [reassoc_of% ht]
    erw [reassoc_of% (scalarRoosChain_snd K K' G O α (X⟦m⟧) j (j - 1) (by omega))]
    rw [Functor.mapHomologicalComplex_map_f, ← O.map_comp_assoc]
    erw [roosShift_snd K p hl hr X m j]
    have hp := congrArg (fun z ↦ z.f (j - 1)) (hprod X m)
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f] at hp
    erw [Category.id_comp] at hp
    rw [Units.smul_def, Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp]
    congr 1
    rw [O.map_comp, Category.assoc]
    erw [hp]

omit eC eC' in
/-- The product square for the Roos chain comparison follows from level squares. -/
theorem scalarRoos_productSquare
    (e : ∀ (X : S) (m : ℤ) (n : ℕ), (K.obj (X⟦m⟧)).obj (op n) ≅ ((K.obj X).obj (op n))⟦m⟧)
    (e' : ∀ (X : S') (m : ℤ) (n : ℕ), (K'.obj (X⟦m⟧)).obj (op n) ≅ ((K'.obj X).obj (op n))⟦m⟧)
    (hp : ∀ X m n, (p X m).hom ≫ (Limits.Pi.π (fun n ↦ (K.obj X).obj (op n)) n)⟦m⟧' =
      Limits.Pi.π (fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) n ≫ (e X m n).hom)
    (hp' : ∀ X m n, (p' X m).hom ≫ (Limits.Pi.π (fun n ↦ (K'.obj X).obj (op n)) n)⟦m⟧' =
      Limits.Pi.π (fun n ↦ (K'.obj (X⟦m⟧)).obj (op n)) n ≫ (e' X m n).hom)
    (hlev : ∀ X m n, (O.mapHomologicalComplex (.up ℤ)).map (e X m n).hom ≫
        ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
        ((α.app X).app (op n))⟦m⟧' =
      (α.app (X⟦m⟧)).app (op n) ≫ (K'.map ((G.commShiftIso m).hom.app X)).app (op n) ≫
        (e' (G.obj X) m n).hom)
    (X : S) (m : ℤ) :
    (O.mapHomologicalComplex (.up ℤ)).map (p X m).hom ≫
        ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
        (piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n)) ≫
          Limits.Pi.map (fun n ↦ (α.app X).app (op n)))⟦m⟧' =
      piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ (α.app (X⟦m⟧)).app (op n)) ≫
        Limits.Pi.map (fun n ↦ (K'.map ((G.commShiftIso m).hom.app X)).app (op n)) ≫
        (p' (G.obj X) m).hom := by
  apply (cancel_mono (PreservesProduct.iso (shiftFunctor (CochainComplex B ℤ) m)
    (fun n ↦ (K'.obj (G.obj X)).obj (op n))).hom).mp
  apply Limits.Pi.hom_ext
  intro n
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
  rw [hp']
  erw [Limits.Pi.map_π_assoc, Limits.Pi.map_π_assoc, piComparison_comp_π_assoc]
  rw [← Functor.map_comp, Category.assoc]
  erw [Limits.Pi.map_π, piComparison_comp_π_assoc]
  rw [Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc]
  erw [hp]
  rw [Functor.map_comp_assoc, hlev]

end ScalarRoosShift

end WeilConjectures
