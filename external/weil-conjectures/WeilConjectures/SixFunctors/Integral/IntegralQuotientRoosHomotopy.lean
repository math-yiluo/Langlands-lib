/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.CategoryTheory.Triangulated.Functor
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import WeilConjectures.CategoryTheory.Strict.StrictRoosHomotopyFunctor

/-! # The augmented quotient Roos functor before deriving

Source: Stacks Project, Tags 014E, 011G and 08TC.
(blueprint: lem-sf-integral-quotient-roos-homotopy)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
universe t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures
open IntegralOnSlice

noncomputable section

open Opposite CochainComplex Pretriangulated

private theorem commShift_of_whiskerLeft
    {C K B : Type*} [Category C] [Category K] [Category B]
    [HasShift C ℤ] [HasShift K ℤ] [HasShift B ℤ]
    (q : C ⥤ K) [q.CommShift ℤ]
    [((Functor.whiskeringLeft C K B).obj q).Faithful]
    {F G : K ⥤ B} [F.CommShift ℤ] [G.CommShift ℤ]
    (a : F ⟶ G) [NatTrans.CommShift (Functor.whiskerLeft q a) ℤ] :
    NatTrans.CommShift a ℤ := by
  constructor
  intro r
  apply ((Functor.whiskeringLeft C K B).obj q).map_injective
  ext P
  apply (cancel_epi (F.map ((q.commShiftIso r).hom.app P))).1
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft q a) r P
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← a.naturality_assoc] at h
  exact h

namespace AugmentedRoos

attribute [local irreducible] roosF roosConeFunctor

universe a b c
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  (F : A ⥤ (ℕᵒᵖ ⥤ A)) [F.Additive]

private def cone
    (η : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⟶ F) (P : CochainComplex A ℤ) :
    Cone ((F.mapHomologicalComplex (.up ℤ)).obj P).asFunctor where
  pt := P
  π :=
    { app n :=
        { f i := (η.app (P.X i)).app n
          comm' i j _ := congrArg (fun k ↦ k.app n) (η.naturality (P.d i j)).symm }
      naturality n m g := by
        ext i
        exact (η.app (P.X i)).naturality g }

private theorem cone_condition (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (j : Cone N.asFunctor) :
    Pi.lift (fun n : ℕ ↦ j.π.app (op n)) ≫ roosU N = 0 := by
  apply Pi.hom_ext
  intro n
  simp [roosU, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, j.w]

private def augmentation
    (η : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⟶ F)
    (hnat : RoosConeCalculus.AugmentationNaturality A) :
    𝟭 (CochainComplex A ℤ) ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ roosF where
  app P := RoosConeCalculus.augmentation (cone F η P)
  naturality P Q f :=
    (hnat ((F.mapHomologicalComplex (.up ℤ)).map f)
      (cone F η P) (cone F η Q) f (by
        intro n
        apply HomologicalComplex.hom_ext
        intro i
        exact (congrArg (fun k ↦ k.app (op n)) (η.naturality (f.f i))).symm)).symm

private theorem augmentation_shift
    (η : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⟶ F)
    (hnat : RoosConeCalculus.AugmentationNaturality A)
    (cs : (roosF (A := A)).CommShift ℤ) (hs : RoosConeCalculus.ShiftAugmentation cs) :
    letI := cs
    NatTrans.CommShift (augmentation F η hnat) ℤ := by
  let := cs
  constructor
  intro r
  apply NatTrans.ext
  funext P
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.commShiftIso_id_hom_app]
  erw [Category.id_comp]
  let s := ((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).app P
  let js : Cone (((F.mapHomologicalComplex (.up ℤ)).obj P)⟦r⟧).asFunctor :=
    { pt := P⟦r⟧
      π := (cone F η (P⟦r⟧)).π ≫
        HomologicalComplex.complexOfFunctorsToFunctorToComplex.map s.hom }
  have hn := hnat s.hom
    (cone F η (P⟦r⟧)) js (𝟙 _) (by intro n; simp [js])
  have hs := hs
    ((F.mapHomologicalComplex (.up ℤ)).obj P) (cone F η P) r js (𝟙 _) (by
      intro q n
      simp only [js, cone, s, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
        CochainComplex.shiftFunctorObjXIso, Functor.const_obj_obj,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, NatTrans.id_app,
        shiftFunctor_obj_X', HomologicalComplex.id_f, Category.id_comp,
        NatTrans.comp_app, HomologicalComplex.comp_f, Iso.app_hom, Category.assoc,
        HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f]
      erw [Category.id_comp, Category.comp_id])
  simp only [Category.id_comp] at hn hs
  change ((augmentation F η hnat).app P)⟦r⟧' = _
  rw [Functor.commShiftIso_comp_hom_app]
  dsimp only [Functor.comp_map, augmentation]
  rw [← Category.assoc]
  change (RoosConeCalculus.augmentation (cone F η P))⟦r⟧' =
    (RoosConeCalculus.augmentation (cone F η (P⟦r⟧)) ≫ roosF.map s.hom) ≫
      (Functor.commShiftIso roosF r).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
  exact hs.symm.trans (congrArg
    (fun (f : P⟦r⟧ ⟶ roosF.obj (((F.mapHomologicalComplex (.up ℤ)).obj P)⟦r⟧)) ↦
      f ≫ (Functor.commShiftIso roosF r).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) hn.symm)

private def roosTriangleIso
    (cs : (roosF (A := A)).CommShift ℤ)
    (Φ : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
    (hc : RoosConeCalculus.ConeCompatibility cs Φ)
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') :
    letI := cs
    roosF.mapTriangle.obj (mappingCone.triangle f) ≅ mappingCone.triangle (roosF.map f) := by
  let := cs
  dsimp only [mappingCone.triangle, CategoryTheory.Functor.mapTriangle_obj]
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Φ f) ?_ ?_ ?_
  · change roosF.map f ≫ 𝟙 _ = 𝟙 _ ≫ roosF.map f
    simp only [Category.comp_id, Category.id_comp]
  · change roosF.map (mappingCone.inr f) ≫ _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
    exact (hc.2 f).1
  · change (_ ≫ _) ≫ (𝟙 _)⟦(1 : ℤ)⟧' = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact (hc.2 f).2

variable [HasDerivedCategory.{c} A]

private theorem descent
    (η : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⟶ F)
    (hnat : RoosConeCalculus.AugmentationNaturality A)
    (cs : (roosF (A := A)).CommShift ℤ)
    (Φ : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
    (hc : RoosConeCalculus.ConeCompatibility cs Φ)
    (hshift : RoosConeCalculus.ShiftAugmentation cs) :
    ∃ (H : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory.{c} A)
      (_ : H.CommShift ℤ)
      (e : HomotopyCategory.quotient A (.up ℤ) ⋙ H ≅
        (F.mapHomologicalComplex (.up ℤ) ⋙ roosF) ⋙ DerivedCategory.Q)
      (β : DerivedCategory.Qh ⟶ H),
      H.IsTriangulated ∧ NatTrans.CommShift β ℤ ∧
        ∀ P : CochainComplex A ℤ,
          (DerivedCategory.quotientCompQhIso A).inv.app P ≫
            β.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
              e.hom.app P = DerivedCategory.Q.map ((augmentation F η hnat).app P) := by
  let := cs
  let G := F.mapHomologicalComplex (.up ℤ) ⋙ roosF
  let q := HomotopyCategory.quotient A (.up ℤ)
  have hG : ∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y),
      homotopic A (.up ℤ) f g →
        (G ⋙ DerivedCategory.Q.{c}).map f = (G ⋙ DerivedCategory.Q.{c}).map g := by
    intro X Y f g ⟨h⟩
    obtain ⟨H, _⟩ := (roosF_homotopy_functor.{a, b, 0} (A := A)).2.1 _ _ _ _
      (F.mapHomotopy h)
    exact DerivedCategory.Q_map_eq_of_homotopy A H
  let H := CategoryTheory.Quotient.lift _ (G ⋙ DerivedCategory.Q.{c}) hG
  let : H.CommShift ℤ := CategoryTheory.Quotient.liftCommShift _ _ _ _
  let e : q ⋙ H ≅ G ⋙ DerivedCategory.Q := CategoryTheory.Quotient.lift.isLift _ _ _
  have : NatTrans.CommShift e.hom ℤ := CategoryTheory.Quotient.liftCommShift_compatibility _ _ _ _
  let a := augmentation F η hnat
  have : NatTrans.CommShift a ℤ := augmentation_shift F η hnat cs hshift
  let b : q ⋙ DerivedCategory.Qh ⟶ q ⋙ H :=
    (DerivedCategory.quotientCompQhIso A).hom ≫
      (DerivedCategory.Q (C := A)).leftUnitor.inv ≫
      Functor.whiskerRight a DerivedCategory.Q ≫ e.inv
  have : NatTrans.CommShift b ℤ := by
    dsimp only [b]
    infer_instance
  let β : DerivedCategory.Qh ⟶ H := CategoryTheory.Quotient.natTransLift _ b
  have hb : Functor.whiskerLeft q β = b := by ext P; rfl
  have : NatTrans.CommShift (Functor.whiskerLeft q β) ℤ := hb.symm ▸ inferInstance
  have : NatTrans.CommShift β ℤ := commShift_of_whiskerLeft q β
  refine ⟨H, inferInstance, e, β, ?_, inferInstance, ?_⟩
  · constructor
    intro T hT
    obtain ⟨M, N, f, ⟨i⟩⟩ := hT
    apply isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (G.map f)) _
    exact H.mapTriangle.mapIso i ≪≫
      (Functor.mapTriangleCompIso q H).symm.app _ ≪≫
      (Functor.mapTriangleIso e).app _ ≪≫
      (Functor.mapTriangleCompIso G DerivedCategory.Q).app _ ≪≫
      DerivedCategory.Q.mapTriangle.mapIso
        ((Functor.mapTriangleCompIso (F.mapHomologicalComplex (.up ℤ)) roosF).app _ ≪≫
          roosF.mapTriangle.mapIso (mappingCone.mapTriangleIso f F) ≪≫
          roosTriangleIso cs Φ hc ((F.mapHomologicalComplex (.up ℤ)).map f))
  · intro P
    change (DerivedCategory.quotientCompQhIso A).inv.app P ≫
      ((DerivedCategory.quotientCompQhIso A).hom.app P ≫
        (𝟙 _ ≫ DerivedCategory.Q.map (a.app P) ≫ e.inv.app P)) ≫ e.hom.app P = _
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]

private theorem descent_compare
    (η : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⟶ F)
    (hnat : RoosConeCalculus.AugmentationNaturality A)
    (cs : (roosF (A := A)).CommShift ℤ)
    (Φ : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
    (hc : RoosConeCalculus.ConeCompatibility cs Φ)
    (hs : RoosConeCalculus.ShiftAugmentation cs)
    (R : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (comparison : F.mapHomologicalComplex (.up ℤ) ⋙ roosF ≅ R)
    (unit : ∀ P : CochainComplex A ℤ, P ⟶ R.obj P)
    (hu : ∀ P, (augmentation F η hnat).app P ≫ comparison.hom.app P = unit P) :
    ∃ (H : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory.{c} A)
      (_ : H.CommShift ℤ)
      (e : HomotopyCategory.quotient A (.up ℤ) ⋙ H ≅ R ⋙ DerivedCategory.Q)
      (β : DerivedCategory.Qh ⟶ H),
      H.IsTriangulated ∧ NatTrans.CommShift β ℤ ∧
        ∀ P : CochainComplex A ℤ,
          (DerivedCategory.quotientCompQhIso A).inv.app P ≫
            β.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
              e.hom.app P = DerivedCategory.Q.map (unit P) := by
  obtain ⟨H, sH, e, β, hH, hβ, he⟩ := descent F η hnat cs Φ hc hs
  let r := Functor.isoWhiskerRight comparison DerivedCategory.Q
  refine ⟨H, sH, e ≪≫ r, β, hH, hβ, ?_⟩
  intro P
  change (DerivedCategory.quotientCompQhIso A).inv.app P ≫
      β.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        (e.hom.app P ≫ DerivedCategory.Q.map (comparison.hom.app P)) = _
  have h := he P
  rw [← Category.assoc] at h
  rw [← Category.assoc, ← Category.assoc, h, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (hu P)

end AugmentedRoos

namespace SequenceComplex

universe a b
variable {A : Type a} [Category.{b} A] [Abelian A]
  (D : ℕ → A ⥤ A) [∀ n, (D n).Additive]
  (τ : ∀ n, D (n + 1) ⟶ D n)
  (L : ℕ → CochainComplex A ℤ ⥤ CochainComplex A ℤ)
  (σ : ∀ n, L (n + 1) ⟶ L n)
  (e : ∀ n, (D n).mapHomologicalComplex (.up ℤ) ≅ L n)
  (h : ∀ n, NatTrans.mapHomologicalComplex (τ n) (.up ℤ) ≫ (e n).hom =
    (e (n + 1)).hom ≫ σ n)

private instance sequence_additive : (Functor.ofOpSequence τ).flip.Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext n
    exact (D n.unop).map_add

private def comparison (P : CochainComplex A ℤ) :
    ((((Functor.ofOpSequence τ).flip).mapHomologicalComplex (.up ℤ)).obj P).asFunctor ≅
      ((Functor.ofOpSequence σ).flip).obj P := by
  let a : ((((Functor.ofOpSequence τ).flip).mapHomologicalComplex (.up ℤ)).obj P).asFunctor ⟶
      ((Functor.ofOpSequence σ).flip).obj P :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom.app P) (fun n ↦ by
      have hs :
          ((((Functor.ofOpSequence τ).flip).mapHomologicalComplex (.up ℤ)).obj P).asFunctor.map
            (homOfLE (Nat.le_succ n)).op =
          (NatTrans.mapHomologicalComplex (τ n) (.up ℤ)).app P := by
        apply HomologicalComplex.hom_ext
        intro i
        change (((Functor.ofOpSequence τ).map
          (homOfLE (Nat.le_succ n)).op).app (P.X i)) = _
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        rfl
      rw [hs]
      change _ = _ ≫ (((Functor.ofOpSequence σ).map
        (homOfLE (Nat.le_succ n)).op).app P)
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact congrArg (fun a ↦ a.app P) (h n))
  exact NatIso.ofComponents (fun n ↦ (e n.unop).app P) (fun f ↦ a.naturality f)

private def comparisonNat :
    ((Functor.ofOpSequence τ).flip).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        (Functor.ofOpSequence σ).flip :=
  NatIso.ofComponents (comparison D τ L σ e h) (fun f ↦ by
    apply NatTrans.ext
    funext n
    exact (e n.unop).hom.naturality f)

private def augmentation (ε : ∀ n, 𝟭 A ⟶ D n)
    (hε : ∀ n, ε n = ε (n + 1) ≫ τ n) :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⟶ (Functor.ofOpSequence τ).flip where
  app M := NatTrans.ofOpSequence (fun n ↦ (ε n).app M) (fun n ↦ by
    change 𝟙 M ≫ _ = _ ≫
      (((Functor.ofOpSequence τ).map (homOfLE (Nat.le_succ n)).op).app M)
    rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
    exact congrArg (fun α ↦ α.app M) (hε n))
  naturality M N a := by
    apply NatTrans.ext
    funext n
    exact (ε n.unop).naturality a

end SequenceComplex

private def roosPresentationIso
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A] :
    roosF (A := A) ≅ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change roosF.map f = integralOperationsRoosMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)
    unfold integralOperationsRoosMap
    rw [arrowConeMap]
    · rfl
    · exact integralOperationsRoos_square _)

private theorem roosAugmentation_compare
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (a : N.asFunctor ⟶ C) (j : Cone N.asFunctor)
    (v : j.pt ⟶ ∏ᶜ fun n : ℕ ↦ C.obj (op n))
    (hv : v ≫ towerTransitionEndomorphism (integralOperationsTowerStep C) = 0)
    (ha : ∀ n : ℕ, j.π.app (op n) ≫ a.app (op n) =
      v ≫ Pi.π (fun n : ℕ ↦ C.obj (op n)) n) :
    RoosConeCalculus.augmentation j ≫ integralOperationsRoosMap a =
      mappingCocone.lift
        (towerTransitionEndomorphism (integralOperationsTowerStep C)) v 0 (by simp [hv]) := by
  have hu := AugmentedRoos.cone_condition N j
  have hn : 𝟙 j.pt ≫ v =
      Pi.lift (fun n : ℕ ↦ j.π.app (op n)) ≫
        CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) := by
    apply Pi.hom_ext
    intro n
    simpa only [Category.id_comp, Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc] using
      (ha n).symm
  unfold integralOperationsRoosMap
  rw [arrowConeMap A _ _ _ _ (integralOperationsRoos_square a)]
  symm
  convert completedCoconeLift_natural A (roosU N) _ _ _
    (integralOperationsRoos_square a) (𝟙 j.pt) _ _ hu hv hn using 1 <;>
    first | rfl | simp only [Category.id_comp]

namespace QuotientRoosProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (T : AlgebraicGeometry.Scheme.{t})

private def moduleLevel (n : ℕ) : Mod l E T none ⥤ Mod l E T none :=
  reduction l E T none n ⋙ SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (projection l E T none n))

private instance moduleLevel_additive (n : ℕ) : (moduleLevel l E T n).Additive := by
  unfold moduleLevel
  infer_instance

private def moduleTransition (n : ℕ) :
    moduleLevel l E T (n + 1) ⟶ moduleLevel l E T n where
  app M := IntegralOnSlice.unrestrictedModuleStep l E T none n M
  naturality _ _ a := IntegralOnSlice.unrestrictedModuleStep_naturality l E T none n a

private theorem transition_eq (n : ℕ) :
    transition l E T none n =
      NatTrans.mapHomologicalComplex (moduleTransition l E T n) (.up ℤ) := by
  apply (transition_existsUnique l E T none n).unique
  · exact (transition_existsUnique l E T none n).exists.choose_spec
  · intro P i V s x
    exact IntegralOnSlice.unrestrictedModuleStep_tmul l E T none n (P.X i) V s x

private def moduleTower : Mod l E T none ⥤ (ℕᵒᵖ ⥤ Mod l E T none) :=
  (Functor.ofOpSequence (moduleTransition l E T)).flip

private instance moduleTower_additive : (moduleTower l E T).Additive :=
  SequenceComplex.sequence_additive (moduleLevel l E T) (moduleTransition l E T)

private theorem moduleUnit_step (n : ℕ) :
    moduleUnit l E T none n =
      moduleUnit l E T none (n + 1) ≫ moduleTransition l E T n := by
  apply NatTrans.ext
  funext M
  ext V x
  change (unitModule l E T none n M).val.app V x =
    (IntegralOnSlice.unrestrictedModuleStep l E T none n M).val.app V
      ((unitModule l E T none (n + 1) M).val.app V x)
  rw [unitModule_apply, unitModule_apply]
  simpa only [map_one] using
    (IntegralOnSlice.unrestrictedModuleStep_tmul l E T none n M V 1 x).symm

private def moduleAugmentation :
    (Functor.const ℕᵒᵖ : Mod l E T none ⥤ (ℕᵒᵖ ⥤ Mod l E T none)) ⟶
      moduleTower l E T :=
  SequenceComplex.augmentation (moduleLevel l E T) (moduleTransition l E T)
    (moduleUnit l E T none) (moduleUnit_step l E T)

private def levelComparison (n : ℕ) :
    (moduleLevel l E T n).mapHomologicalComplex (.up ℤ) ≅ level l E T none n :=
  Iso.refl _

private theorem stepComparison (n : ℕ) :
    NatTrans.mapHomologicalComplex (moduleTransition l E T n) (.up ℤ) ≫
        (levelComparison l E T n).hom =
      (levelComparison l E T (n + 1)).hom ≫ transition l E T none n := by
  simp only [levelComparison, Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact (transition_eq l E T n).symm

private def towerComparison (P : Cx l E T none) :
    (((moduleTower l E T).mapHomologicalComplex (.up ℤ)).obj P).asFunctor ≅
      (tower l E T none).obj P :=
  SequenceComplex.comparison (moduleLevel l E T) (moduleTransition l E T)
    (level l E T none) (transition l E T none) (levelComparison l E T)
    (stepComparison l E T) P

private def towerComparisonNat :
    (moduleTower l E T).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ tower l E T none :=
  SequenceComplex.comparisonNat (moduleLevel l E T) (moduleTransition l E T)
    (level l E T none) (transition l E T none) (levelComparison l E T)
    (stepComparison l E T)

private def roosComparison :
    (moduleTower l E T).mapHomologicalComplex (.up ℤ) ⋙ roosF ≅ roos l E T none :=
  Functor.isoWhiskerLeft _ roosPresentationIso ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (towerComparisonNat l E T) integralOperationsRoosFunctor

private theorem roosComparison_hom (P : Cx l E T none) :
    (roosComparison l E T).hom.app P =
      integralOperationsRoosMap (towerComparison l E T P).hom := by
  simp only [roosComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    towerComparisonNat, roosPresentationIso]
  rfl

private theorem augmentation_comparison
    (hnat : RoosConeCalculus.AugmentationNaturality (Mod l E T none))
    (P : Cx l E T none) :
    (AugmentedRoos.augmentation (moduleTower l E T)
      (moduleAugmentation l E T) hnat).app P ≫ (roosComparison l E T).hom.app P =
        roosUnit l E T none P := by
  let N := ((moduleTower l E T).mapHomologicalComplex (.up ℤ)).obj P
  let a := (towerComparison l E T P).hom
  let γ := fun n : ℕ ↦ (AugmentedRoos.cone (moduleTower l E T)
    (moduleAugmentation l E T) P).π.app (op n)
  have hδ : productAugmentation l E T none P ≫
      towerTransitionEndomorphism
        (integralOperationsTowerStep ((tower l E T none).obj P)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa using roosUnit_condition l E T none P
  have ha (n : ℕ) : γ n ≫ a.app (op n) =
      ((IntegralOnSlice.augmentation l E T none).app P).app (op n) := by
    apply HomologicalComplex.hom_ext
    intro i
    change (unitModule l E T none n (P.X i)) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    ext V x
    exact (unitModule_apply l E T none n (P.X i) V x).trans
      ((augmentation_existsUnique l E T none).exists.choose_spec P n i V x).symm
  rw [roosComparison_hom]
  change RoosConeCalculus.augmentation (AugmentedRoos.cone (moduleTower l E T)
    (moduleAugmentation l E T) P) ≫ integralOperationsRoosMap a = _
  exact roosAugmentation_compare N ((tower l E T none).obj P) a
    (AugmentedRoos.cone (moduleTower l E T) (moduleAugmentation l E T) P)
    (productAugmentation l E T none P) hδ (by
      intro n
      simpa only [productAugmentation, Pi.lift_comp_π] using ha n)

end QuotientRoosProof

end

/-- The ordinary quotient Roos construction descends to an exact functor on the
homotopy category, with its zero-second-coordinate augmentation.

Source: Stacks Project, Tags 014E, 011G and 08TC; signed Roos cone calculus.
(blueprint: lem-sf-integral-quotient-roos-homotopy).

Proof: Assemble ordinary quotient extension and scalar restriction into an
additive module-valued tower functor. Its degreewise extension preserves
homotopies and commutes with shifts and mapping cones, including their
inclusions and negative projections. Identify its complex-valued tower with
IntegralOnSlice.tower by the pure-tensor characterization of transition.
The signed Roos cone calculus preserves compatible homotopies and gives a
coherent shift comparison and a cone comparison preserving the last arrow.
Consequently localization of Roos descends through the homotopy quotient,
and sends every distinguished homotopy triangle to a distinguished derived
triangle. The module units give an augmentation into the tower. Its Roos
augmentation has zero second coordinate, so the signed shift comparison
fixes that augmentation. Descend this natural transformation through the
full homotopy quotient. Uniqueness of the termwise quotient units and the
mapping-cocone lift identifies its components with roosUnit. This is all
before deriving: no K-flat resolution, quasi-isomorphism inversion, derived
completion functor or completeness assertion is used. -/
theorem integralQuotientRoos_homotopy
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : AlgebraicGeometry.Scheme.{t}) :
    ∃ (H : HomotopyCategory (Mod l E T none) (.up ℤ) ⥤ D l E T none)
      (_ : H.CommShift ℤ)
      (e : HomotopyCategory.quotient (Mod l E T none) (.up ℤ) ⋙ H ≅
        roos l E T none ⋙ DerivedCategory.Q)
      (β : DerivedCategory.Qh ⟶ H),
      H.IsTriangulated ∧ NatTrans.CommShift β ℤ ∧
        ∀ P : Cx l E T none,
          (DerivedCategory.quotientCompQhIso (Mod l E T none)).inv.app P ≫
            β.app ((HomotopyCategory.quotient (Mod l E T none) (.up ℤ)).obj P) ≫
              e.hom.app P = DerivedCategory.Q.map (roosUnit l E T none P) := by
  classical
  obtain ⟨_, _, _, _, cs, Φ, hnat, _, _, hc, _, hs⟩ :=
    @RoosConeCalculus.roos_cone_calculus T (rings l E T none)
      (IntegralOnSlice.hasDerived l E T none)
  exact AugmentedRoos.descent_compare
    (QuotientRoosProof.moduleTower l E T) (QuotientRoosProof.moduleAugmentation l E T)
    hnat cs Φ hc hs (roos l E T none) (QuotientRoosProof.roosComparison l E T)
    (roosUnit l E T none) (QuotientRoosProof.augmentation_comparison l E T hnat)

end WeilConjectures
