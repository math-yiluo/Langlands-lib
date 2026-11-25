/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # The strict signed Roos reindexing square -/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 50000] WeilConjectures.podSheafCanonicalPreadditive

universe a b u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 10000] WeilConjectures.podLimitCommShift

private abbrev canonicalSheafComplex
    {T : Type*} [Category T] {J : GrothendieckTopology T}
    (M : Sheaf J RingCat)
    [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] :=
  CochainComplex (SheafOfModules.{a} M) ℤ

private abbrev canonicalSheafRoosFunctor
    {T : Type*} [Category T] {J : GrothendieckTopology T}
    (M : Sheaf J RingCat)
    [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
    [HasCountableProducts (SheafOfModules.{a} M)] :
    (ℕᵒᵖ ⥤ canonicalSheafComplex M) ⥤ canonicalSheafComplex M :=
  integralOperationsRoosFunctor

private theorem commShift_of_conjugate
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G F' G' : C ⥤ D}
    [F.CommShift ℤ] [G.CommShift ℤ] [F'.CommShift ℤ] [G'.CommShift ℤ]
    (a : F ≅ F') (b : G ≅ G') (τ : F ⟶ G) (ν : F' ⟶ G')
    [NatTrans.CommShift a.hom ℤ] [NatTrans.CommShift b.hom ℤ]
    [NatTrans.CommShift ν ℤ] (h : a.hom ≫ ν = τ ≫ b.hom) :
    NatTrans.CommShift τ ℤ := by
  have : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  have ht : τ = a.hom ≫ ν ≫ b.inv := by
    have hh := congrArg (· ≫ b.inv) h
    simpa only [Category.assoc, b.hom_inv_id, Category.comp_id] using hh.symm
  rw [ht]
  infer_instance

private theorem commShift_Q_components
    {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category C] [HasShift C ℤ]
    (U V : C ⥤ CochainComplex A ℤ) [U.CommShift ℤ] [V.CommShift ℤ]
    (ν : U ⋙ DerivedCategory.Q ⟶ V ⋙ DerivedCategory.Q)
    (f : ∀ X, U.obj X ⟶ V.obj X)
    (hn : ∀ X, ν.app X = DerivedCategory.Q.map (f X))
    (hf : ∀ X (r : ℤ), (U.commShiftIso r).hom.app X ≫ (f X)⟦r⟧' =
      f (X⟦r⟧) ≫ (V.commShiftIso r).hom.app X) :
    NatTrans.CommShift ν ℤ := by
  constructor
  intro r
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, hn,
    Functor.commShiftIso_comp_hom_app]
  rw [Category.assoc, ← DerivedCategory.Q.commShiftIso_hom_naturality,
    ← DerivedCategory.Q.map_comp_assoc, hf, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]

private def towerToComplex
    {A : Type*} [Category A] [Abelian A] :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  obj C := towerAsComplex C
  map {C C'} a :=
    { f := fun i ↦
        { app := fun n ↦ (a.app n).f i
          naturality := fun n m z ↦ congrArg (fun x ↦ x.f i) (a.naturality z) }
      comm' := fun i j _ ↦ NatTrans.ext (by
        funext n
        exact (a.app n).comm i j) }
  map_id C := by ext i n; rfl
  map_comp a b := by ext i n; rfl

private theorem nativeRoos_map
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {C C' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : C ⟶ C') :
    roosF.map f = integralOperationsRoosFunctor.map
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) := by
  exact (podNativeRoosMap_eq f).symm

private theorem roosMap_eq
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : C ⟶ C') :
    integralOperationsRoosMap f = integralOperationsRoosFunctor.map f := by
  rfl

private theorem native_signed_natural
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') (r : ℤ) :
    integralOperationsRoosFunctor.map
      (Functor.whiskerRight a (shiftFunctor (CochainComplex A ℤ) r)) ≫
        (podNativeRoosShift.comparison C' r).hom =
    (podNativeRoosShift.comparison C r).hom ≫
      (integralOperationsRoosFunctor.map a)⟦r⟧' := by
  let f := (towerToComplex (A := A)).map a
  let := CategoryTheory.RoosConeCalculus.roosCommShift (A := A)
  have h := Functor.commShiftIso_hom_naturality roosF f r
  rw [nativeRoos_map, nativeRoos_map] at h
  exact h

private theorem paste_shift_square
    {A : Type*} [Category A] {P Q R S T U V W Z Y V₁ V₂ : A}
    (x : P ⟶ Q) (y : Q ⟶ R) (t : R ⟶ S) (z' : S ⟶ T) (d' : T ⟶ U)
    (z : P ⟶ V) (d : V ⟶ W) (p : W ⟶ Z) (q : Z ⟶ Y) (s : Y ⟶ U)
    (m : V ⟶ V₁) (n : V₁ ⟶ V₂) (dₛ : V₂ ⟶ Y) (s' : V₂ ⟶ T) (k : Q ⟶ V₁)
    (hc : d ≫ p ≫ q = m ≫ n ≫ dₛ) (ha : dₛ ≫ s = s' ≫ d')
    (hb : z ≫ m = x ≫ k) (hd : k ≫ n ≫ s' = y ≫ t ≫ z') :
    x ≫ y ≫ t ≫ (z' ≫ d') = z ≫ d ≫ p ≫ q ≫ s := by
  calc
    _ = x ≫ (y ≫ t ≫ z') ≫ d' := by simp only [Category.assoc]
    _ = x ≫ (k ≫ n ≫ s') ≫ d' := by rw [← hd]
    _ = (x ≫ k) ≫ n ≫ (s' ≫ d') := by simp only [Category.assoc]
    _ = (z ≫ m) ≫ n ≫ (dₛ ≫ s) := by rw [← hb, ← ha]
    _ = z ≫ (m ≫ n ≫ dₛ) ≫ s := by simp only [Category.assoc]
    _ = z ≫ (d ≫ p ≫ q) ≫ s := by rw [← hc]
    _ = _ := by simp only [Category.assoc]

private theorem map_triple_eq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {P Q R S Q' R' : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S)
    (f' : P ⟶ Q') (g' : Q' ⟶ R') (h' : R' ⟶ S)
    (he : f ≫ g ≫ h = f' ≫ g' ≫ h') :
    F.map f ≫ F.map g ≫ F.map h = F.map f' ≫ F.map g' ≫ F.map h' := by
  simpa only [F.map_comp] using congrArg F.map he

private theorem generic_restricted_shift
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Preadditive A] [Preadditive A'] [Preadditive B] [Preadditive B']
    (P : A ⥤ A') (G : B ⥤ B') (RY : A ⥤ (ℕᵒᵖ ⥤ B))
    (RX : A' ⥤ (ℕᵒᵖ ⥤ B'))
    [P.Additive] [G.Additive] [RY.Additive] [RX.Additive]
    (e : ∀ C : CochainComplex A ℤ,
      ((RY.mapHomologicalComplex (.up ℤ)).obj C).asFunctor ⋙
          G.mapHomologicalComplex (.up ℤ) ≅
        ((RX.mapHomologicalComplex (.up ℤ)).obj
          ((P.mapHomologicalComplex (.up ℤ)).obj C)).asFunctor)
    (he : ∀ C (r : ℤ) n i,
      ((e (C⟦r⟧)).hom.app n).f i = ((e C).hom.app n).f (i + r))
    (C : CochainComplex A ℤ) (r : ℤ) :
    let RYc := RY.mapHomologicalComplex (.up ℤ)
    let RXc := RX.mapHomologicalComplex (.up ℤ)
    let Pc := P.mapHomologicalComplex (.up ℤ)
    let Gc := G.mapHomologicalComplex (.up ℤ)
    let K := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (e (C⟦r⟧)).hom ≫ K.map (RXc.map ((Pc.commShiftIso r).hom.app C)) ≫
      K.map ((RXc.commShiftIso r).hom.app (Pc.obj C)) =
    Functor.whiskerRight
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((RYc.commShiftIso r).hom.app C)) Gc ≫
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (RYc.obj C).asFunctor (Gc.commShiftIso r) ≪≫
          (Functor.associator _ _ _).symm).hom ≫
      Functor.whiskerRight (e C).hom (shiftFunctor (CochainComplex B' ℤ) r) := by
  dsimp only
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  dsimp only [Iso.trans, Iso.symm, Functor.associator, Functor.mapIso,
    Functor.isoWhiskerLeft, Functor.whiskerLeft, Functor.whiskerRight,
    whiskeringLeft, Functor.category, NatTrans.vcomp,
    NatTrans.comp_app, HomologicalComplex.comp_f,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex,
    Functor.isoWhiskerLeft_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomologicalComplex_map_f]
  erw [NatTrans.comp_app, NatTrans.comp_app]
  dsimp only
  simp only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    NatTrans.id_app, CochainComplex.shiftFunctor_map_f']
  dsimp only [Functor.comp_obj]
  erw [RX.map_id, NatTrans.id_app, G.map_id]
  erw [NatTrans.comp_app]
  dsimp only
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  erw [Category.comp_id, Category.comp_id,
    Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  exact he C r n i

attribute [local irreducible] CategoryTheory.RoosConeCalculus.roosCommShift

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev scalarRoosFunctor (W : Scheme.{u}) :
    (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ) ⥤
      CochainComplex (scalarReductionSource l E W) ℤ :=
  canonicalSheafRoosFunctor _

/-- Completed relabelling is additive on module sheaves.
Source: Stacks 015F (blueprint: lem-pod-strict-roos-reindex-shift-s8). -/
instance podReindexIntegralInverseAdditive
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoReductionIntegralInverse l E g).Additive :=
  isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom

private instance integralInverse_limits
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteLimits (isoReductionIntegralInverse l E g) := by
  let := (isoReductionCompletedMap l E g).isIso_hom
  exact isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom

private instance integralInverse_colimits
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteColimits (isoReductionIntegralInverse l E g) := by
  let := (isoReductionCompletedMap l E g).isIso_hom
  exact isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom

private theorem restricted_shift_f
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ)
    (n : ℕ) (i : ℤ) :
    ((D.restricted (C⟦r⟧)).hom.app (op n)).f i =
      ((D.restricted C).hom.app (op n)).f (i + r) := by
  ext U x
  let V := (proEtaleIsoPostcompose g).op.obj U
  let x' : (C.X (i + r)).val.obj (op (n, V.unop)) :=
    cast (integralComparisonRestrictedSectionType l E Y (C.X (i + r)) n V) x
  have hx : integralComparisonRestrictedSection l E Y (C.X (i + r)) n V x' = x := by
    dsimp only [integralComparisonRestrictedSection, x']
    erw [cast_cast, cast_eq]
  have h := (hgen (C⟦r⟧) n i U.unop x').trans
    (hgen C n (i + r) U.unop x').symm
  change ((((D.restricted (C⟦r⟧)).hom.app (op n)).f i).val.app U)
      (integralComparisonRestrictedSection l E Y (C.X (i + r)) n V x') =
    ((((D.restricted C).hom.app (op n)).f (i + r)).val.app U)
      (integralComparisonRestrictedSection l E Y (C.X (i + r)) n V x') at h
  rw [hx] at h
  exact h

private theorem signed_natural
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (S : PodSignedRoosShift A) (hS : S.Laws)
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') (r : ℤ) :
    integralOperationsRoosFunctor.map
      (Functor.whiskerRight a (shiftFunctor (CochainComplex A ℤ) r)) ≫
        (S.comparison C' r).hom =
    (S.comparison C r).hom ≫ (integralOperationsRoosFunctor.map a)⟦r⟧' := by
  rw [roosShift_hom_ext S podNativeRoosShift hS nativeRoos_laws,
    roosShift_hom_ext S podNativeRoosShift hS nativeRoos_laws]
  exact native_signed_natural a r

private theorem restricted_shift
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ) :
    let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
    let R := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
    (D.restricted (C⟦r⟧)).hom ≫
      HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (R.map ((P.commShiftIso r).hom.app C)) ≫
      (podRestrictionShift l E X (P.obj C) r).hom =
    (podReindexTower l E g).map (podRestrictionShift l E Y C r).hom ≫
      (podTowerShift l E g (podRestrictedTower l E C) r).hom ≫
      Functor.whiskerRight (D.restricted C).hom
        (shiftFunctor (CochainComplex (scalarReductionSource l E X) ℤ) r) := by
  exact generic_restricted_shift
    (integralComparisonSequencePullback l E g) (isoReductionIntegralInverse l E g)
    (coefficientSequenceRestriction l E Y) (coefficientSequenceRestriction l E X)
    D.restricted (fun C r n i ↦ by
      rcases n with ⟨n⟩
      exact restricted_shift_f l E g D hgen C r n i) C r

/-- The strict Roos reindexing square commutes with the specified signed shifts.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 0941 and 011G
(blueprint: lem-pod-strict-roos-reindex-shift-s8).
Proof: the restricted generator formula identifies the component in degree i+r
before and after shifting. Apply the Roos functor to that restriction square.
The coordinate laws uniquely determine the target signed Roos map, which is
therefore natural. Paste its naturality square with RoosNaturality and RoosShift;
associativity gives the displayed five-factor identity. -/
theorem podStrictRoosReindexShift
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hnat : PodCompletionReindex.RoosNaturality l E g D)
    (hshift : PodCompletionReindex.RoosShift l E g D)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (hSX : D.shiftTarget.Laws)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ) :
    let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
    let R := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
    let F := isoReductionIntegralComplex l E g
    F.map (integralOperationsRoosFunctor.map (podRestrictionShift l E Y C r).hom) ≫
      F.map (D.shiftSource.comparison (podRestrictedTower l E C) r).hom ≫
      (F.commShiftIso r).hom.app (integralOperationsRoos (podRestrictedTower l E C)) ≫
      ((D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom)⟦r⟧' =
    (D.roos (podRestrictedTower l E (C⟦r⟧))).hom ≫
      integralOperationsRoosFunctor.map (D.restricted (C⟦r⟧)).hom ≫
      integralOperationsRoosFunctor.map
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (R.map ((P.commShiftIso r).hom.app C))) ≫
      integralOperationsRoosFunctor.map (podRestrictionShift l E X (P.obj C) r).hom ≫
      (D.shiftTarget.comparison (podRestrictedTower l E (P.obj C)) r).hom := by
  dsimp only
  have hc := map_triple_eq (scalarRoosFunctor l E X) _ _ _ _ _ _
    (restricted_shift l E g D hgen C r)
  have ha := signed_natural D.shiftTarget hSX (D.restricted C).hom r
  have hb := hnat (podRestrictedTower l E (C⟦r⟧))
    (podShiftTower (podRestrictedTower l E C) r) (podRestrictionShift l E Y C r).hom
  have hd := hshift (podRestrictedTower l E C) r
  simp only [roosMap_eq] at hb hd
  erw [(shiftFunctor (CochainComplex (scalarReductionSource l E X) ℤ) r).map_comp
    (D.roos (podRestrictedTower l E C)).hom
    (integralOperationsRoosFunctor.map (D.restricted C).hom)]
  refine paste_shift_square _ _ _ _ _ _ _ _ _ _
    (integralOperationsRoosFunctor.map
      ((podReindexTower l E g).map (podRestrictionShift l E Y C r).hom))
    (integralOperationsRoosFunctor.map
      (podTowerShift l E g (podRestrictedTower l E C) r).hom)
    (integralOperationsRoosFunctor.map (Functor.whiskerRight (D.restricted C).hom
      (shiftFunctor (CochainComplex (scalarReductionSource l E X) ℤ) r)))
    (D.shiftTarget.comparison ((podReindexTower l E g).obj (podRestrictedTower l E C)) r).hom
    (D.roos (podShiftTower (podRestrictedTower l E C) r)).hom ?_ ?_ ?_ ?_
  · exact hc
  · exact ha
  · exact hb.symm
  · exact hd

end WeilConjectures
