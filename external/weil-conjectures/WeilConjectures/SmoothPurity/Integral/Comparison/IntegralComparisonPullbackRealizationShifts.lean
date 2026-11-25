/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonCanonicalShifts
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonPullbackGeneratorShifts
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Shift compatibility of the normalized pullback realization
Source: Stacks Tags 014E, 0941 and 099N(5).
(blueprint: lem-sf-integral-pullback-realization-shifts). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralDerivedPullback CategoryTheory.Functor.leftAdjoint

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private def composeComparison
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    (Q : A ⥤ B) (R : C ⥤ D) (S : E ⥤ F) (U : A ⥤ C)
    (V : B ⥤ D) (W : D ⥤ F) (Z : C ⥤ E)
    (e : Q ⋙ V ≅ U ⋙ R) (b : R ⋙ W ≅ Z ⋙ S) :
    Q ⋙ (V ⋙ W) ≅ (U ⋙ Z) ⋙ S :=
  (Functor.associator Q V W).symm ≪≫ Functor.isoWhiskerRight e W ≪≫
    Functor.associator U R W ≪≫ Functor.isoWhiskerLeft U b ≪≫
    (Functor.associator U Z S).symm

private theorem composeComparison_commShift
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    [HasShift E ℤ] [HasShift F ℤ]
    (Q : A ⥤ B) (R : C ⥤ D) (S : E ⥤ F) (U : A ⥤ C)
    (V : B ⥤ D) (W : D ⥤ F) (Z : C ⥤ E)
    [Q.CommShift ℤ] [R.CommShift ℤ] [S.CommShift ℤ] [U.CommShift ℤ]
    [V.CommShift ℤ] [W.CommShift ℤ] [Z.CommShift ℤ]
    (e : Q ⋙ V ≅ U ⋙ R) (b : R ⋙ W ≅ Z ⋙ S)
    (he : NatTrans.CommShift e.hom ℤ) (hb : NatTrans.CommShift b.hom ℤ) :
    NatTrans.CommShift (composeComparison Q R S U V W Z e b).hom ℤ := by
  let := he
  let := hb
  dsimp only [composeComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

private theorem composeComparison_hom_app
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    (Q : A ⥤ B) (R : C ⥤ D) (S : E ⥤ F) (U : A ⥤ C)
    (V : B ⥤ D) (W : D ⥤ F) (Z : C ⥤ E)
    (e : Q ⋙ V ≅ U ⋙ R) (b : R ⋙ W ≅ Z ⋙ S) (P : A) :
    (composeComparison Q R S U V W Z e b).hom.app P =
      W.map (e.hom.app P) ≫ b.hom.app (U.obj P) := by
  dsimp only [composeComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]

private def pullbackRoosComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ρ : IntegralComparisonRoosModel l E X) :
    DerivedCategory.Q ⋙ (integralComparisonDerivedSequencePullback l E f ⋙
      coefficientSequenceLimit l E X) ≅
    ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
      integralComparisonSequenceRoosFunctor l E X) ⋙ DerivedCategory.Q :=
  composeComparison DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ))
    (integralComparisonDerivedSequencePullback l E f) (coefficientSequenceLimit l E X)
    (integralComparisonSequenceRoosFunctor l E X)
    (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors
    (integralComparisonRoosBridgeComparison l E X ρ)

private theorem pullbackRoosComparison_hom_app
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ρ : IntegralComparisonRoosModel l E X)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (pullbackRoosComparison l E f ρ).hom.app C =
      (coefficientSequenceLimit l E X).map
        ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (integralComparisonRoosBridge l E X ρ
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).hom := by
  rw [show (pullbackRoosComparison l E f ρ).hom.app C = _ from
    composeComparison_hom_app _ _ _ _ _ _ _ _ _ C]
  rfl

private theorem pullbackRoosComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ρ : IntegralComparisonRoosModel l E X) :
    letI := integralComparisonSequencePullbackShift l E f
    letI := integralComparisonLimitShift l E X
    letI := integralComparisonSequenceRoosShift l E X
    NatTrans.CommShift (pullbackRoosComparison l E f ρ).hom ℤ := by
  let := integralComparisonSequencePullbackShift l E f
  let := integralComparisonLimitShift l E X
  let := integralComparisonSequenceRoosShift l E X
  let := integralComparisonRoosBridge_commShift l E X ρ
  exact composeComparison_commShift _ _ _ _ _ _ _ _ _
    (Functor.instCommShiftCochainComplexIntDerivedCategoryHomMapDerivedCategoryFactors
      (integralComparisonSequencePullback l E f))
    (integralComparisonRoosBridge_commShift l E X ρ)

attribute [local irreducible] pullbackRoosComparison

private theorem shifted_comparison
    {A B C D T : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* T]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift T ℤ]
    (F : A ⥤ B) (Q : C ⥤ A) (Q' : D ⥤ B) (H : B ⥤ T) (K : D ⥤ T)
    [F.CommShift ℤ] [Q.CommShift ℤ] [Q'.CommShift ℤ] [H.CommShift ℤ] [K.CommShift ℤ]
    (τ : Q' ⋙ H ≅ K) [NatTrans.CommShift τ.hom ℤ]
    (P : C) (N : D) (e : F.obj (Q.obj P) ≅ Q'.obj N) (m : ℤ) :
    let em := F.mapIso ((Q.commShiftIso m).app P) ≪≫
      (F.commShiftIso m).app (Q.obj P) ≪≫ (shiftFunctor B m).mapIso e ≪≫
      ((Q'.commShiftIso m).app N).symm
    (F ⋙ H).map ((Q.commShiftIso m).hom.app P) ≫
        ((F ⋙ H).commShiftIso m).hom.app (Q.obj P) ≫
        (H.map e.hom ≫ τ.hom.app N)⟦m⟧' =
      H.map em.hom ≫ τ.hom.app (N⟦m⟧) ≫ (K.commShiftIso m).hom.app N := by
  dsimp only
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [← NatTrans.shift_app_comm τ.hom m N]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
  simp only [Iso.app_inv, ← H.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [H.map_comp, Category.assoc]
  rw [← H.commShiftIso_hom_naturality_assoc e.hom m]
  erw [H.map_id, Category.id_comp]

private theorem shifted_postcomparison
    {A B C D T : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* T]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift T ℤ]
    (F : A ⥤ B) (Q : C ⥤ A) (Q' : D ⥤ B) (H : B ⥤ T) (K : D ⥤ T)
    (Z : C ⥤ T)
    [F.CommShift ℤ] [Q.CommShift ℤ] [Q'.CommShift ℤ] [H.CommShift ℤ] [K.CommShift ℤ]
    [Z.CommShift ℤ]
    (τ : Q' ⋙ H ≅ K) [NatTrans.CommShift τ.hom ℤ]
    (P : C) (N : D) (e : F.obj (Q.obj P) ≅ Q'.obj N) (m : ℤ)
    (a : K.obj N ⟶ Z.obj P) (am : K.obj (N⟦m⟧) ⟶ Z.obj (P⟦m⟧))
    (ha : am ≫ (Z.commShiftIso m).hom.app P =
      (K.commShiftIso m).hom.app N ≫ a⟦m⟧') :
    let em := F.mapIso ((Q.commShiftIso m).app P) ≪≫
      (F.commShiftIso m).app (Q.obj P) ≪≫ (shiftFunctor B m).mapIso e ≪≫
      ((Q'.commShiftIso m).app N).symm
    (F ⋙ H).map ((Q.commShiftIso m).inv.app P) ≫
      (H.map em.hom ≫ τ.hom.app (N⟦m⟧) ≫ am) ≫ (Z.commShiftIso m).hom.app P =
    ((F ⋙ H).commShiftIso m).hom.app (Q.obj P) ≫
      (H.map e.hom ≫ τ.hom.app N ≫ a)⟦m⟧' := by
  dsimp only
  have h := shifted_comparison F Q Q' H K τ P N e m
  have h' := congrArg (fun z ↦ z ≫ a⟦m⟧') h
  simp only [Functor.map_comp, Category.assoc] at h' ⊢
  rw [← ha] at h'
  apply (cancel_epi ((F ⋙ H).map ((Q.commShiftIso m).hom.app P))).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  rw [(F ⋙ H).map_id, Category.id_comp]
  simpa only [Functor.map_comp, Category.assoc] using h'.symm

private theorem localized_shift_square
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ C) (J : B ⥤ C) (Q : C ⥤ D)
    [F.CommShift ℤ] [J.CommShift ℤ] [Q.CommShift ℤ]
    (P : A) (N : B) (m : ℤ) (a : J.obj N ⟶ F.obj P)
    (am : J.obj (N⟦m⟧) ⟶ F.obj (P⟦m⟧))
    (h : am ≫ (F.commShiftIso m).hom.app P =
      (J.commShiftIso m).hom.app N ≫ a⟦m⟧') :
    Q.map am ≫ ((F ⋙ Q).commShiftIso m).hom.app P =
      ((J ⋙ Q).commShiftIso m).hom.app N ≫ (Q.map a)⟦m⟧' := by
  simp only [Functor.commShiftIso_comp_hom_app]
  rw [← Q.map_comp_assoc, h, Q.map_comp, Category.assoc,
    Q.commShiftIso_hom_naturality]
  simp only [Category.assoc]

private theorem map_comp_eq
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X Y Z : A} (a : X ⟶ Y) (b : Y ⟶ Z) (d : X ⟶ Z) (h : a ≫ b = d) :
    F.map a ≫ F.map b = F.map d :=
  (F.map_comp a b).symm.trans (congrArg F.map h)

private theorem cancel_shift_square
    {A : Type*} [Category* A]
    {F₀ G₀ F₁ G₁ T₁ F₂ G₂ T₂ : A}
    (αm : F₁ ⟶ G₁) (bm : G₁ ⟶ T₁) (δm : F₁ ⟶ T₁)
    (αs : F₂ ⟶ G₂) (bs : G₂ ⟶ T₂) (δs : F₂ ⟶ T₂)
    (fr : F₀ ⟶ F₁) (gr : G₀ ⟶ G₁) (t : T₁ ⟶ T₂)
    (α' : F₀ ⟶ G₀) (fs : F₀ ⟶ F₂) (gs : G₀ ⟶ G₂)
    (hb : IsIso bs) (hnm : αm ≫ bm = δm)
    (hshift : αs ≫ bs = δs)
    (hs : fs ≫ δs = fr ≫ δm ≫ t)
    (hp : gr ≫ bm ≫ t = gs ≫ bs)
    (hnatur : fr ≫ αm = α' ≫ gr) :
    fs ≫ αs = α' ≫ gs := by
  let := hb
  apply (cancel_mono bs).1
  simp only [Category.assoc]
  rw [hshift, hs, ← hnm]
  simp only [Category.assoc]
  rw [← Category.assoc fr αm, hnatur]
  simp only [Category.assoc]
  rw [hp]

private theorem normalize_associated
    {A : Type*} [Category* A] {X₀ X₁ X₂ X₃ X₄ X₅ : A}
    (α : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) (δ : X₀ ⟶ X₅)
    (h : α ≫ a ≫ b ≫ c ≫ d = δ) :
    α ≫ (a ≫ (b ≫ c) ≫ d) = δ := by
  simpa only [Category.assoc] using h

attribute [-instance] IntegralCompletedComparison.products
  IntegralCompletedComparison.complexProducts in
private def postcomparisonIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj
          C)).asFunctor ≅ (integralOperationsPullbackTowerFunctor l E f).obj P) :=
  ((integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E X).mapIso
    e) ≪≫ (pullbackRoosComparison l E f ρ).app C ≪≫
      DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso q)

attribute [-instance] IntegralCompletedComparison.products
  IntegralCompletedComparison.complexProducts in
private theorem postcomparisonIso_hom
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj
          C)).asFunctor ≅ (integralOperationsPullbackTowerFunctor l E f).obj P) :
    (postcomparisonIso l E f S ρ P C e q).hom =
      (integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E X).map
          e.hom ≫ (pullbackRoosComparison l E f ρ).hom.app C ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) := by
  rfl

attribute [local irreducible] postcomparisonIso

private def commShiftApp {B C : Type*} [Category* B] [Category* C] [HasShift B ℤ]
    [HasShift C ℤ] (F : B ⥤ C) [F.CommShift ℤ] (m : ℤ) (X : B) :
    F.obj (X⟦m⟧) ⟶ (F.obj X)⟦m⟧ :=
  (F.commShiftIso m).hom.app X

private def natApp {B C : Type*} [Category* B] [Category* C] {F G : B ⥤ C} (α : F ⟶ G)
    (X : B) : F.obj X ⟶ G.obj X :=
  α.app X

private def shiftMap {C : Type*} [Category* C] [HasShift C ℤ] (m : ℤ) {X Y : C}
    (f : X ⟶ Y) : X⟦m⟧ ⟶ Y⟦m⟧ :=
  f⟦m⟧'

private def SquareEq {C : Type*} [Category* C] {X Y Z W : C} (a : X ⟶ Y) (b : Y ⟶ W)
    (c : X ⟶ Z) (d : Z ⟶ W) : Prop :=
  a ≫ b = c ≫ d

private theorem commShift_of_localization
    {A A' B C : Type*} [Category* A] [Category* A'] [Category* B] [Category* C]
    [HasShift B ℤ] [HasShift C ℤ]
    (F G : B ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ] (α : F ⟶ G)
    (ι : A ⥤ A') (o : A → A') (hι : ∀ P, ι.obj P = o P) (Q₀ : A' ⥤ B)
    (W : MorphismProperty A) [hQ : (ι ⋙ Q₀).IsLocalization W]
    (h : ∀ (P : A) (m : ℤ),
      SquareEq (commShiftApp F m (Q₀.obj (o P))) (shiftMap m (natApp α (Q₀.obj (o P))))
        (natApp α ((Q₀.obj (o P))⟦m⟧)) (commShiftApp G m (Q₀.obj (o P)))) :
    NatTrans.CommShift α ℤ := by
  constructor
  intro m
  refine Localization.natTrans_ext (ι ⋙ Q₀) W (fun P ↦ ?_)
  have key : ∀ X, X = Q₀.obj (o P) →
      (F.commShiftIso m).hom.app X ≫ (α.app X)⟦m⟧' =
        α.app (X⟦m⟧) ≫ (G.commShiftIso m).hom.app X := by
    rintro X rfl
    exact h P m
  exact key _ (by rw [Functor.comp_obj, hι P])

attribute [-instance] IntegralCompletedComparison.products
  IntegralCompletedComparison.complexProducts in
/-- The representative-normalized pullback realization respects the independently
fixed whole-system shifts.

Source: Stacks Tags 014E, 0941 and 099N(5); the Weil-structures paragraph
of the open-closed triangle proof, expanded in parent node steps 2–7.
(blueprint: lem-sf-integral-pullback-realization-shifts).

Proof: resolve a complex by a flat-term K-flat complex P and take its simultaneous
quotient-system presentation from SY.reductionModel. Shift that presentation
termwise. To identify the reduction shift, first compute the total-limit projection on
an injective replacement and its shift: the degree-j projection is the same
projection in degree j+m. Transpose this equation through the finite scalar
adjunction. Its mate is the finite evaluation comparison of reduction, by
SY.counit_projection; thus that comparison commutes with the adjoint reduction
shift. The universal finite scalar counit identifies its representative shift
with termwise reindexing. Conjugate e[m] by these two localization comparisons
and the reduction shift to present P[m] by C[m]. Define the finite kappa maps
by the termwise shift comparisons. The first presentation equation follows
from the mate equation just proved, and the horizontal one follows by shifting
the old horizontal equation. The
pullback generator x tensor a goes to the same generator in the shifted degree;
thus the normalized presentation map q commutes with shifts and with quotient
transitions. Compute the total-limit comparison on a K-injective replacement of
the restricted tower. The limit-cone insertion is (0,z), so it commutes with the
Roos shift (y,x) to ((-1)^m y,x). The two coordinate equations in hc determine
this same shift on the pullback representative. More explicitly, define q_m
by conjugating q[m] with the exact restriction/pullback termwise shifts. Its
generator equation is the old equation in degree j+m, so M.normalization applies
to this particular q_m after uniqueness on tensor-unit generators. For the Roos
bridge, its equation on injectives follows from rho.computes and the two
coordinates of integralComparisonLimitToRoos: the first is the limit tuple and
the second is zero. Both coordinates agree after the signed shift. Naturality
along an injective replacement gives the bridge equation on the original tower.
Apply M's representative
normalization to P and P[m], and cancel the invertible presentation and Roos
comparison maps. This is the desired square on Q(P), after using hs for the
derived pullback comparison. Naturality along the K-flat resolution and the
essential surjectivity of localization give the square on every derived object. -/
theorem integralComparisonPullbackRealization_commShift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (M : IntegralComparisonPullbackModel l E f SY ρ)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c)
    (s : (integralDerivedPullback l E f).CommShift ℤ)
    (hs : IntegralCompletedComparison.ShiftDescent l E f c s) :
    letI := s
    letI := integralComparisonReductionShift l E Y SY
    letI := integralComparisonSequencePullbackShift l E f
    letI := integralComparisonLimitShift l E X
    NatTrans.CommShift M.realization.hom ℤ := by
  let := c
  let := s
  let := integralComparisonReductionShift l E Y SY
  let := integralComparisonSequencePullbackShift l E f
  let := integralComparisonLimitShift l E X
  let := integralComparisonSequenceRoosShift l E X
  let := integralComparisonRoosBridge_commShift l E X ρ
  let A := integralComparisonSequencePullback l E f
  let D := integralComparisonDerivedSequencePullback l E f
  let L := coefficientSequenceLimit l E X
  let B := integralComparisonSequenceRoosFunctor l E X
  let H : coefficientSequenceDerived l E Y ⥤
      DerivedCategory (integralTowerModules l E X) := D ⋙ L
  let J : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
    A.mapHomologicalComplex (.up ℤ) ⋙ B
  let T : CochainComplex (integralTowerModules l E Y) ℤ ⥤
      DerivedCategory (integralTowerModules l E X) :=
    integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q
  let ψ := pullbackRoosComparison l E f ρ
  have : NatTrans.CommShift ψ.hom ℤ := pullbackRoosComparison_commShift l E f ρ
  refine commShift_of_localization _ _ M.realization.hom (integralOperationsGoodComplex l E Y).ι
    ObjectProperty.FullSubcategory.obj (fun _ ↦ rfl) DerivedCategory.Q
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι)
    (hQ := integralOperationsGoodLocalization_isLocalization l E Y) ?_
  intro P m
  change SquareEq
    (commShiftApp (integralDerivedPullback l E f) m (DerivedCategory.Q.obj P.obj))
    (shiftMap m (natApp M.realization.hom (DerivedCategory.Q.obj P.obj)))
    (natApp M.realization.hom ((DerivedCategory.Q.obj P.obj)⟦m⟧))
    (commShiftApp (SY.reduction ⋙ H) m (DerivedCategory.Q.obj P.obj))
  change ((integralDerivedPullback l E f).commShiftIso m).hom.app
      (DerivedCategory.Q.obj P.obj) ≫
        (M.realization.hom.app (DerivedCategory.Q.obj P.obj))⟦m⟧' =
    M.realization.hom.app ((DerivedCategory.Q.obj P.obj)⟦m⟧) ≫
      ((SY.reduction ⋙ H).commShiftIso m).hom.app (DerivedCategory.Q.obj P.obj)
  obtain ⟨hm, hsP⟩ := hs P m
  obtain ⟨C, e, κ, hp, hcoh⟩ := coherentPrimitiveReductionPresentation l E SY P
  obtain ⟨q, hq, hnorm⟩ := M.normalization P C e κ hp hcoh
  let em := integralComparisonShiftedReductionIso l E Y SY P.obj C e m
  let κm := integralComparisonShiftedFiniteIso l E Y P.obj C κ m
  have hpm := integralComparisonReductionPresentation_shift l E Y SY P C e κ
    hp hcoh m hm
  obtain ⟨qm, hqm, hnormm⟩ := M.normalization ⟨P.obj⟦m⟧, hm⟩ (C⟦m⟧) em κm
    hpm.1 hpm.2
  let a : (J ⋙ DerivedCategory.Q).obj C ⟶ T.obj P.obj :=
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
  let am : (J ⋙ DerivedCategory.Q).obj (C⟦m⟧) ⟶ T.obj (P.obj⟦m⟧) :=
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map qm.hom)
  let β := postcomparisonIso l E f SY ρ P.obj C e q
  let βm := postcomparisonIso l E f SY ρ (P.obj⟦m⟧) (C⟦m⟧) em qm
  let b : (SY.reduction ⋙ H).obj
      ((integralOperationsGoodLocalization l E Y).obj P) ⟶
      (integralOperationsPullbackOnGood l E f).obj P := β.hom
  let bm : (SY.reduction ⋙ H).obj
      ((integralOperationsGoodLocalization l E Y).obj ⟨P.obj⟦m⟧, hm⟩) ⟶
      (integralOperationsPullbackOnGood l E f).obj ⟨P.obj⟦m⟧, hm⟩ := βm.hom
  have hb : IsIso b := β.isIso_hom
  have hn : M.realization.hom.app (DerivedCategory.Q.obj P.obj) ≫ b =
      (integralDerivedPullbackComparison l E f).hom.app P := by
    dsimp only [b, β]
    rw [postcomparisonIso_hom]
    dsimp only [Functor.comp_map, integralComparisonDerivedSequencePullback]
    rw [pullbackRoosComparison_hom_app]
    exact normalize_associated _ _ _ _ _ _ hnorm
  have hnm : M.realization.hom.app (DerivedCategory.Q.obj (P.obj⟦m⟧)) ≫ bm =
      (integralDerivedPullbackComparison l E f).hom.app ⟨P.obj⟦m⟧, hm⟩ := by
    dsimp only [bm, βm]
    rw [postcomparisonIso_hom]
    dsimp only [Functor.comp_map, integralComparisonDerivedSequencePullback]
    rw [pullbackRoosComparison_hom_app]
    exact normalize_associated _ _ _ _ _ _ hnormm
  have hqshift := integralComparisonPullbackGenerator_shift l E f P.obj C κ m q qm
    hq hqm c hc
  have ha : am ≫
      (T.commShiftIso m).hom.app P.obj =
    ((J ⋙ DerivedCategory.Q).commShiftIso m).hom.app C ≫ a⟦m⟧' := by
    exact localized_shift_square (integralOperationsPullbackComplexFunctor l E f) J
      DerivedCategory.Q P.obj C m (integralOperationsRoosFunctor.map q.hom)
      (integralOperationsRoosFunctor.map qm.hom) hqshift
  have hpost' : (SY.reduction ⋙ H).map
      ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫ bm ≫
      (T.commShiftIso m).hom.app P.obj =
    ((SY.reduction ⋙ H).commShiftIso m).hom.app (DerivedCategory.Q.obj P.obj) ≫ b⟦m⟧' := by
    dsimp only [bm, b, βm, β]
    rw [postcomparisonIso_hom, postcomparisonIso_hom]
    dsimp only [em, integralComparisonShiftedReductionIso]
    exact shifted_postcomparison SY.reduction DerivedCategory.Q DerivedCategory.Q H
      (J ⋙ DerivedCategory.Q) T ψ P.obj C e m a am ha
  have hd : ((integralDerivedPullback l E f).commShiftIso m).hom.app
      (DerivedCategory.Q.obj P.obj) ≫
        ((integralDerivedPullbackComparison l E f).hom.app P)⟦m⟧' =
    (integralDerivedPullback l E f).map
        ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
      (integralDerivedPullbackComparison l E f).hom.app ⟨P.obj⟦m⟧, hm⟩ ≫
      (T.commShiftIso m).hom.app P.obj := by
    rw [Functor.commShiftIso_comp_hom_app
      (F := integralOperationsPullbackComplexFunctor l E f) (G := DerivedCategory.Q)]
    exact hsP
  have hnatur₀ : (integralDerivedPullback l E f).map
      ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
        M.realization.hom.app (DerivedCategory.Q.obj (P.obj⟦m⟧)) =
    M.realization.hom.app ((DerivedCategory.Q.obj P.obj)⟦m⟧) ≫
      (SY.reduction ⋙ H).map ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) :=
    M.realization.hom.naturality ((DerivedCategory.Q.commShiftIso m).inv.app P.obj)
  have hshift := map_comp_eq
    (shiftFunctor (DerivedCategory (integralTowerModules l E X)) m)
    (M.realization.hom.app (DerivedCategory.Q.obj P.obj)) b
    ((integralDerivedPullbackComparison l E f).hom.app P) hn
  have hbs : IsIso ((shiftFunctor (DerivedCategory (integralTowerModules l E X)) m).map b) :=
    by let := hb; infer_instance
  exact cancel_shift_square
    (M.realization.hom.app (DerivedCategory.Q.obj (P.obj⟦m⟧))) bm
    ((integralDerivedPullbackComparison l E f).hom.app ⟨P.obj⟦m⟧, hm⟩)
    ((M.realization.hom.app (DerivedCategory.Q.obj P.obj))⟦m⟧') (b⟦m⟧')
    (((integralDerivedPullbackComparison l E f).hom.app P)⟦m⟧')
    ((integralDerivedPullback l E f).map ((DerivedCategory.Q.commShiftIso m).inv.app P.obj))
    ((SY.reduction ⋙ H).map ((DerivedCategory.Q.commShiftIso m).inv.app P.obj))
    ((T.commShiftIso m).hom.app P.obj)
    (M.realization.hom.app ((DerivedCategory.Q.obj P.obj)⟦m⟧))
    (((integralDerivedPullback l E f).commShiftIso m).hom.app
      (DerivedCategory.Q.obj P.obj))
    (((SY.reduction ⋙ H).commShiftIso m).hom.app (DerivedCategory.Q.obj P.obj))
    hbs hnm hshift hd hpost' hnatur₀

end WeilConjectures
