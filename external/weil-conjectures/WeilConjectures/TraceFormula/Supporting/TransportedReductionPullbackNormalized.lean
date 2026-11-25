/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatNormalization
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Normalization after transported integral inverse image.

Source: Stacks 07A4, 06YY and 0941; the inverse-image step of
`lem-trf-transported-reduction-systems-normalized`.
(blueprint: stage3-trf-transported-pullback-normalized)

The proof identifies the actual whole-system inverse image with the
pro-etale inverse-image calculus and transports the normalized transition
adjunctions through its coefficient and evaluation comparisons. -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u c v r w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] coefficientSequenceCommRingSheaf integralCoefficientSheaf
  completedIntegralCoefficientSheafUnrestricted
open CategoryTheory.Limits Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalizedIso {W : Scheme.{t}}
    {A B : coefficientSequenceDerived l E W} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  intro m n h P
  let F := coefficientSequenceDerivedEvaluation l E W m
  let G := coefficientSequenceDerivedEvaluation l E W n
  let U := normalizedDVRRes l E W h
  let τ := coefficientSequenceDerivedTransition l E W h
  constructor
  · intro f g hfg
    apply (cancel_epi (G.map e.hom)).1
    apply (hA h P).1
    simp only [Functor.map_comp]
    change τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map f =
      τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map g
    change τ.app B ≫ U.map f = τ.app B ≫ U.map g at hfg
    rw [← τ.naturality_assoc e.hom, ← τ.naturality_assoc e.hom, hfg]
  · intro f
    obtain ⟨g, hg⟩ := (hA h P).2 (F.map e.hom ≫ f)
    refine ⟨G.map e.inv ≫ g, ?_⟩
    apply (cancel_epi (F.map e.hom)).1
    rw [← Category.assoc, τ.naturality e.hom]
    simp only [Functor.comp_map, Category.assoc, Functor.map_comp]
    rw [← U.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, U.map_id,
      Category.id_comp]
    exact hg

private theorem restrictedMap_smul {R S : Type*} [Ring R] [Ring S]
    (q : R →+* S) (hq : Function.Surjective q) (M N : ModuleCat S)
    (g : (ModuleCat.restrictScalars q).obj M ⟶ (ModuleCat.restrictScalars q).obj N)
    (a : S) (x : M) : g (a • x) = a • g x := by
  obtain ⟨b, rfl⟩ := hq a
  exact g.hom.map_smul b x

private theorem conjugateSquare {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {C₀ D₀ T₀ : B} {C₁ D₁ T₁ : A}
    (c : C₀ ⟶ F.obj C₁) (d : D₀ ⟶ F.obj D₁) (t : T₀ ⟶ F.obj T₁)
    (e₀ : C₀ ≅ T₀) (e₁ : C₁ ≅ T₁) (f₀ : D₀ ≅ T₀) (f₁ : D₁ ≅ T₁)
    (hc : c ≫ F.map e₁.hom = e₀.hom ≫ t)
    (hd : d ≫ F.map f₁.hom = f₀.hom ≫ t) :
    c ≫ F.map (e₁ ≪≫ f₁.symm).hom = (e₀ ≪≫ f₀.symm).hom ≫ d := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [F.map_comp]
  apply (cancel_mono (F.map f₁.hom)).1
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, Category.comp_id]
  rw [hc, hd]
  simp only [Iso.inv_hom_id_assoc]

private theorem presheafSequenceIso {C : Type c} [Category.{v} C]
    (R : (ℕ × C)ᵒᵖ ⥤ RingCat.{r}) (S : ℕ → Cᵒᵖ ⥤ RingCat.{r})
    (φ : ∀ n, S n ⟶ (Prod.sectR n C).op ⋙ R)
    (hq : ∀ n U, Function.Surjective ((φ n).app U).hom)
    (M N : PresheafOfModules.{w} R)
    (e : ∀ n, (PresheafOfModules.pushforward (φ n)).obj M ≅
      (PresheafOfModules.pushforward (φ n)).obj N)
    (he : ∀ {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : M.obj (op (m, U.unop))),
      (e n).hom.app U (M.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) =
        N.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op ((e m).hom.app U x)) :
    ∃ a : M ≅ N, ∀ (A : (ℕ × C)ᵒᵖ) (x : M.obj A),
      a.hom.app A x = (e A.unop.1).hom.app (op A.unop.2) x := by
  let ei (A : (ℕ × C)ᵒᵖ) : M.obj A ≅ N.obj A := by
    let U := op A.unop.2
    let g := ((e A.unop.1).hom.app U).hom
    let gi := ((e A.unop.1).inv.app U).hom
    exact LinearEquiv.toModuleIso
      { toFun := g
        invFun := gi
        left_inv := fun x ↦ congrArg (fun f ↦ f.app U x) (e A.unop.1).hom_inv_id
        right_inv := fun x ↦ congrArg (fun f ↦ f.app U x) (e A.unop.1).inv_hom_id
        map_add' := g.map_add
        map_smul' := fun a x ↦ restrictedMap_smul ((φ A.unop.1).app U).hom
          (hq A.unop.1 U) (M.obj A) (N.obj A) ((e A.unop.1).hom.app U) a x }
  have hn {A B : (ℕ × C)ᵒᵖ} (g : A ⟶ B) (x : M.obj A) :
      (ei B).hom (M.map g x) = N.map g ((ei A).hom x) := by
    change (e B.unop.1).hom.app (op B.unop.2) (M.map g x) =
      N.map g ((e A.unop.1).hom.app (op A.unop.2) x)
    let h : B.unop.1 ≤ A.unop.1 := leOfHom g.unop.1
    have hg : g =
        (Prod.mkHom (homOfLE h) (𝟙 A.unop.2)).op ≫
          (Prod.mkHom (𝟙 B.unop.1) g.unop.2).op := by
      apply Quiver.Hom.unop_inj
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp
    have hv := PresheafOfModules.naturality_apply (e B.unop.1).hom
      g.unop.2.op (M.map (Prod.mkHom (homOfLE h) (𝟙 A.unop.2)).op x)
    change (e B.unop.1).hom.app (op B.unop.2)
        (M.map (Prod.mkHom (𝟙 B.unop.1) g.unop.2).op
          (M.map (Prod.mkHom (homOfLE h) (𝟙 A.unop.2)).op x)) =
      N.map (Prod.mkHom (𝟙 B.unop.1) g.unop.2).op
        ((e B.unop.1).hom.app (op A.unop.2)
          (M.map (Prod.mkHom (homOfLE h) (𝟙 A.unop.2)).op x)) at hv
    refine (congrArg (fun z ↦ (e B.unop.1).hom.app (op B.unop.2) z)
      (M.congr_map_apply hg x)).trans ?_
    refine Eq.trans ?_ (N.congr_map_apply hg
      ((e A.unop.1).hom.app (op A.unop.2) x)).symm
    simpa only [PresheafOfModules.map_comp_apply] using
      hv.trans (congrArg
        (fun z ↦ N.map (Prod.mkHom (𝟙 B.unop.1) g.unop.2).op z)
        (he h (op A.unop.2) x))
  exact ⟨PresheafOfModules.isoMk ei (fun {_ _} g ↦ by ext x; exact hn g x),
    fun _ _ ↦ rfl⟩

private theorem sheafSequenceIso {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (S : ℕ → Sheaf J RingCat.{r})
    (φ : ∀ n, S n ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hq : ∀ n U, Function.Surjective ((φ n).hom.app U).hom)
    (M N : SheafOfModules.{w} R)
    (e : ∀ n, (SheafOfModules.pushforward (φ n)).obj M ≅
      (SheafOfModules.pushforward (φ n)).obj N)
    (he : ∀ {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : M.val.obj (op (m, U.unop))),
      (e n).hom.val.app U (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) =
        N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
          ((e m).hom.val.app U x)) :
    ∃ a : M ≅ N, ∀ (A : (ℕ × C)ᵒᵖ) (x : M.val.obj A),
      a.hom.val.app A x = (e A.unop.1).hom.val.app (op A.unop.2) x := by
  let ep (n : ℕ) :
      (PresheafOfModules.pushforward (F := Prod.sectR n C) (φ n).hom).obj M.val ≅
        (PresheafOfModules.pushforward (F := Prod.sectR n C) (φ n).hom).obj N.val :=
    { hom := (e n).hom.val
      inv := (e n).inv.val
      hom_inv_id := congrArg (fun k ↦ k.val) (e n).hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val) (e n).inv_hom_id }
  obtain ⟨a, ha⟩ := presheafSequenceIso R.obj (fun n ↦ (S n).obj)
    (fun n ↦ (φ n).hom) hq M.val N.val ep he
  exact ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso a, ha⟩

private theorem sheafEqScalarSurj {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (h : R = S) (U : Cᵒᵖ) :
    Function.Surjective ((eqToHom h.symm).hom.app U).hom := by
  cases h
  intro x
  exact ⟨x, rfl⟩

private theorem stripAddTransports {A B : AddCommGrpCat.{w}}
    (ha : A = A) (hb : B = B) (f g : A ⟶ B)
    (h : eqToHom ha ≫ f ≫ eqToHom hb = g) (x : A) : f x = g x := by
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    congrArg (fun k ↦ k x) h

private theorem pushforwardTransitionSection {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [∀ k : ℕ, (Prod.sectR k C).IsContinuous J (coefficientSequenceTopology J)]
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (S : ℕ → Sheaf J RingCat.{r})
    (φ : ∀ k, S k ⟶ ((Prod.sectR k C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    {m n : ℕ} (h : n ≤ m) (q : S m ⟶ S n)
    (τ : SheafOfModules.pushforward (φ m) ⟶
      SheafOfModules.pushforward (φ n) ⋙ SheafOfModules.restrictScalars q)
    (M : SheafOfModules.{w} R) (U : Cᵒᵖ) (x : M.val.obj (op (m, U.unop)))
    (ha : ((SheafOfModules.pushforward (φ m)).obj M).val.presheaf.obj U =
      M.val.presheaf.obj (op (m, U.unop)))
    (hb : ((SheafOfModules.restrictScalars q).obj
      ((SheafOfModules.pushforward (φ n)).obj M)).val.presheaf.obj U =
        M.val.presheaf.obj (op (n, U.unop)))
    (ht : eqToHom ha.symm ≫
      (forget₂ (ModuleCat.{w} ((S m).obj.obj U)) AddCommGrpCat.{w}).map
        ((τ.app M).val.app U) ≫ eqToHom hb =
      M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) :
    (τ.app M).val.app U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  exact stripAddTransports ha.symm hb _ _ ht x

private theorem restrictionSquareSection {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}}
    (q : R ⟶ S) (A B : SheafOfModules.{w} R) (A' B' : SheafOfModules.{w} S)
    (a : A ⟶ (SheafOfModules.restrictScalars q).obj A')
    (b : B ⟶ (SheafOfModules.restrictScalars q).obj B')
    (e : A ≅ B) (e' : A' ≅ B')
    (h : a ≫ (SheafOfModules.restrictScalars q).map e'.hom = e.hom ≫ b)
    (U : Cᵒᵖ) (x : A.val.obj U) :
    e'.hom.val.app U (a.val.app U x) = b.val.app U (e.hom.val.app U x) := by
  exact congrArg (fun k ↦ k.val.app U x) h

private theorem sheafSequenceIsoOfTransitions {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [∀ k : ℕ, (Prod.sectR k C).IsContinuous J (coefficientSequenceTopology J)]
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (S : ℕ → Sheaf J RingCat.{r})
    (φ : ∀ k, S k ⟶ ((Prod.sectR k C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hq : ∀ k U, Function.Surjective ((φ k).hom.app U).hom)
    (q : ∀ {m n : ℕ}, n ≤ m → (S m ⟶ S n))
    (τ : ∀ {m n : ℕ} (h : n ≤ m), SheafOfModules.pushforward (φ m) ⟶
      SheafOfModules.pushforward (φ n) ⋙ SheafOfModules.restrictScalars (q h))
    (ha : ∀ (M : SheafOfModules.{w} R) k U,
      ((SheafOfModules.pushforward (φ k)).obj M).val.presheaf.obj U =
        M.val.presheaf.obj (op (k, U.unop)))
    (hb : ∀ (M : SheafOfModules.{w} R) {m n : ℕ} (h : n ≤ m) U,
      ((SheafOfModules.restrictScalars (q h)).obj
        ((SheafOfModules.pushforward (φ n)).obj M)).val.presheaf.obj U =
          M.val.presheaf.obj (op (n, U.unop)))
    (ht : ∀ (M : SheafOfModules.{w} R) {m n : ℕ} (h : n ≤ m) U,
      eqToHom (ha M m U).symm ≫
        (forget₂ (ModuleCat.{w} ((S m).obj.obj U)) AddCommGrpCat.{w}).map
          (((τ h).app M).val.app U) ≫ eqToHom (hb M h U) =
        M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    (M N : SheafOfModules.{w} R)
    (e : ∀ k, (SheafOfModules.pushforward (φ k)).obj M ≅
      (SheafOfModules.pushforward (φ k)).obj N)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      (τ h).app M ≫ (SheafOfModules.restrictScalars (q h)).map (e n).hom =
        (e m).hom ≫ (τ h).app N) :
    ∃ a : M ≅ N, ∀ (A : (ℕ × C)ᵒᵖ) (x : M.val.obj A),
      a.hom.val.app A x = (e A.unop.1).hom.val.app (op A.unop.2) x := by
  apply sheafSequenceIso J R S φ hq M N e
  intro m n h U x
  have hM := pushforwardTransitionSection J R S φ h (q h) (τ h) M U x
    (ha M m U) (hb M h U) (ht M h U)
  have hN := pushforwardTransitionSection J R S φ h (q h) (τ h) N U
    ((e m).hom.val.app U x) (ha N m U) (hb N h U) (ht N h U)
  have hc := restrictionSquareSection (q h)
    ((SheafOfModules.pushforward (φ m)).obj M)
    ((SheafOfModules.pushforward (φ m)).obj N)
    ((SheafOfModules.pushforward (φ n)).obj M)
    ((SheafOfModules.pushforward (φ n)).obj N)
    ((τ h).app M) ((τ h).app N) (e m) (e n) (he h) U x
  exact (congrArg (fun z ↦ (e n).hom.val.app U z) hM.symm).trans (hc.trans hN)

private theorem sequenceModuleIso (W : Scheme.{t})
    (M N : coefficientSequenceModules l E W)
    (e : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj M ≅
      (coefficientSequenceEvaluation l E W n).obj N)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceTransition l E W h).app M ≫
        (normalizedDVRModuleRes l E W h).map (e n).hom =
      (e m).hom ≫ (coefficientSequenceTransition l E W h).app N) :
    ∃ a : M ≅ N, ∀ (A : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj A),
      a.hom.val.app A x = (e A.unop.1).hom.val.app (op A.unop.2) x := by
  let φ (n : ℕ) := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  have hq (n : ℕ) (U : W.ProEtᵒᵖ) : Function.Surjective ((φ n).hom.app U).hom :=
    sheafEqScalarSurj (coefficientSequenceEvaluationRing_eq l E W n) U
  exact sheafSequenceIsoOfTransitions (Scheme.ProEt.topology W)
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat RingCat)).obj (coefficientSequenceCommRingSheaf l E W))
    (fun k ↦ integralCoefficientSheaf l E W k) φ hq
    (fun {_ _} h ↦ normalizedDVRQuotient l E W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l E W h)
    (fun T k U ↦ coefficientSequenceEvaluationAb_eq l E W T k U)
    (fun T {_ _} h U ↦ coefficientSequenceRestrictedEvaluationAb_eq l E W T h U)
    (fun T {_ _} h U ↦
      (coefficientSequenceTransition_exists l E W h).exists.choose_spec T U) M N e he

private theorem sequenceComplexIso (W : Scheme.{t})
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
          (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (e n).hom =
      (e m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
          (.up ℤ)).app D) : Nonempty (C ≅ D) := by
  classical
  have hm (i : ℤ) := sequenceModuleIso l E W (C.X i) (D.X i)
    (fun n ↦ HomologicalComplex.Hom.isoApp (e n) i)
    (fun h ↦ congrArg (fun f ↦ f.f i) (he h))
  choose a ha using hm
  refine ⟨HomologicalComplex.Hom.isoOfComponents a ?_⟩
  intro i j hij
  ext A x
  change (D.d i j).val.app A ((a i).hom.val.app A x) =
    (a j).hom.val.app A ((C.d i j).val.app A x)
  rw [ha i A, ha j A]
  exact congrArg (fun f ↦ f.val.app (op A.unop.2) x) ((e A.unop.1).hom.comm i j)

/-- The transported pullback of every normalized reduction is normalized.
Source: Stacks 07A4, 06YY and 0941; inverse-image step of the parent proof.
(blueprint: stage3-trf-transported-pullback-normalized)
Proof: identify the specified whole-system pullback with the inverse-image
model of the semilinear coefficient calculus.  The pullback transition formula
expresses each target reduction as the inverse image of the source reduction,
conjugated by the canonical coefficient and finite-evaluation comparisons.
These comparisons are isomorphisms, so the bijection defining normalization
is transported through the conjugation.  This works for arbitrary ambient
derived objects and does not use flatness of quotient-ring maps. -/
theorem transportedReductionSystems_pullback_normalized
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K)) := by
  classical
  intro K
  have := Localization.essSurj
    (DerivedCategory.Q (C := scalarReductionSource l E Y))
      (HomologicalComplex.quasiIso _ (.up ℤ))
  let G := (DerivedCategory.Q (C := scalarReductionSource l E Y)).objPreimage K
  let eG := (DerivedCategory.Q (C := scalarReductionSource l E Y)).objObjPreimageIso K
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) G
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P.X i) := by
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E Y) (P.X i)).symm (hflat i)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let eP : DerivedCategory.Q.obj P ≅ K := asIso (DerivedCategory.Q.map p) ≪≫ eG
  obtain ⟨C, eC, κC, _, hκC⟩ := SY.reductionModel P hP hsite
  obtain ⟨N, κN, hκN, _, hnorm, _, _⟩ :=
    StrictQuotient.quotientExpressionKFlatNormalization l E (𝟙 X) f _hlX _hlX _hlY
      1 (fun _ ↦ P) (fun _ ↦ hP) (fun _ ↦ hsite)
  let a (n : ℕ) := κC n ≪≫ (κN 0 n).symm
  have ha {m n : ℕ} (h : n ≤ m) :
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E Y h)
          (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E Y h).mapHomologicalComplex (.up ℤ)).map (a n).hom =
      (a m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E Y h)
          (.up ℤ)).app (N 0) := by
    exact conjugateSquare
      ((normalizedDVRModuleRes l E Y h).mapHomologicalComplex (.up ℤ))
      _ _ _ (κC m) (κC n) (κN 0 m) (κN 0 n) (hκC m n h) (hκN 0 h)
  obtain ⟨b⟩ := sequenceComplexIso l E Y C (N 0) a ha
  let F := integralComparisonDerivedSequencePullback l E f
  let e : F.obj (SY.reduction.obj K) ≅
      DerivedCategory.Q.obj (StrictQuotient.pull l E f (N 0)) :=
    F.mapIso ((SY.reduction.mapIso eP).symm ≪≫ eC ≪≫ DerivedCategory.Q.mapIso b) ≪≫
      (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app (N 0)
  apply normalizedIso l E e.symm
  exact (hnorm X _ (StrictQuotient.Generated.pullF
    (StrictQuotient.Generated.input 0))).2.1

end WeilConjectures
