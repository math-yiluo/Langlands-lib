/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor

/-! # Ordinary association of strict scalar tensor complexes

Source: Stacks 03D7, 03EK and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private theorem conjugateSection
    {S₀ S₁ D₀ D₁ T₀ T₁ : Type*}
    (a₀ : S₀ → T₀) (a₁ : S₁ → T₁) (ai₀ : T₀ → S₀)
    (d₁ : D₁ → T₁) (di₀ : T₀ → D₀) (di₁ : T₁ → D₁)
    (s : S₁ → S₀) (d : D₁ → D₀) (t : T₁ → T₀) (x : S₁)
    (ht : d (di₁ (a₁ x)) = di₀ (t (d₁ (di₁ (a₁ x)))))
    (hs : s x = ai₀ (t (a₁ x)))
    (hd : d₁ (di₁ (a₁ x)) = a₁ x) (ha : a₀ (ai₀ (t (a₁ x))) = t (a₁ x)) :
    d (di₁ (a₁ x)) = di₀ (a₀ (s x)) := by
  rw [ht, hd, hs, ha]

private theorem conjugateSquareSections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{w}} (q : R ⟶ S)
    {X Y T : SheafOfModules.{w} R} {X' Y' T' : SheafOfModules.{w} S}
    (sx : X ⟶ (SheafOfModules.restrictScalars q).obj X')
    (sy : Y ⟶ (SheafOfModules.restrictScalars q).obj Y')
    (a : X ≅ T) (a' : X' ≅ T') (b : Y ≅ T) (b' : Y' ≅ T')
    (t : ∀ U, T.val.obj U → T'.val.obj U)
    (ha : ∀ U (x : X.val.obj U), HEq (sx.val.app U x)
      (a'.inv.val.app U (t U (a.hom.val.app U x))))
    (hb : ∀ U (x : Y.val.obj U), HEq (sy.val.app U x)
      (b'.inv.val.app U (t U (b.hom.val.app U x)))) :
    (a.hom ≫ b.inv) ≫ sy = sx ≫
      (SheafOfModules.restrictScalars q).map (a'.hom ≫ b'.inv) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact conjugateSection
    (fun z ↦ a'.hom.val.app U z) (fun z ↦ a.hom.val.app U z)
    (fun z ↦ a'.inv.val.app U z) (fun z ↦ b.hom.val.app U z)
    (fun z ↦ b'.inv.val.app U z) (fun z ↦ b.inv.val.app U z)
    (fun z ↦ sx.val.app U z) (fun z ↦ sy.val.app U z) (t U) x
    (eq_of_heq (hb U (b.inv.val.app U (a.hom.val.app U x))))
    (eq_of_heq (ha U x))
    (congrArg (fun f ↦ f.val.app U (a.hom.val.app U x)) b.inv_hom_id)
    (congrArg (fun f ↦ f.val.app U (t U (a.hom.val.app U x))) a'.inv_hom_id)

private theorem restrictedMap_smul {R S : Type*} [Ring R] [Ring S]
    (q : R →+* S) (hq : Function.Surjective q) (M N : ModuleCat S)
    (g : (ModuleCat.restrictScalars q).obj M ⟶ (ModuleCat.restrictScalars q).obj N)
    (a : S) (x : M) : g (a • x) = a • g x := by
  obtain ⟨b, rfl⟩ := hq a
  exact g.hom.map_smul b x

private theorem presheafSequenceIso {C : Type c} [Category.{v} C]
    (R : (ℕ × C)ᵒᵖ ⥤ RingCat.{w}) (S : ℕ → Cᵒᵖ ⥤ RingCat.{w})
    (φ : ∀ n, S n ⟶ (Prod.sectR n C).op ⋙ R)
    (hq : ∀ n U, Function.Surjective ((φ n).app U).hom)
    (M N : PresheafOfModules.{w} R)
    (e : ∀ n, (PresheafOfModules.pushforward (φ n)).obj M ≅
      (PresheafOfModules.pushforward (φ n)).obj N)
    (hs : ∀ (n : ℕ) (U : Cᵒᵖ) (x : M.obj (op (n + 1, U.unop))),
      (e n).hom.app U (M.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x) =
        N.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
          ((e (n + 1)).hom.app U x)) :
    ∃ a : M ≅ N, ∀ (A : (ℕ × C)ᵒᵖ) (x : M.obj A),
      a.hom.app A x = (e A.unop.1).hom.app (op A.unop.2) x := by
  have hc (Z : PresheafOfModules.{w} R) {m n : ℕ} (h : n ≤ m)
      (U : Cᵒᵖ) (x : Z.obj (op (m + 1, U.unop))) :
      Z.map (Prod.mkHom (homOfLE (h.trans (Nat.le_succ m))) (𝟙 U.unop)).op x =
        Z.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
          (Z.map (Prod.mkHom (homOfLE (Nat.le_succ m)) (𝟙 U.unop)).op x) := by
    have hg : (Prod.mkHom (homOfLE (h.trans (Nat.le_succ m))) (𝟙 U.unop)).op =
        (Prod.mkHom (homOfLE (Nat.le_succ m)) (𝟙 U.unop)).op ≫
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
      apply Quiver.Hom.unop_inj
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp
    exact (Z.congr_map_apply hg x).trans (Z.map_comp_apply _ _ x)
  have he {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : M.obj (op (m, U.unop))) :
      (e n).hom.app U (M.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) =
        N.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op ((e m).hom.app U x) := by
    induction m, h using Nat.le_induction with
    | base => exact PresheafOfModules.naturality_apply (e n).hom (𝟙 U) x
    | succ m h ih =>
      rw [hc M h U x, hc N h U ((e (m + 1)).hom.app U x), ih, hs]
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
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{w})
    (S : ℕ → Sheaf J RingCat.{w})
    (φ : ∀ n, S n ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hq : ∀ n U, Function.Surjective ((φ n).hom.app U).hom)
    (M N : SheafOfModules.{w} R)
    (e : ∀ n, (SheafOfModules.pushforward (φ n)).obj M ≅
      (SheafOfModules.pushforward (φ n)).obj N)
    (he : ∀ (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj (op (n + 1, U.unop))),
      (e n).hom.val.app U
          (M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x) =
        N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
          ((e (n + 1)).hom.val.app U x)) :
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
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{w}} (h : R = S) (U : Cᵒᵖ) :
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
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{w})
    (S : ℕ → Sheaf J RingCat.{w})
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
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{w}}
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
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{w})
    (S : ℕ → Sheaf J RingCat.{w})
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
    (he : ∀ n : ℕ,
      (τ (Nat.le_succ n)).app M ≫
          (SheafOfModules.restrictScalars (q (Nat.le_succ n))).map (e n).hom =
        (e (n + 1)).hom ≫ (τ (Nat.le_succ n)).app N) :
    ∃ a : M ≅ N, ∀ (A : (ℕ × C)ᵒᵖ) (x : M.val.obj A),
      a.hom.val.app A x = (e A.unop.1).hom.val.app (op A.unop.2) x := by
  apply sheafSequenceIso J R S φ hq M N e
  intro n U x
  let m := n + 1
  let h := Nat.le_succ n
  have hM := pushforwardTransitionSection J R S φ h (q h) (τ h) M U x
    (ha M m U) (hb M h U) (ht M h U)
  have hN := pushforwardTransitionSection J R S φ h (q h) (τ h) N U
    ((e m).hom.val.app U x) (ha N m U) (hb N h U) (ht N h U)
  have hc := restrictionSquareSection (q h)
    ((SheafOfModules.pushforward (φ m)).obj M)
    ((SheafOfModules.pushforward (φ m)).obj N)
    ((SheafOfModules.pushforward (φ n)).obj M)
    ((SheafOfModules.pushforward (φ n)).obj N)
    ((τ h).app M) ((τ h).app N) (e m) (e n) (he n) U x
  exact (congrArg (fun z ↦ (e n).hom.val.app U z) hM.symm).trans (hc.trans hN)

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

section Glue
attribute [local irreducible] coefficientSequenceCommRingSheaf integralCoefficientSheaf
  completedIntegralCoefficientSheafUnrestricted

private theorem sequence_hom_ext {X Y : coefficientSequenceModules l L W}
    (f g : X ⟶ Y)
    (h : ∀ n, (coefficientSequenceEvaluation l L W n).map f =
      (coefficientSequenceEvaluation l L W n).map g) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun f ↦ (f.val.app (op U.unop.2)) x) (h U.unop.1)

private theorem sequenceIsoOfSuccessor
    (X Y : coefficientSequenceModules l L W)
    (a : ∀ n, (coefficientSequenceEvaluation l L W n).obj X ≅
      (coefficientSequenceEvaluation l L W n).obj Y)
    (ha : ∀ n, (a (n + 1)).hom ≫
        (coefficientSequenceTransition l L W (Nat.le_succ n)).app Y =
      (coefficientSequenceTransition l L W (Nat.le_succ n)).app X ≫
        (normalizedDVRModuleRes l L W (Nat.le_succ n)).map (a n).hom) :
    ∃ b : X ≅ Y, ∀ n, (coefficientSequenceEvaluation l L W n).map b.hom = (a n).hom := by
  let φ (n : ℕ) := eqToHom (coefficientSequenceEvaluationRing_eq l L W n).symm
  have hq (n : ℕ) (U : W.ProEtᵒᵖ) : Function.Surjective ((φ n).hom.app U).hom :=
    sheafEqScalarSurj (coefficientSequenceEvaluationRing_eq l L W n) U
  obtain ⟨b, hb⟩ := sheafSequenceIsoOfTransitions (Scheme.ProEt.topology W)
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat RingCat)).obj (coefficientSequenceCommRingSheaf l L W))
    (fun k ↦ integralCoefficientSheaf l L W k) φ hq
    (fun {_ _} h ↦ normalizedDVRQuotient l L W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l L W h)
    (fun T k U ↦ coefficientSequenceEvaluationAb_eq l L W T k U)
    (fun T {_ _} h U ↦ coefficientSequenceRestrictedEvaluationAb_eq l L W T h U)
    (fun T {_ _} h U ↦
      (coefficientSequenceTransition_exists l L W h).exists.choose_spec T U)
    X Y a (fun n ↦ (ha n).symm)
  refine ⟨b, ?_⟩
  intro n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact hb (op (n, U.unop)) x

private theorem successor_square
    (X Y : coefficientSequenceModules l L W)
    (T : ∀ n, normalizedDVRModules l L W n)
    (a : ∀ n, (coefficientSequenceEvaluation l L W n).obj X ≅ T n)
    (b : ∀ n, (coefficientSequenceEvaluation l L W n).obj Y ≅ T n)
    (t : ∀ n (U : W.ProEtᵒᵖ), (T (n + 1)).val.obj U → (T n).val.obj U)
    (ha : ∀ n U (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj X).val.obj U),
      HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app X).val.app U x)
        ((a n).inv.val.app U (t n U ((a (n + 1)).hom.val.app U x))))
    (hb : ∀ n U (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj Y).val.obj U),
      HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app Y).val.app U x)
        ((b n).inv.val.app U (t n U ((b (n + 1)).hom.val.app U x)))) (n : ℕ) :
    ((a (n + 1)).hom ≫ (b (n + 1)).inv) ≫
        (coefficientSequenceTransition l L W (Nat.le_succ n)).app Y =
      (coefficientSequenceTransition l L W (Nat.le_succ n)).app X ≫
        (normalizedDVRModuleRes l L W (Nat.le_succ n)).map ((a n).hom ≫ (b n).inv) := by
  exact conjugateSquareSections (normalizedDVRQuotient l L W (Nat.le_succ n))
    ((coefficientSequenceTransition l L W (Nat.le_succ n)).app X)
    ((coefficientSequenceTransition l L W (Nat.le_succ n)).app Y)
    (a (n + 1)) (a n) (b (n + 1)) (b n) (t n) (ha n) (hb n)

private theorem complexIsoOfSuccessor
    {I : Type*} [Category I]
    (F G : I ⥤ CochainComplex (coefficientSequenceModules l L W) ℤ)
    (a : ∀ n, F ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      G ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ))
    (ha : ∀ P n i, ((a (n + 1)).hom.app P).f i ≫
        (coefficientSequenceTransition l L W (Nat.le_succ n)).app ((G.obj P).X i) =
      (coefficientSequenceTransition l L W (Nat.le_succ n)).app ((F.obj P).X i) ≫
        (normalizedDVRModuleRes l L W (Nat.le_succ n)).map
          (((a n).hom.app P).f i)) :
    ∃ b : F ≅ G, ∀ P n,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).map
        (b.hom.app P) = (a n).hom.app P := by
  classical
  have hb (P : I) (i : ℤ) := sequenceIsoOfSuccessor l L W
    ((F.obj P).X i) ((G.obj P).X i)
    (fun n ↦ HomologicalComplex.Hom.isoApp ((a n).app P) i) (fun n ↦ ha P n i)
  choose b hb using hb
  let e (P : I) : F.obj P ≅ G.obj P :=
    HomologicalComplex.Hom.isoOfComponents (b P) (by
      intro i j hij
      apply sequence_hom_ext l L W
      intro n
      rw [Functor.map_comp, Functor.map_comp, hb P i n, hb P j n]
      exact ((a n).hom.app P).comm i j)
  let β : F ≅ G := NatIso.ofComponents e (by
    intro P Q f
    apply HomologicalComplex.hom_ext
    intro i
    apply sequence_hom_ext l L W
    intro n
    simp only [HomologicalComplex.comp_f, e,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Functor.map_comp, hb]
    exact congrArg (fun f ↦ f.f i) ((a n).hom.naturality f))
  refine ⟨β, ?_⟩
  intro P n
  apply HomologicalComplex.hom_ext
  intro i
  exact hb P i n

end Glue

attribute [local irreducible] integralScalarReduction

/-- Ordinary tensor association glues over the strict sequence site.

Source: Stacks sites-modules.tex, tensor/restriction adjunction (03D7),
tensor products (03EK), and sites-cohomology.tex, inverse systems (0941);
step 3 of stage3-pur-extension-strict-derived-comparison.
(blueprint: stage3-pur-extension-ordinary-association-chain).

Proof: at level n compose scalar evaluation rho, the termwise scalar extension
of M.evaluation n, and the given balanced association. These give the indicated
finite chain isomorphisms. The unit equation for rho identifies its action on
local scalar tensors with the identity on b tensor x. M.transition and the
balanced formula hassociation then identify the transported successor map with
the actual quotient tensor transition. The hypothesis htransition gives that
same map for direct. Thus these finite isomorphisms commute with every successor;
composition gives the equality for every arrow of the natural-number poset.
View modules on the sequence site as strict systems. The finite maps and their
inverses define inverse system maps degreewise; they commute with the cochain
differentials by naturality of tensor association. They therefore define the
chain isomorphism beta. Naturality in the input complex follows levelwise in the
ordinary module category, whose evaluations are jointly faithful. The displayed
equation is exactly its construction. This argument contains no derived functor
or derived comparison, and works for zero complexes and ramified inclusions. -/
theorem coefficientExtensionOrdinaryAssociationChain
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (htransition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation) :
    letI := coefficientScalarModelZero A.scalar
    ∃ β : (integralOperationsGoodComplex l E W).ι ⋙ M.quotient l E W ⋙
        A.scalar.model.E.mapHomologicalComplex (.up ℤ) ≅ direct,
      ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
        letI := coefficientExtensionSystemEvaluationZero l E L ι W A n
        letI := coefficientExtensionEvaluationFiniteZero l E L ι W A n
        ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).map
              (β.hom.app P) ≫ (directEvaluation n).hom.app P =
          (NatIso.mapHomologicalComplex (ρ n) (.up ℤ)).hom.app
              ((M.quotient l E W).obj P.obj) ≫
            ((A.levels n).model.E.mapHomologicalComplex (.up ℤ)).map
              ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P.obj) ≫
            coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj
      := by
  classical
  let := coefficientScalarModelZero A.scalar
  let F := (integralOperationsGoodComplex l E W).ι ⋙ M.quotient l E W ⋙
    A.scalar.model.E.mapHomologicalComplex (.up ℤ)
  let a₀ (n : ℕ) := Functor.isoWhiskerLeft M.tensor (ρ n) ≪≫
    Functor.isoWhiskerRight (M.evaluation n) (A.levels n).model.E ≪≫ association n
  let a (n : ℕ) : F ⋙
        (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n :=
    NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (a₀ n).app (P.obj.X i)) (by
        intro i j hij
        exact ((a₀ n).hom.naturality (P.obj.d i j)).symm)) (by
      intro P Q f
      apply HomologicalComplex.hom_ext
      intro i
      exact (a₀ n).hom.naturality (f.hom.f i))
  let e (n : ℕ) := a n ≪≫ (directEvaluation n).symm
  have hs := coefficientExtensionAssociation_successor l E L ι W A M ρ hρ
    association hassociation
  have he (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) (i : ℤ) :
      ((e (n + 1)).hom.app P).f i ≫
          (coefficientSequenceTransition l L W (Nat.le_succ n)).app ((direct.obj P).X i) =
        (coefficientSequenceTransition l L W (Nat.le_succ n)).app ((F.obj P).X i) ≫
          (normalizedDVRModuleRes l L W (Nat.le_succ n)).map
            (((e n).hom.app P).f i) := by
    exact successor_square l L W ((F.obj P).X i) ((direct.obj P).X i)
      (fun k ↦ ((integralScalarFiniteComplex l E L ι W k).obj P.obj).X i)
      (fun k ↦ HomologicalComplex.Hom.isoApp ((a k).app P) i)
      (fun k ↦ HomologicalComplex.Hom.isoApp ((directEvaluation k).app P) i)
      (fun k U x ↦ (((integralScalarTransition l E L ι W k).app P.obj).f i).val.app U x)
      (fun k U x ↦ hs P.obj k i U x) (fun k U x ↦ htransition P k i U x) n
  obtain ⟨β, hβ⟩ := complexIsoOfSuccessor l L W F direct e he
  refine ⟨β, ?_⟩
  intro P n
  rw [hβ P n]
  change ((a n).hom.app P ≫ (directEvaluation n).inv.app P) ≫
    (directEvaluation n).hom.app P = _
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro i
  unfold coefficientExtensionAssociationChain
  rfl

end WeilConjectures
