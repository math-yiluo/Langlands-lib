/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels

/-! # Assembling maps of coefficient systems from their finite evaluations

Source: Stacks Project, Tags 03CZ and 0941.

A family of maps between the finite evaluations of two modules on the ringed sequence
site, compatible with the strict transition maps, assembles to a unique map of modules
on the sequence site. Maps of modules on the sequence site are determined by their
finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
universe t u r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.OrdinaryReductionTensor
namespace GeneralAssembly
universe c v
variable {T : Type c} [Category.{v} T] (J : GrothendieckTopology T)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (S : ℕ → Sheaf J RingCat.{r})

local instance inclusionContinuous (n : ℕ) :
    (Prod.sectR n T).IsContinuous J (coefficientSequenceTopology J) :=
  SemilinearSections.evaluationContinuous.{c, v, max c v} J n

variable (φ : ∀ n : ℕ, S n ≅
  ((Prod.sectR n T).sheafPushforwardContinuous RingCat.{r} J
    (coefficientSequenceTopology J)).obj R)

variable (κ : ∀ {m n : ℕ}, n ≤ m → (S m ⟶ S n))
    (δ : ∀ {m n : ℕ} (h : n ≤ m), (SheafOfModules.pushforward.{r} (φ m).hom) ⟶
      (SheafOfModules.pushforward.{r} (φ n).hom) ⋙ SheafOfModules.restrictScalars (κ h))
    (hδ : ∀ {m n : ℕ} (h : n ≤ m) (M : SheafOfModules.{r} R) (V : Tᵒᵖ),
      HEq (fun x ↦ ((δ h).app M).val.app V x)
        (fun x : M.val.obj (op (m, V.unop)) ↦
          M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    {M N : SheafOfModules.{r} R}
    (d : ∀ n : ℕ, (SheafOfModules.pushforward.{r} (φ n).hom).obj M ⟶
      (SheafOfModules.pushforward.{r} (φ n).hom).obj N)
    (ht : ∀ {m n : ℕ} (h : n ≤ m),
      (δ h).app M ≫ (SheafOfModules.restrictScalars (κ h)).map (d n) =
        d m ≫ (δ h).app N)

/-- Undo a restriction of scalars along a ring isomorphism on a map of modules.
Source: Stacks 03CZ, 0941. -/
def undoRestriction {A B : RingCat.{r}} (φ : A ≅ B)
    {M N : ModuleCat.{r} B}
    (f : (ModuleCat.restrictScalars φ.hom.hom).obj M ⟶
      (ModuleCat.restrictScalars φ.hom.hom).obj N) : M ⟶ N :=
  ModuleCat.ofHom {
    toFun := f
    map_add' := f.hom.map_add
    map_smul' := by
      intro a x
      have h := f.hom.map_smul (φ.inv a) x
      change f (φ.hom (φ.inv a) • x) = φ.hom (φ.inv a) • f x at h
      have hi : φ.hom (φ.inv a) = a :=
        congrArg (fun k : B ⟶ B ↦ k a) φ.inv_hom_id
      simpa only [hi, RingHom.id_apply] using h }

/-- The sectionwise components of the assembled map.
Source: Stacks 03CZ, 0941. -/
@[irreducible] def assemble_app (V : (ℕ × T)ᵒᵖ) :
    M.val.obj V ⟶ N.val.obj V :=
  undoRestriction
    (((CategoryTheory.evaluation Tᵒᵖ RingCat.{r}).obj (op V.unop.2)).mapIso
      ((sheafToPresheaf J RingCat.{r}).mapIso (φ V.unop.1)))
    ((d V.unop.1).val.app (op V.unop.2))

/-- The sectionwise components of the assembled map on sections.
Source: Stacks 03CZ, 0941. -/
theorem assemble_app_apply (V : (ℕ × T)ᵒᵖ) (x : M.val.obj V) :
    assemble_app J R S φ d V x = (d V.unop.1).val.app (op V.unop.2) x := by
  unfold assemble_app undoRestriction
  rfl

/-- A square through restriction of scalars, on sections.
Source: Stacks 03CZ, 0941. -/
theorem restriction_square_apply
    {A B : Sheaf J RingCat.{r}} (ψ : A ⟶ B)
    {V W : SheafOfModules.{r} A} {V' W' : SheafOfModules.{r} B}
    (a : V ⟶ (SheafOfModules.restrictScalars ψ).obj V')
    (b : W ⟶ (SheafOfModules.restrictScalars ψ).obj W')
    (f : V ⟶ W) (g : V' ⟶ W')
    (h : a ≫ (SheafOfModules.restrictScalars ψ).map g = f ≫ b)
    (U : Tᵒᵖ) (x : V.val.obj U) :
    g.val.app U (a.val.app U x) = b.val.app U (f.val.app U x) :=
  congrArg (fun k ↦ k.val.app U x) h

/-- Transport of a square of functions along equalities.
Source: Stacks 03CZ, 0941. -/
theorem square_of_functions {A B P Q : Type r}
    (f : A → B) (g : P → Q) (a a' : A → P) (b b' : B → Q)
    (ha : a = a') (hb : b = b') (hs : ∀ x, g (a x) = b (f x)) (x : A) :
    b' (f x) = g (a' x) := by
  rw [← ha, ← hb]
  exact (hs x).symm

include ht hδ in
/-- The assembled components commute with horizontal restriction.
Source: Stacks 03CZ, 0941. -/
theorem horizontal_natural {m n : ℕ} (h : n ≤ m) (V : Tᵒᵖ)
    (x : M.val.obj (op (m, V.unop))) :
    N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
        (assemble_app J R S φ d (op (m, V.unop)) x) =
      assemble_app J R S φ d (op (n, V.unop))
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  rw [assemble_app_apply, assemble_app_apply]
  exact square_of_functions
    (fun y ↦ (d m).val.app V y) (fun y ↦ (d n).val.app V y)
    (fun y ↦ ((δ h).app M).val.app V y)
    (fun y ↦ M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op y)
    (fun y ↦ ((δ h).app N).val.app V y)
    (fun y ↦ N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op y)
    (eq_of_heq (hδ h M V)) (eq_of_heq (hδ h N V))
    (fun y ↦ restriction_square_apply J (κ h)
      ((δ h).app M) ((δ h).app N) (d m) (d n) (ht h) V y) x

include ht hδ in
/-- The map of sequence-site modules assembled from compatible levelwise maps.
Source: Stacks 03CZ, 0941. -/
@[irreducible] def assemble : M ⟶ N where
  val := {
    app := assemble_app J R S φ d
    naturality := by
      intro V Z f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change assemble_app J R S φ d Z (M.val.map f x) =
        N.val.map f (assemble_app J R S φ d V x)
      let a : V ⟶ op (V.unop.1, Z.unop.2) :=
        (Prod.mkHom (𝟙 V.unop.1) f.unop.2).op
      let b : op (V.unop.1, Z.unop.2) ⟶ Z :=
        (Prod.mkHom f.unop.1 (𝟙 Z.unop.2)).op
      have hab : f = a ≫ b := by
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext <;> simp [a, b]
      have hv : assemble_app J R S φ d (op (V.unop.1, Z.unop.2)) (M.val.map a x) =
          N.val.map a (assemble_app J R S φ d V x) := by
        simp only [assemble_app_apply]
        exact PresheafOfModules.naturality_apply (d V.unop.1).val f.unop.2.op x
      rw [hab, M.val.map_comp_apply, N.val.map_comp_apply, ← hv]
      exact (horizontal_natural J R S φ κ δ hδ d ht (leOfHom f.unop.1)
        (op Z.unop.2) (M.val.map a x)).symm }

/-- The assembled map has the prescribed levelwise components.
Source: Stacks 03CZ, 0941. -/
theorem assemble_evaluation (n : ℕ) :
    ((SheafOfModules.pushforward.{r} (φ n).hom)).map (assemble J R S φ κ δ hδ d ht) = d n := by
  unfold assemble
  ext V x
  exact assemble_app_apply J R S φ d (op (n, V.unop)) x

end GeneralAssembly

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Maps of modules on the sequence site are determined by their finite evaluations.
Source: Stacks 0941. -/
theorem coefficientSequence_hom_ext {M N : coefficientSequenceModules l E W} {f g : M ⟶ N}
    (h : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).map f =
      (coefficientSequenceEvaluation l E W n).map g) : f = g := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

/-- Transport of a map of abelian groups along equalities, on elements.
Source: Stacks 03CZ, 0941. -/
theorem transported_ab_map_apply
    {A A' B B' : AddCommGrpCat.{r}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (x' : A') (hx : HEq x x') : HEq (f x) (g x') := by
  cases hA
  cases hB
  cases hx
  apply heq_of_eq
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    congrArg (fun k ↦ k x) h

/-- The strict transition on sections is horizontal restriction.
Source: Stacks 03CZ, 0941. -/
theorem transition_section {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (V : W.ProEtᵒᵖ)
    (x : M.val.obj (op (m, V.unop))) :
    ((coefficientSequenceTransition l E W h).app M).val.app V x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x := by
  have hh := (coefficientSequenceTransition_exists l E W h).exists.choose_spec M V
  have he := transported_ab_map_apply.{max u (t + 1)}
    (coefficientSequenceEvaluationAb_eq l E W M m V)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W M h V)
    _ _ hh x x (HEq.rfl)
  exact eq_of_heq he

/-- The strict transition is horizontal restriction, as functions.
Source: Stacks 03CZ, 0941. -/
theorem transition_functions {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (V : W.ProEtᵒᵖ) :
    HEq (fun x ↦ ((coefficientSequenceTransition l E W h).app M).val.app V x)
      (fun x : M.val.obj (op (m, V.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  exact heq_of_eq (funext (transition_section l E W h M V))

/-- The ring sheaf of the ringed sequence site, with commutativity forgotten.
Source: Stacks 03CZ, 0941. -/
abbrev coefficientRing :=
  ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W))

section Assembly
variable {M N : coefficientSequenceModules l E W}
  (d : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj M ⟶
    (coefficientSequenceEvaluation l E W n).obj N)
  (ht : ∀ {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app M ≫
      (normalizedDVRModuleRes l E W h).map (d n) =
    d m ≫ (coefficientSequenceTransition l E W h).app N)

include d ht in
/-- The map of sequence-site modules assembled from compatible finite evaluations.
Source: Stacks 03CZ, 0941. -/
@[irreducible] def coefficientSequenceAssemble : M ⟶ N :=
  GeneralAssembly.assemble (Scheme.ProEt.topology W) (coefficientRing l E W)
    (integralCoefficientSheaf l E W)
    (fun n ↦ eqToIso (coefficientSequenceEvaluationRing_eq l E W n).symm)
    (fun {_ _} h ↦ normalizedDVRQuotient l E W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l E W h)
    (fun {_ _} h M V ↦ transition_functions l E W h M V) d ht

/-- The assembled map has the prescribed finite evaluations.
Source: Stacks 0941. -/
theorem coefficientSequenceAssemble_evaluation (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).map (coefficientSequenceAssemble l E W d ht) = d n := by
  unfold coefficientSequenceAssemble
  exact GeneralAssembly.assemble_evaluation
    (Scheme.ProEt.topology W) (coefficientRing l E W)
    (integralCoefficientSheaf l E W)
    (fun k ↦ eqToIso (coefficientSequenceEvaluationRing_eq l E W k).symm)
    (fun {_ _} h ↦ normalizedDVRQuotient l E W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l E W h)
    (fun {_ _} h M V ↦ transition_functions l E W h M V) d ht n

end Assembly
end WeilConjectures.OrdinaryReductionTensor
