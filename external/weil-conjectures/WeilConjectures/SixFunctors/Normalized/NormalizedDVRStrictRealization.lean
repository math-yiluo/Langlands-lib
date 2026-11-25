/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRCompletedRestrictionCoherence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Strict realization of coherent finite coefficient systems

Source: the strict representative step in the inverse-limit assertion of
proposition-sp-integral-adjunction; Stacks, Derived Categories, lemma-K-injective.
(blueprint: lem-coef-normalized-dvr-strict-realization).
-/

@[expose] public section
set_option autoImplicit false
universe u t d
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

private theorem chainMap_rep
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P J : CochainComplex A ℤ) [J.IsKInjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj J) :
    ∃ a : P ⟶ J, DerivedCategory.Q.map a = f := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) J).surjective
      (e.hom.app P ≫ f ≫ e.inv.app J)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective a
  refine ⟨a, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality a
  rw [ha] at h
  simpa [e] using h.symm

private theorem strictSequence
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] (K : ℕᵒᵖ ⥤ DerivedCategory A) :
    ∃ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ), Nonempty (T ⋙ DerivedCategory.Q ≅ K) := by
  classical
  have hr (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K.obj (op n))
  choose I hI e using hr
  let a (n : ℕ) : DerivedCategory.Q.obj (I n) ≅ K.obj (op n) := (e n).some.symm
  have hl (n : ℕ) : ∃ f : I (n + 1) ⟶ I n,
      DerivedCategory.Q.map f =
        (a (n + 1)).hom ≫ K.map (homOfLE n.le_succ).op ≫ (a n).inv := by
    have := hI n
    exact chainMap_rep _ _ _
  choose f hf using hl
  let T := Functor.ofOpSequence f
  let α : T ⋙ DerivedCategory.Q ⟶ K := NatTrans.ofOpSequence (fun n ↦ (a n).hom)
    (fun n ↦ by simp [T, hf, Category.assoc])
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (a n.unop).hom
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app _
  exact ⟨T, ⟨asIso α⟩⟩

private def transposeTower {A : Type*} [Category A] [HasZeroMorphisms A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := T ⋙ HomologicalComplex.eval A (.up ℤ) i
  d i j :=
    { app := fun n ↦ (T.obj n).d i j
      naturality := fun n m f ↦ (T.map f).comm i j }
  shape i j hij := by
    ext n
    exact (T.obj n).shape i j hij
  d_comp_d' i j k hij hjk := by
    ext n
    exact (T.obj n).d_comp_d i j k

/-- A coherent finite coefficient system admits a derived strict completed-coefficient
realization. This assertion does not impose normalization or identify a limit.

Source: the strict representative step of lem-coef-integral-dualizing-roos-model,
expanded from the inverse-limit paragraph of proposition-sp-integral-adjunction;
Stacks, Derived Categories, lemma-K-injective.
(blueprint: lem-coef-normalized-dvr-strict-realization).

Proof: restrict each finite object to the completed coefficient sheaf. The canonical
restriction-composition comparisons and the two given identities make these objects
an inverse diagram in the derived category. Choose K-injective complexes representing
its objects, using the Grothendieck property of the module-sheaf category. Each successor
morphism is represented by a homotopy class of chain maps into its K-injective target;
choose a chain map in that class. Form the strict inverse sequence from these successor
maps, composing them for longer transitions, and transpose the resulting diagram of
complexes to a complex of diagrams. Localize it to obtain Z. The chosen representative
isomorphisms give e. For successors the required square is the defining equation of
the lifted chain map. The identity case follows from the restriction unit, and induction
on the distance m-n, using the quotient cocycle and restriction-composition coherence,
gives the displayed square for every h. No uniform bound, normalization, or product
exactness is needed. On the empty scheme the same construction is the zero diagram;
identity transitions and constant systems satisfy exactly the same recursion. -/
theorem normalizedDVR_strict_realization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (M : ∀ n : ℕ, normalizedDVRDerived l E X n)
    (tau : ∀ {m n : ℕ} (h : n ≤ m), M m ⟶ (normalizedDVRRes l E X h).obj (M n))
    (hu : ∀ n : ℕ, tau (Nat.le_refl n) ≫
      (normalizedDVRResUnit l E X n).hom.app (M n) = 𝟙 (M n))
    (hc : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      tau (le_trans hmn hrm) ≫ (normalizedDVRResComp l E X hrm hmn).inv.app (M n) =
        tau hrm ≫ (normalizedDVRRes l E X hrm).map (tau hmn)) :
    ∃ (Z : normalizedDVRDerivedTowers l E X D hl)
      (e : ∀ n : ℕ, (normalizedDVRTowerEvaluation l E X D hl n).obj Z ≅
        (normalizedDVRResCompleted l E X D hl n).obj (M n)),
      ∀ {m n : ℕ} (h : n ≤ m),
        (normalizedDVRTowerTransition l E X D hl h).app Z ≫ (e n).hom =
          (e m).hom ≫ (normalizedDVRResCompleted l E X D hl m).map (tau h) ≫
            (normalizedDVRResCompletedComp l E X D hl h).hom.app (M n) := by
  classical
  let := HasDerivedCategory.standard (completedIntegralModuleSheaves l E X D hl)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E X D hl)
  obtain ⟨hunit, hassoc⟩ := normalizedDVR_completedRestriction_coherence l E X D hl
  let R (n : ℕ) := normalizedDVRResCompleted l E X D hl n
  let k {m n : ℕ} (h : n ≤ m) : (R m).obj (M m) ⟶ (R n).obj (M n) :=
    (R m).map (tau h) ≫ (normalizedDVRResCompletedComp l E X D hl h).hom.app (M n)
  have kid (n : ℕ) : k (Nat.le_refl n) = 𝟙 _ := by
    dsimp only [k, R]
    rw [hunit, ← Functor.map_comp, hu, CategoryTheory.Functor.map_id]
  have kcomp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
      k (hmn.trans hrm) = k hrm ≫ k hmn := by
    dsimp only [k, R]
    rw [← hassoc hrm hmn, ← Functor.map_comp_assoc, hc, Functor.map_comp]
    have hn := (normalizedDVRResCompletedComp l E X D hl hrm).hom.naturality (tau hmn)
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, reassoc_of% hn]
    simp only [Category.assoc]
  let K : ℕᵒᵖ ⥤ completedIntegralDerivedCategory l E X D hl :=
    { obj := fun n ↦ (R n.unop).obj (M n.unop)
      map := fun f ↦ k (leOfHom f.unop)
      map_id := fun n ↦ kid n.unop
      map_comp := fun f g ↦ kcomp (leOfHom f.unop) (leOfHom g.unop) }
  let : IsGrothendieckAbelian.{max u (t + 1)} (completedIntegralModuleSheaves l E X D hl) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)).1
  obtain ⟨T, ⟨a⟩⟩ := strictSequence K
  let C := transposeTower T
  let Z : normalizedDVRDerivedTowers l E X D hl := DerivedCategory.Q.obj C
  let ev (n : ℕ) :=
    (evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E X D hl)).obj (op n)
  let e (n : ℕ) : (normalizedDVRTowerEvaluation l E X D hl n).obj Z ≅ (R n).obj (M n) :=
    (ev n).mapDerivedCategoryFactors.app C ≪≫ a.app (op n)
  refine ⟨Z, e, ?_⟩
  intro m n h
  have hf : (normalizedDVRTowerTransition l E X D hl h).app Z ≫
      (ev n).mapDerivedCategoryFactors.hom.app C =
    (ev m).mapDerivedCategoryFactors.hom.app C ≫
      DerivedCategory.Q.map (T.map (homOfLE h).op) := by
    dsimp only [Z, ev, normalizedDVRTowerTransition]
    rw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]
    rfl
  dsimp only [e, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, hf, Category.assoc]
  simpa only [Functor.comp_map, K, k, R, Category.assoc] using
    congrArg (fun f ↦ (ev m).mapDerivedCategoryFactors.hom.app C ≫ f)
      (a.hom.naturality (homOfLE h).op)

end WeilConjectures
