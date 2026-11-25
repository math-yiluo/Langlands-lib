/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # A whole-system integral diagonal coefficient family

Source: sk-thm-int-restriction-line.proof.md, paragraph (1).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u uC
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
private theorem towerGrothendieck (A : Type*) [Category A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] :
    IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

variable (ℓ : ℕ) [Fact ℓ.Prime]

@[irreducible] private def localizations (X : Scheme.{u}) : DiagonalTraceLocalizations ℓ X := by
  let : IsGrothendieckAbelian.{u + 1} (DiagonalAb X) := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (DiagonalMod ℓ X) := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (DiagonalCompleted ℓ X) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  let : IsGrothendieckAbelian.{u + 1} (DiagonalSystems ℓ X) :=
    towerGrothendieck (DiagonalMod ℓ X)
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb X) :=
    towerGrothendieck (DiagonalAb X)
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X) :=
    towerGrothendieck (DiagonalCompleted ℓ X)
  exact {
    ab := HasDerivedCategory.ofIsGrothendieckAbelian _
    mod := HasDerivedCategory.ofIsGrothendieckAbelian _
    systems := HasDerivedCategory.ofIsGrothendieckAbelian _
    abSystems := HasDerivedCategory.ofIsGrothendieckAbelian _
    completed := HasDerivedCategory.ofIsGrothendieckAbelian _
    completedSystems := HasDerivedCategory.ofIsGrothendieckAbelian _
    ext := IsGrothendieckAbelian.hasExt _ }

-- Extract the unique arrow of the compatibility clause.
private theorem selectEquation
    {Z : Sort*} {p q r s t : Prop} {f : Z → Prop}
    (h : p ∧ q ∧ r ∧ s ∧ (∃! z, f z) ∧ t) : ∃ z, f z := by
  obtain ⟨z, hz, -⟩ := h.2.2.2.2.1
  exact ⟨z, hz⟩

-- Move the completed arrow outside the dependent presentation in abstract logic.
-- Keeping the witness types abstract avoids repeated reduction of sheaf categories.
-- The first three predicates are finite-system conditions; the next two normalize cones.
private theorem selectPresentation
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {E : ∀ a b c, D a b c → Sort*}
    {F : ∀ a b c d, E a b c d → Sort*}
    {G : ∀ a b c d e, F a b c d e → Sort*}
    {H : ∀ a b c d e f, G a b c d e f → Sort*}
    {I : ∀ a b c d e f g, H a b c d e f g → Sort*} {Z : Sort*} {Result : Prop}
    {p q r : ∀ a b c d, E a b c d → Prop}
    {s t v : ∀ a b c d e f g h, I a b c d e f g h → Prop}
    {w : ∀ a b c d e f g h, I a b c d e f g h → Z → Prop}
    (convert : ∀ a b c d e f g h i, v a b c d e f g h i →
      ∃ z, w a b c d e f g h i z)
    (data : ∃ a b c d e, p a b c d e ∧ q a b c d e ∧ r a b c d e ∧
      ∃ f g h i, s a b c d e f g h i ∧ t a b c d e f g h i ∧ v a b c d e f g h i)
    (conclude : ∀ z, (∃ a b c d e, p a b c d e ∧ q a b c d e ∧ r a b c d e ∧
      ∃ f g h i, (s a b c d e f g h i ∧ t a b c d e f g h i ∧ v a b c d e f g h i) ∧
        w a b c d e f g h i z) →
      Result) : Result := by
  obtain ⟨a, b, c, d, e, hp, hq, hr, f, g, h, i, hs, ht, hv⟩ := data
  obtain ⟨z, hz⟩ := convert a b c d e f g h i hv
  exact conclude z ⟨a, b, c, d, e, hp, hq, hr, f, g, h, i, ⟨hs, ht, hv⟩, hz⟩

/-- The coefficient family comes from one completed whole-system diagonal class and
its three normalized traces. Source: diagonal tower coefficients, clauses (1)--(3).
(blueprint: lem-integral-normalized-family). -/
def IntegralFamilyReference (Y : Scheme.{u}) (family : Family ℓ Y) : Prop :=
  ∃ (_hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (aY : DiagonalTraceLocalizations ℓ Y)
    (aP : DiagonalTraceLocalizations ℓ (ProjectiveLine Y))
    (aW : DiagonalTraceLocalizations ℓ (diagonalSurface Y)),
    let := aY
    let := aP
    let := aW
    ∃ δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
      Nonempty (Reference ℓ Y δ family)

/-- Existence of a referenced integral coefficient family over a separated finite-type
base. Source: diagonal tower limit and coefficient extension, paragraph (1).
(blueprint: lem-integral-normalized-family).
Proof: finite type over the field makes Y, its projective line and its self-square
Noetherian. The characteristic assumption makes ell a unit on Y. Choose the localization
sizes furnished by Grothendieck abelianity of the sheaf categories and their strict
system categories. Construct the strict diagonal system, apply the completed limit
statement, and take its unique completed diagonal arrow with all its normalizations.
The coefficient extension theorem supplies the family and its completed reference.
Retain the reference to the completed arrow in IntegralFamilyReference. -/
theorem integralNormalizedFamily_exists
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    ∃ family : Family ℓ Y, IntegralFamilyReference ℓ Y family := by
  have hl : (ℓ : k) ≠ 0 := by
    intro hz
    exact (Fact.out : ringChar k ≠ ℓ)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) hz)
  have hY : IsUnit (ℓ : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hl).map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop).hom)
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsNoetherian (ProjectiveLine Y) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y ↘ Y)
  have : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let aY := localizations ℓ Y
  let aP := localizations ℓ (ProjectiveLine Y)
  let aW := localizations ℓ (diagonalSurface Y)
  refine Exists.elim (exists_diagonalTowerSystem ℓ Y hY) ?_
  intro D hd
  have hcompletion := hd.1
  have hsystem := hd.2
  have hLim := diagonalTower_limit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ) Y hY
    D hcompletion hsystem
  refine selectPresentation (data := hLim)
    (fun _ _ _ _ _ _ _ _ _ hh ↦ selectEquation hh) ?_
  intro δ hlimit
  exact (diagonalTower_coefficients ℓ k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) Y hY D hcompletion hsystem δ (by
      unfold DiagonalTrace.IsDiagonalLimit DiagonalTrace.FiniteCartierNormalization
        DiagonalTrace.FiniteRootNormalization DiagonalTrace.finiteCartierClass
      exact hlimit)).imp
      (fun family hfamily ↦ ⟨hY, aY, aP, aW, δ, hfamily.1⟩)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
