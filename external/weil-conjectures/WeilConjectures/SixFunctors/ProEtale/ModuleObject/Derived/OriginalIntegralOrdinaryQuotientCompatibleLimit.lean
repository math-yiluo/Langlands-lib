/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientCompatibleLimitFinitePresentation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientCompatibleLimitReassembly
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelSeparated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Convergence of integral Cauchy morphisms -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

private theorem lift_sectionwise
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} (M W : SheafOfModules R)
    (Q : ℕ → SheafOfModules R) (q : ∀ n, M ⟶ Q n)
    (sep : ∀ U (x y : M.val.obj U),
      (∀ n, (q n).val.app U x = (q n).val.app U y) → x = y)
    (complete : ∀ U (b : ℕ → M.val.obj U),
      (∀ n m, n ≤ m → (q n).val.app U (b m) = (q n).val.app U (b n)) →
      ∃ x : M.val.obj U, ∀ n, (q n).val.app U x = (q n).val.app U (b n))
    (a : ∀ _n, W ⟶ M)
    (ha : ∀ n m, n ≤ m → a m ≫ q n = a n ≫ q n) :
    ∃ g : W ⟶ M, ∀ n, g ≫ q n = a n ≫ q n := by
  classical
  have hex (U : Cᵒᵖ) (x : W.val.obj U) :
      ∃ y : M.val.obj U, ∀ n, (q n).val.app U y =
        (q n).val.app U ((a n).val.app U x) := by
    apply complete U (fun n ↦ (a n).val.app U x)
    intro n m hnm
    exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app U) (ha n m hnm)) x
  choose g hg using hex
  let G : W ⟶ M := ⟨{
    app := fun U ↦ ModuleCat.ofHom {
      toFun := g U
      map_add' := by
        intro x y
        apply sep U
        intro n
        simp only [hg, map_add]
      map_smul' := by
        intro r x
        apply sep U
        intro n
        simp only [hg, map_smul, RingHom.id_apply]
    }
    naturality := by
      intro U V f
      ext x
      apply sep V
      intro n
      change (q n).val.app V (g V (W.val.map f x)) =
        (q n).val.app V (M.val.map f (g U x))
      calc
        _ = (q n).val.app V ((a n).val.app V (W.val.map f x)) := hg V _ n
        _ = (Q n).val.map f ((q n).val.app U ((a n).val.app U x)) :=
          (congrArg ((q n).val.app V) (PresheafOfModules.naturality_apply
            (a n).val f x)).trans
              (PresheafOfModules.naturality_apply (q n).val f _)
        _ = (Q n).val.map f ((q n).val.app U (g U x)) :=
          congrArg ((Q n).val.map f) (hg U x n).symm
        _ = _ := (PresheafOfModules.naturality_apply (q n).val f _).symm
  }⟩
  refine ⟨G, fun n ↦ ?_⟩
  ext U x
  exact hg U x n

set_option linter.unusedVariables false in
/-- Gluing of compatible lifts through the ordinary quotient tower.

Source: Hemo--Richarz--Scholbach, Theorem 7.7; Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-compatible-limit).

The hypothesis supplies agreement of all later integral maps with a_n modulo
ell^(n+1). The caller derives this by telescoping consecutive differences.
Proof: pass through the section-module equivalence. The quotient projections
jointly detect equality of sections, because the augmentation into the product
of the ordinary quotients is a monomorphism by constructible kernel-separatedness
and evaluation at a test preserves the product. For each test U and section x of
W, the sections a_n(x) form a compatible family; finite-presentation chart
convergence and constructible reassembly give a section g(x) with every
prescribed reduction. Joint detection shows that g is additive, linear and
natural, so it is a morphism of section modules; the equivalence transports it
back to a morphism W -> M with the prescribed reductions.
-/
theorem originalIntegralOrdinaryQuotient_compatibleLimit
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M)
    {W : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)}
    (a : ∀ n : ℕ, W ⟶ M)
    (ha : ∀ n m : ℕ, n ≤ m →
      a m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M)) :
    ∃ g : W ⟶ M, ∀ n : ℕ,
      g ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) := by
  classical
  let F :=
    CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)
  let q (n : ℕ) := cokernel.π (ell ^ (n + 1) • 𝟙 M)
  let A := CategoryTheory.OriginalIntegralQuotientSequence.augmentation ell M
  have hA : Mono A := Preadditive.mono_of_cancel_zero A (fun g hg ↦
    originalIntegralOrdinaryQuotientKernel_separated ell E X M hM g hg)
  have sep (U : X.ProEtᵒᵖ) (x y : (F.functor.obj M).val.obj U)
      (hxy : ∀ n, (F.functor.map (q n)).val.app U x =
        (F.functor.map (q n)).val.app U y) : x = y := by
    let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
      CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology X) (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)
    let T := F.functor ⋙ SheafOfModules.evaluation
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ⋙
        forget (ModuleCat.{u + 1} _)
    have hmono : Mono (T.map A) := inferInstance
    apply (CategoryTheory.mono_iff_injective (T.map A)).mp hmono
    let D := Discrete.functor (fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M))
    have hlim := isLimitOfPreserves T (limit.isLimit D)
    have hsec : Types.sectionOfCone (T.mapCone (limit.cone D)) (T.map A x) =
        Types.sectionOfCone (T.mapCone (limit.cone D)) (T.map A y) := by
      apply Subtype.ext
      funext n
      change T.map (Pi.π _ n.as) (T.map A x) =
        T.map (Pi.π _ n.as) (T.map A y)
      have heq : A ≫ Pi.π _ n.as = q n.as := by
        simp [A, q, CategoryTheory.OriginalIntegralQuotientSequence.augmentation]
      have hp := congrArg T.map heq
      rw [Functor.map_comp] at hp
      exact (ConcreteCategory.congr_hom hp x).trans
        ((hxy n.as).trans (ConcreteCategory.congr_hom hp y).symm)
    exact (Types.isLimit_iff_bijective_sectionOfCone _).mp ⟨hlim⟩ |>.injective hsec
  have hc := originalIntegralOrdinaryQuotient_compatibleLimit_reassembly ell E X M hM
    (fun Y N hN ↦ originalIntegralOrdinaryQuotient_compatibleLimit_finitePresentation
      ell E Y N hN)
  obtain ⟨g, hg⟩ := lift_sectionwise (F.functor.obj M) (F.functor.obj W)
    (fun n ↦ F.functor.obj (cokernel (ell ^ (n + 1) • 𝟙 M)))
    (fun n ↦ F.functor.map (q n)) sep hc (fun n ↦ F.functor.map (a n))
    (fun n m hnm ↦ by
      simpa only [← Functor.map_comp] using congrArg F.functor.map (ha n m hnm))
  refine ⟨F.functor.preimage g, fun n ↦ ?_⟩
  apply F.functor.map_injective
  simpa only [Functor.map_comp, Functor.map_preimage] using hg n

end AlgebraicGeometry.ProEtale.CondensedRing
