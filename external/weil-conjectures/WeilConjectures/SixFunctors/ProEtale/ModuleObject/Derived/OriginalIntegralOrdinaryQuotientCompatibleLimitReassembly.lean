/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelSeparatedFinitePresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStarHomotopyLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Constructible reassembly of compatible integral sections

This statement concerns only existence of sections. The caller separately proves
that these sections assemble into a linear natural morphism.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.InternalAbelianSheafModule
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

-- The high-priority `u + 1` sheafification instance gets stuck on these universe levels.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
-- Represent sections by a sheafified free Yoneda module, with the site universes retained.
private theorem sections_of_hom_lifts
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max v w}} (M : SheafOfModules.{max v w} R)
    (Q : ℕ → SheafOfModules R) (q : ∀ n, M ⟶ Q n)
    (hc : ∀ (W : SheafOfModules R) (a : ℕ → (W ⟶ M)),
      (∀ n m, n ≤ m → a m ≫ q n = a n ≫ q n) →
      ∃ g : W ⟶ M, ∀ n, g ≫ q n = a n ≫ q n)
    (U : Cᵒᵖ) (b : ℕ → M.val.obj U)
    (hb : ∀ n m, n ≤ m → (q n).val.app U (b m) = (q n).val.app U (b n)) :
    ∃ x : M.val.obj U, ∀ n, (q n).val.app U x = (q n).val.app U (b n) := by
  classical
  let P := (PresheafOfModules.free R.obj).obj (uliftYoneda.{v}.obj U.unop)
  let adj := PresheafOfModules.sheafificationAdjunction.{max v w} (𝟙 R.obj)
  let W := (PresheafOfModules.sheafification.{max v w} (𝟙 R.obj)).obj P
  let e (N : SheafOfModules R) : (W ⟶ N) ≃ N.val.obj U :=
    (adj.homEquiv P N).trans
      (PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv)
  have he {N N' : SheafOfModules R} (f : W ⟶ N) (g : N ⟶ N') :
      e N' (f ≫ g) = g.val.app U (e N f) := by
    dsimp [e]
    erw [adj.homEquiv_naturality_right]
    rfl
  let a (n : ℕ) : W ⟶ M := (e M).symm (b n)
  obtain ⟨g, hg⟩ := hc W a (by
    intro n m hnm
    apply (e (Q n)).injective
    simpa only [he, a, Equiv.apply_symm_apply] using hb n m hnm)
  refine ⟨e M g, fun n ↦ ?_⟩
  have h := congrArg (e (Q n)) (hg n)
  simpa only [he, a, Equiv.apply_symm_apply] using h

private theorem map_quotient_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {V N : C} (x : V ⟶ N) (k : ℕ)
    (hx : x ≫ cokernel.π (k • 𝟙 N) = 0) :
    F.map x ≫ cokernel.π (k • 𝟙 (F.obj N)) = 0 := by
  have hz : F.map x ≫ F.map (cokernel.π (k • 𝟙 N)) = 0 := by
    simpa only [Functor.map_comp, Functor.map_zero] using congrArg F.map hx
  let d := cokernel.desc (F.map (k • 𝟙 N)) (cokernel.π (k • 𝟙 (F.obj N))) (by
    rw [F.map_nsmul, F.map_id]
    exact cokernel.condition _)
  have hd : F.map (cokernel.π (k • 𝟙 N)) ≫
      (PreservesCokernel.iso F (k • 𝟙 N)).hom ≫ d =
      cokernel.π (k • 𝟙 (F.obj N)) := by
    rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]
  rw [← hd, ← Category.assoc, ← Category.assoc, hz, zero_comp, zero_comp]

private theorem quotient_lift_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] {V N : C} (g : F.obj V ⟶ F.obj N)
    (a : V ⟶ N) (k : ℕ)
    (hg : g ≫ cokernel.π (k • 𝟙 (F.obj N)) =
      F.map a ≫ cokernel.π (k • 𝟙 (F.obj N))) :
    g ≫ F.map (cokernel.π (k • 𝟙 N)) =
      F.map a ≫ F.map (cokernel.π (k • 𝟙 N)) := by
  let d := cokernel.desc (k • 𝟙 (F.obj N)) (F.map (cokernel.π (k • 𝟙 N))) (by
    rw [← F.map_id, ← F.map_nsmul, ← F.map_comp, cokernel.condition, F.map_zero])
  simpa only [Category.assoc, d, cokernel.π_desc] using congrArg (fun t ↦ t ≫ d) hg

-- The underlying-sheaf comparison transfers countable-product preservation to modules.
private theorem pullback_products
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [PreservesLimitsOfShape (Discrete ℕ) ((f)^*[Ab.{u + 1}])] :
    PreservesLimitsOfShape (Discrete ℕ) ((f)^*⟦Λ⟧) := by
  have : PreservesLimitsOfShape (Discrete ℕ)
      ((f)^*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y)) :=
    preservesLimitsOfShape_of_natIso (upperStarForgetIso Λ f)
  have : ReflectsLimitsOfShape (Discrete ℕ)
      (Mod.forget (condensedRingObj Λ Y) :
        Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤ _) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Mod.forget _)

-- Keep the preservation and concrete-category checks independent of the coefficient equivalence.
private theorem quotient_sections_separated
    {C : Type*} [Category C] [HasLimitsOfShape (Discrete ℕ) C]
    {D : Type v} [Category.{w} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{max v w}} (F : C ≌ SheafOfModules.{max v w} R)
    (N : C) (Q : ℕ → C) (q : ∀ n, N ⟶ Q n) [Mono (Pi.lift q)]
    (U : Dᵒᵖ) (x y : (F.functor.obj N).val.obj U)
    (hxy : ∀ n, (F.functor.map (q n)).val.app U x =
      (F.functor.map (q n)).val.app U y) : x = y := by
  let T := F.functor ⋙ SheafOfModules.evaluation R U ⋙ forget (ModuleCat.{max v w} _)
  have hmono : Mono (T.map (Pi.lift q)) := inferInstance
  apply (CategoryTheory.mono_iff_injective (T.map (Pi.lift q))).mp hmono
  have hlim := isLimitOfPreserves T (limit.isLimit (Discrete.functor Q))
  have hsec : Types.sectionOfCone (T.mapCone (limit.cone (Discrete.functor Q)))
        (T.map (Pi.lift q) x) =
      Types.sectionOfCone (T.mapCone (limit.cone (Discrete.functor Q)))
        (T.map (Pi.lift q) y) := by
    apply Subtype.ext
    funext n
    change T.map (Pi.π Q n.as) (T.map (Pi.lift q) x) =
      T.map (Pi.π Q n.as) (T.map (Pi.lift q) y)
    have hp := congrArg T.map (Pi.lift_comp_π q n.as)
    rw [Functor.map_comp] at hp
    exact (ConcreteCategory.congr_hom hp x).trans
      ((hxy n.as).trans (ConcreteCategory.congr_hom hp y).symm)
  exact (Types.isLimit_iff_bijective_sectionOfCone _).mp ⟨hlim⟩ |>.injective hsec

private theorem map_cokernel_zero_of_factor
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] {W N P : C} (A : N ⟶ P) (t : W ⟶ P)
    (g : F.obj W ⟶ F.obj N) (hg : g ≫ F.map A = F.map t) :
    F.map (t ≫ cokernel.π A) = 0 := by
  rw [Functor.map_comp, ← hg, Category.assoc, ← F.map_comp,
    cokernel.condition, F.map_zero, comp_zero]

private theorem quotient_hom_lifts_finitePresentation
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    {Y : Scheme.{u}}
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) N)
    (hlocal :
      let F := sectionModuleFunctor (ProEt.topology Y)
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y)
      ∀ (U : Y.ProEtᵒᵖ) (b : ℕ → (F.obj N).val.obj U),
        (∀ n m : ℕ, n ≤ m →
            ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b m) =
              ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b n)) →
        ∃ x : (F.obj N).val.obj U, ∀ n : ℕ,
            ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) x =
              ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b n))
    (W : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
    (a : ℕ → (W ⟶ N))
    (ha : ∀ n m, n ≤ m → a m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 N) =
      a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 N)) :
    ∃ g : W ⟶ N, ∀ n, g ≫ cokernel.π (ell ^ (n + 1) • 𝟙 N) =
      a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 N) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ell E
  let F := sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology Y) (condensedRingObj Λ Y)
  let qN (n : ℕ) := cokernel.π (ell ^ (n + 1) • 𝟙 N)
  let A := OriginalIntegralQuotientSequence.augmentation ell N
  have hA : Mono A := Preadditive.mono_of_cancel_zero A (fun g hg ↦ by
    apply originalIntegralOrdinaryQuotientKernel_separated_finitePresentation
      ell E Y N hN g
    intro n
    simpa [A, OriginalIntegralQuotientSequence.augmentation] using
      congrArg (fun t ↦ t ≫ Pi.π _ n) hg)
  have : Mono (Pi.lift qN) := hA
  have sep := quotient_sections_separated F N
    (fun n ↦ cokernel (ell ^ (n + 1) • 𝟙 N)) qN
  obtain ⟨g, hg⟩ := lift_sectionwise (F.functor.obj N) (F.functor.obj W)
    (fun n ↦ F.functor.obj (cokernel (ell ^ (n + 1) • 𝟙 N)))
    (fun n ↦ F.functor.map (qN n)) sep hlocal
    (fun n ↦ F.functor.map (a n))
    (fun n m hnm ↦ by
      simpa only [← Functor.map_comp] using congrArg F.functor.map (ha n m hnm))
  refine ⟨F.functor.preimage g, fun n ↦ ?_⟩
  apply F.functor.map_injective
  simpa only [Functor.map_comp, Functor.map_preimage] using hg n

private theorem quotient_lift_obstruction_map_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimitsOfShape (Discrete ℕ) C]
    (ell : ℕ) (L : C ⥤ D) [L.Additive] [PreservesFiniteColimits L]
    [PreservesLimitsOfShape (Discrete ℕ) L]
    (M W : C) (a : ℕ → (W ⟶ M))
    (ha : ∀ n m, n ≤ m → a m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
      a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M))
    (hcomplete : ∀ b : ℕ → (L.obj W ⟶ L.obj M),
      (∀ n m, n ≤ m → b m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 (L.obj M)) =
        b n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 (L.obj M))) →
      ∃ g : L.obj W ⟶ L.obj M, ∀ n,
        g ≫ cokernel.π (ell ^ (n + 1) • 𝟙 (L.obj M)) =
          b n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 (L.obj M))) :
    L.map (Pi.lift (fun n ↦ a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M)) ≫
      cokernel.π (OriginalIntegralQuotientSequence.augmentation ell M)) = 0 := by
  let Q (n : ℕ) := cokernel (ell ^ (n + 1) • 𝟙 M)
  let q (n : ℕ) := cokernel.π (ell ^ (n + 1) • 𝟙 M)
  let A := OriginalIntegralQuotientSequence.augmentation ell M
  let t : W ⟶ ∏ᶜ Q := Pi.lift (fun n ↦ a n ≫ q n)
  have hcompat (n m : ℕ) (hnm : n ≤ m) :
      L.map (a m) ≫ cokernel.π (ell ^ (n + 1) • 𝟙 (L.obj M)) =
        L.map (a n) ≫ cokernel.π (ell ^ (n + 1) • 𝟙 (L.obj M)) := by
    have hz : (a m - a n) ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) = 0 := by
      rw [Preadditive.sub_comp, ha n m hnm, sub_self]
    have h := map_quotient_zero L (a m - a n) _ hz
    simpa only [Functor.map_sub, Preadditive.sub_comp, sub_eq_zero] using h
  obtain ⟨g, hg⟩ := hcomplete (fun n ↦ L.map (a n)) hcompat
  have he : g ≫ L.map A = L.map t := by
    apply (isLimitOfPreserves L (limit.isLimit (Discrete.functor Q))).hom_ext
    intro n
    change (g ≫ L.map A) ≫ L.map (Pi.π Q n.as) =
      L.map t ≫ L.map (Pi.π Q n.as)
    rw [Category.assoc, ← L.map_comp, ← L.map_comp]
    have hπ : A ≫ Pi.π Q n.as = q n.as := by
      simp [A, q, Q, OriginalIntegralQuotientSequence.augmentation]
    rw [hπ]
    simpa only [t, q, Pi.lift_comp_π, L.map_comp] using
      quotient_lift_map L g (a n.as) (ell ^ (n.as + 1)) (hg n.as)
  exact map_cokernel_zero_of_factor L A t g he

private theorem proetale_cover_detects_zero {Y : Scheme.{u}}
    (C : Scheme.Cover.{u} proetalePrecoverage Y)
    {F G : Sheaf (ProEt.topology Y) Ab.{u + 1}} (q : F ⟶ G)
    (hq : ∀ j, (C.f j)^*[Ab.{u + 1}].map q = 0) : q = 0 := by
  have (j : C.I₀) : WeaklyEtale (C.f j) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk j)
  have hk (j : C.I₀) : IsIso ((C.f j)^*[Ab.{u + 1}].map (kernel.ι q)) := by
    have : IsIso (kernel.ι ((C.f j)^*[Ab.{u + 1}].map q)) :=
      kernel.ι_of_zero (hq j)
    have heq : (C.f j)^*[Ab.{u + 1}].map (kernel.ι q) =
        (PreservesKernel.iso (C.f j)^*[Ab.{u + 1}] q).hom ≫
          kernel.ι ((C.f j)^*[Ab.{u + 1}].map q) := by
      rw [← PreservesKernel.iso_inv_ι (C.f j)^*[Ab.{u + 1}] q]
      simp
    rw [heq]
    infer_instance
  have : IsIso (kernel.ι q) := by
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1}
      (kernel.ι q) C.f C.mem₀
    intro j
    exact (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (C.f j) inferInstance)
      (kernel.ι q)).1 (hk j)
  exact eq_zero_of_epi_kernel q

private theorem quotient_obstruction_zero_of_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M)
    {W V : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (v : W ⟶ V)
    (hpull : ∀ {Y : Scheme.{u}} (f : Y ⟶ X),
      [PreservesLimitsOfShape (Discrete ℕ) ((f)^*[Ab.{u + 1}])] →
      Mod.IsFinitelyPresented (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M) →
      (f)^*⟦Λ⟧.map v = 0) : v = 0 := by
  classical
  have hraw {Y : Scheme.{u}} (f : Y ⟶ X)
      [PreservesLimitsOfShape (Discrete ℕ) ((f)^*[Ab.{u + 1}])]
      (hfp : Mod.IsFinitelyPresented (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M)) :
      (f)^*[Ab.{u + 1}].map v.hom = 0 := by
    have hn := (upperStarForgetIso Λ f).hom.naturality v
    change (f)^*[Ab.{u + 1}].map v.hom ≫
        (upperStarForgetIso Λ f).hom.app V =
      (upperStarForgetIso Λ f).hom.app W ≫ ((f)^*⟦Λ⟧.map v).hom at hn
    rw [hpull f hfp] at hn
    apply (cancel_mono ((upperStarForgetIso Λ f).hom.app V)).1
    simpa using hn
  obtain ⟨S, hS⟩ := hM
  choose C hC using hS
  have hstr (a : Fin S.n) : (S.immersion a)^*[Ab.{u + 1}].map v.hom = 0 := by
    apply proetale_cover_detects_zero (C a)
    intro j
    have hfp := isFinitelyPresented_upperStar_of_comap_iso Λ ((C a).f j)
      (condensedPullbackHom Λ (S.immersion a))
      (comapUpperStarObjIso Λ (S.immersion a) M) (hC a j)
    have hfpc : Mod.IsFinitelyPresented (condensedRingObj Λ ((C a).X j))
        (((C a).f j ≫ S.immersion a)^*⟦Λ⟧.obj M) :=
      hfp.of_iso ((upperStarComp Λ ((C a).f j) (S.immersion a)).app M).symm
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        ((S.immersion a)^*[Ab.{u + 1}]) :=
      (Scheme.proEtale_immersion_inverseImage_preservesLimits (S.immersion a)).2.1
    have : PreservesLimitsOfSize.{0, 0} ((S.immersion a)^*[Ab.{u + 1}]) :=
      preservesSmallestLimits_of_preservesLimits _
    have : WeaklyEtale ((C a).f j) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ (C a).mem₀ (.mk j)
    have : PreservesLimitsOfShape (Discrete ℕ)
        (((C a).f j ≫ S.immersion a)^*[Ab.{u + 1}]) :=
      preservesLimitsOfShape_of_natIso
        (ProEtale.upperStarComp Ab.{u + 1} ((C a).f j) (S.immersion a)).symm
    have hn := (ProEtale.upperStarComp Ab.{u + 1} ((C a).f j)
      (S.immersion a)).hom.naturality v.hom
    simp only [Functor.comp_map, hraw _ hfpc, zero_comp] at hn
    apply (cancel_epi ((ProEtale.upperStarComp Ab.{u + 1} ((C a).f j)
      (S.immersion a)).app W.X).hom).1
    simpa using hn.symm
  -- Constructibility makes every stratum immersion quasi-compact.
  have : ∀ a : Fin S.n, QuasiCompact (S.immersion a) := fun a ↦ ⟨fun U hU hc ↦ by
    rw [(S.immersion a).isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range,
      S.range_immersion a, Set.inter_comm]
    exact (S.isConstructible_stratum a).isRetrocompact hc hU⟩
  apply (Mod.forget _).map_injective
  change v.hom = 0
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
  · intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · exact hstr

/-- Reassembly of individual section limits over a constructible module.
Source: Hemo--Richarz--Scholbach, Proposition 5.1, proof for constructible sheaves;
Bhatt--Scholze, Corollary 6.1.5.
(blueprint: lem-sp-original-integral-ordinary-quotient-compatible-limit-reassembly).
Proof: first use finite-presentation separatedness to make the section limits
supplied by hlocal unique, hence linear and natural. They give limits for all
compatible sequences of morphisms into a finitely presented module. For a
constructible M, its augmentation A into the product of positive quotients is
monic by constructible separatedness. For a compatible sequence a_n : W -> M,
let t : W -> product(M/ell^(n+1)) have coordinates a_n modulo ell^(n+1).
It lifts through A exactly when t followed by cokernel.π A vanishes. Pullback
to each finite-presentation chart preserves the countable product and ordinary
cokernels. The chartwise limit factors the pulled-back t through the pulled-back
A, so this obstruction vanishes there. Cover-local detection and finite
quasi-compact detection along the constructible strata make it vanish on X.
The abelian mono-lifting property now supplies the required morphism limit.
Finally, sections over U are represented by the sheafification of the free
module presheaf on the lifted Yoneda object of U. Apply the morphism limit to
these representing maps and evaluate to obtain the requested section. This
includes empty schemes, empty strata, and the zero module. -/
theorem originalIntegralOrdinaryQuotient_compatibleLimit_reassembly
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M)
    (hlocal : ∀ (Y : Scheme.{u})
      (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
      (_hN : Mod.IsFinitelyPresented
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) N),
      let F := sectionModuleFunctor (ProEt.topology Y)
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y)
      ∀ (U : Y.ProEtᵒᵖ) (b : ℕ → (F.obj N).val.obj U),
        (∀ n m : ℕ, n ≤ m →
            ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b m) =
              ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b n)) →
        ∃ x : (F.obj N).val.obj U, ∀ n : ℕ,
            ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) x =
              ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b n)) :
    let F := sectionModuleFunctor (ProEt.topology X)
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)
    ∀ (U : X.ProEtᵒᵖ) (b : ℕ → (F.obj M).val.obj U),
      (∀ n m : ℕ, n ≤ m →
        ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 M))).val.app U) (b m) =
          ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 M))).val.app U) (b n)) →
      ∃ x : (F.obj M).val.obj U, ∀ n : ℕ,
        ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 M))).val.app U) x =
          ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 M))).val.app U) (b n) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ell E
  have hhom
      (W : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (a : ℕ → (W ⟶ M))
      (ha : ∀ n m, n ≤ m → a m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M)) :
      ∃ g : W ⟶ M, ∀ n, g ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) := by
    let Q (n : ℕ) := cokernel (ell ^ (n + 1) • 𝟙 M)
    let q (n : ℕ) := cokernel.π (ell ^ (n + 1) • 𝟙 M)
    let A := OriginalIntegralQuotientSequence.augmentation ell M
    have hA : Mono A := Preadditive.mono_of_cancel_zero A (fun g hg ↦
      originalIntegralOrdinaryQuotientKernel_separated ell E X M hM g hg)
    let t : W ⟶ ∏ᶜ Q := Pi.lift (fun n ↦ a n ≫ q n)
    let v := t ≫ cokernel.π A
    have hpull {Y : Scheme.{u}} (f : Y ⟶ X)
        [PreservesLimitsOfShape (Discrete ℕ) ((f)^*[Ab.{u + 1}])]
        (hfp : Mod.IsFinitelyPresented (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M)) :
        (f)^*⟦Λ⟧.map v = 0 := by
      let L := (f)^*⟦Λ⟧
      have : PreservesLimitsOfShape (Discrete ℕ) L := pullback_products Λ f
      exact quotient_lift_obstruction_map_zero ell L M W a ha
        (quotient_hom_lifts_finitePresentation ell E
          (L.obj M) hfp (hlocal Y (L.obj M) hfp) (L.obj W))
    have hv : v = 0 := quotient_obstruction_zero_of_constructible Λ X M hM v hpull
    refine ⟨Abelian.monoLift A t hv, fun n ↦ ?_⟩
    have h := congrArg (fun z ↦ z ≫ Pi.π Q n) (Abelian.monoLift_comp A t hv)
    simpa only [Category.assoc, A, OriginalIntegralQuotientSequence.augmentation,
      Pi.lift_comp_π, t, Q, q] using h
  let F := sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (condensedRingObj Λ X)
  dsimp only
  intro U b hb
  apply sections_of_hom_lifts (F.functor.obj M)
    (fun n ↦ F.functor.obj (cokernel (ell ^ (n + 1) • 𝟙 M)))
    (fun n ↦ F.functor.map (cokernel.π (ell ^ (n + 1) • 𝟙 M))) ?_ U b hb
  intro W a ha
  let a' (n : ℕ) : F.inverse.obj W ⟶ M :=
    F.functor.preimage (F.counitIso.hom.app W ≫ a n)
  have hcompat (n m : ℕ) (hnm : n ≤ m) :
      a' m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        a' n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) := by
    apply F.functor.map_injective
    simp only [Functor.map_comp, a', Functor.map_preimage, Category.assoc, ha n m hnm]
  obtain ⟨g, hg⟩ := hhom (F.inverse.obj W) a' hcompat
  refine ⟨F.counitIso.inv.app W ≫ F.functor.map g, fun n ↦ ?_⟩
  have h := congrArg F.functor.map (hg n)
  simpa only [Functor.map_comp, a', Functor.map_preimage, Category.assoc,
    Iso.inv_hom_id_app_assoc] using congrArg (fun z ↦ F.counitIso.inv.app W ≫ z) h

end AlgebraicGeometry.ProEtale.CondensedRing
