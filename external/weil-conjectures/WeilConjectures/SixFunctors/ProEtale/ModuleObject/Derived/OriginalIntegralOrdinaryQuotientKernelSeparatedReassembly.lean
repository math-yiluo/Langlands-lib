/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.OriginalIntegralQuotientSequence.OriginalIntegralOrdinaryQuotientSequence
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Topology.ConstructibleIsRetrocompact

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

-- Preserve the descriptive hypothesis names inside the supplied finite-presentation criterion.
set_option linter.unusedVariables false in
/-- Reassembly of finite-presentation separatedness over a constructible module.

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-kernel-separated-reassembly).

Proof. Constructibility gives a finite stratification and, on each stratum, a
pro-étale cover on whose charts the pullback of the module is finitely
presented. Pullback is additive and right exact, so it carries the vanishing
of every quotient projection to the pulled-back map; the finite-presentation
separatedness statement then makes the pullback of the map zero on every
chart. A pro-étale cover detects zero maps, so the restriction to each stratum
is zero. The strata are constructible, hence retrocompact, so their immersions
are quasi-compact and jointly surjective; finite quasi-compact detection makes
the map zero. -/
theorem originalIntegralOrdinaryQuotientKernel_separated_of_finitePresentation
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
    (g : W ⟶ M)
    (hsep : ∀ {Y : Scheme.{u}}
      (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
      (hN : Mod.IsFinitelyPresented
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) N)
      {V : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y)}
      (u : V ⟶ N)
      (hu : ∀ n : ℕ, u ≫ cokernel.π (ell ^ (n + 1) • 𝟙 N) = 0),
      u = 0)
    (hg : ∀ n : ℕ, g ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) = 0) :
    g = 0 := by
  classical
  let Λ := Profinite.padicIntegersRingObj ell E
  -- Cokernel preservation transports the quotient-vanishing hypothesis to every pullback.
  have hpull {Y : Scheme.{u}} (f : Y ⟶ X)
      (hfp : Mod.IsFinitelyPresented (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M)) :
      (f)^*⟦Λ⟧.map g = 0 := by
    apply hsep _ hfp
    intro n
    have h : (f)^*⟦Λ⟧.map g ≫
        cokernel.π ((f)^*⟦Λ⟧.map (ell ^ (n + 1) • 𝟙 M)) = 0 := by
      rw [← PreservesCokernel.π_iso_hom (f)^*⟦Λ⟧ (ell ^ (n + 1) • 𝟙 M),
        ← Category.assoc, ← Functor.map_comp, hg n, Functor.map_zero, zero_comp]
    let e := cokernel.map ((f)^*⟦Λ⟧.map (ell ^ (n + 1) • 𝟙 M))
      (ell ^ (n + 1) • 𝟙 ((f)^*⟦Λ⟧.obj M)) (𝟙 _) (𝟙 _)
      (by
        rw [Category.id_comp, Category.comp_id, Functor.map_nsmul]
        exact congrArg (fun q ↦ ell ^ (n + 1) • q) ((f)^*⟦Λ⟧.map_id M))
    have hπ : cokernel.π ((f)^*⟦Λ⟧.map (ell ^ (n + 1) • 𝟙 M)) ≫ e =
        cokernel.π (ell ^ (n + 1) • 𝟙 ((f)^*⟦Λ⟧.obj M)) := by
      simp [e]
    simpa only [Category.assoc, hπ, zero_comp] using congrArg (fun q ↦ q ≫ e) h
  -- The coefficient comparison identifies the underlying morphism with sheaf pullback.
  have hraw {Y : Scheme.{u}} (f : Y ⟶ X)
      (hfp : Mod.IsFinitelyPresented (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M)) :
      (f)^*[Ab.{u + 1}].map g.hom = 0 := by
    have hn : ((f)^*⟦Λ⟧.map g).hom ≫ (upperStarObjXIso Λ f M).hom =
        (upperStarObjXIso Λ f W).hom ≫ (f)^*[Ab.{u + 1}].map g.hom :=
      congrArg (fun q ↦ q.hom)
        ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.naturality
          (((f)^*[Ab.{u + 1}].mapMod _).map g))
    rw [hpull f hfp] at hn
    apply (cancel_epi (upperStarObjXIso Λ f W).hom).1
    simpa using hn.symm
  -- A pro-étale cover detects zero maps: its restrictions make the kernel inclusion invertible.
  have hcover {Y : Scheme.{u}} (C : Scheme.Cover.{u} proetalePrecoverage Y)
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
  obtain ⟨S, hS⟩ := hM
  choose C hC using hS
  have hstr (a : Fin S.n) : (S.immersion a)^*[Ab.{u + 1}].map g.hom = 0 := by
    apply hcover (C a)
    intro j
    have hfp := isFinitelyPresented_upperStar_of_comap_iso Λ ((C a).f j)
      (condensedPullbackHom Λ (S.immersion a))
      (comapUpperStarObjIso Λ (S.immersion a) M) (hC a j)
    have hfpc : Mod.IsFinitelyPresented (condensedRingObj Λ ((C a).X j))
        (((C a).f j ≫ S.immersion a)^*⟦Λ⟧.obj M) :=
      hfp.of_iso ((upperStarComp Λ ((C a).f j) (S.immersion a)).app M).symm
    have hn := (ProEtale.upperStarComp Ab.{u + 1} ((C a).f j)
      (S.immersion a)).hom.naturality g.hom
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
  change g.hom = 0
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
  · intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · exact hstr

end AlgebraicGeometry.ProEtale.CondensedRing
