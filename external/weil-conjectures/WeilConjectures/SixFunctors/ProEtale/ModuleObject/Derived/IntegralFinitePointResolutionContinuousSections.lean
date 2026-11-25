/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionAlgebraic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Separation.Hausdorff
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra

/-! Lifted sectionwise exactness for the integral finite point resolution. -/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

abbrev LiftedPointSections0 (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (P : Profinite.{u}) (r : ℕ) :=
  ULift.{u + 1} C(P, Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1))

abbrev LiftedPointSections2 (P : Profinite.{u}) (A : Type u) [TopologicalSpace A] :=
  ULift.{u + 1} C(P, ULift.{u + 1} A)

/-- Shortcut instance: on v4.35 the default search for this instance times out. -/
local instance (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    ContinuousSMul (PadicAlgCl.integers ell E.1) (PadicAlgCl.integers ell E.1) :=
  ContinuousMul.to_continuousSMul

/-- Shortcut instance: on v4.35 the default search for this instance times out. -/
local instance (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    ContinuousSMul (PadicAlgCl.integers ell E.1) (ULift.{u + 1} (PadicAlgCl.integers ell E.1)) :=
  ContinuousSMul.induced
    (ULift.moduleEquiv : ULift.{u + 1} (PadicAlgCl.integers ell E.1) ≃ₗ[_] _)

private theorem continuous_liftedPi_linearMap
    {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type (u + 1)} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M] (r : ℕ)
    (f : (Fin r → ULift.{u + 1} R) →ₗ[R] M) : Continuous f := by
  let e : (Fin r → ULift.{u + 1} R) ≃ₗ[R] (Fin r → R) :=
    LinearEquiv.piCongrRight (fun _ ↦ ULift.moduleEquiv)
  have he : Continuous e := continuous_pi fun i ↦
    continuous_uliftDown.comp (continuous_apply i)
  simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_def,
    LinearEquiv.symm_apply_apply] using
    ((f.comp e.symm.toLinearMap).continuous_on_pi.comp he)

/-- The finite resolution maps remain exact after applying them to lifted continuous sections.

Source: the compact-image inverse and finite-discrete-fibre part of the continuous point
resolution proof (blueprint: lem-s3-integral-finite-point-resolution-continuous).
The section carriers are stated with the canonical universe lifts used by `ModuleCat`.
-/
theorem integralFinitePointResolution_continuous_sections
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (A : Type u) [CommRing A] [Finite A]
    (φ : PadicAlgCl.integers ell E.1 →+* A)
    (hφ : @Continuous _ _ inferInstance ⊥ φ) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := inferInstance
    letI : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
    let φ' : PadicAlgCl.integers ell E.1 →+* ULift.{u + 1} A :=
      ULift.ringEquiv.symm.toRingHom.comp φ
    letI : Module (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A) :=
      Module.compHom (ULift.{u + 1} A) φ'
    ∀ (r : ℕ)
      (f : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1)
        (Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
        ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1)
          (Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1)))
      (g : ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1)
        (Fin r → ULift.{u + 1} (PadicAlgCl.integers ell E.1)) ⟶
        ModuleCat.of.{u + 1} (PadicAlgCl.integers ell E.1) (ULift.{u + 1} A)),
      Function.Injective f.hom → Function.Exact f.hom g.hom →
        Function.Surjective g.hom →
      ∃ (F : ∀ P : Profinite.{u},
          LiftedPointSections0 ell E P r →+
            LiftedPointSections0 ell E P r)
        (G : ∀ P : Profinite.{u},
          LiftedPointSections0 ell E P r →+
            LiftedPointSections2 P A),
        (∀ (P : Profinite.{u}) (b : LiftedPointSections0 ell E P r) (s : P),
          (F P b).down s = f.hom (b.down s)) ∧
        (∀ (P : Profinite.{u}) (b : LiftedPointSections0 ell E P r) (s : P),
          (G P b).down s = g.hom (b.down s)) ∧
        (∀ {P Q : Profinite.{u}} (q : C(Q, P))
          (b : LiftedPointSections0 ell E P r),
          (F Q (ULift.up (b.down.comp q))).down = (F P b).down.comp q) ∧
        (∀ {P Q : Profinite.{u}} (q : C(Q, P))
          (b : LiftedPointSections0 ell E P r),
          (G Q (ULift.up (b.down.comp q))).down = (G P b).down.comp q) ∧
        (∀ (P : Profinite.{u}) (c : C(P, PadicAlgCl.integers ell E.1))
          (b : LiftedPointSections0 ell E P r) (s : P),
          (F P (ULift.up (c • b.down))).down s = c s • (F P b).down s) ∧
        (∀ (P : Profinite.{u}) (c : C(P, PadicAlgCl.integers ell E.1))
          (b : LiftedPointSections0 ell E P r) (s : P),
          (G P (ULift.up (c • b.down))).down s = c s • (G P b).down s) ∧
        (∀ P, Function.Injective (F P)) ∧
        (∀ P, Function.Exact (F P) (G P)) ∧
        (∀ P, Function.Surjective (G P)) := by
  classical
  dsimp only
  let R := PadicAlgCl.integers ell E.1
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : Module R A := Module.compHom A φ
  let φ' : R →+* ULift.{u + 1} A := ULift.ringEquiv.symm.toRingHom.comp φ
  let : Module R (ULift.{u + 1} A) := Module.compHom (ULift.{u + 1} A) φ'
  have : ContinuousSMul R A := ⟨by
    change Continuous (fun p : R × A ↦ φ p.1 * p.2)
    exact (hφ.comp continuous_fst).mul continuous_snd⟩
  have : ContinuousSMul R (ULift.{u + 1} A) := by
    refine ⟨continuous_uliftUp.comp ?_⟩
    exact (hφ.comp continuous_fst).mul (continuous_uliftDown.comp continuous_snd)
  have : ContinuousSMul R (ULift.{u + 1} R) :=
    ContinuousSMul.induced (ULift.moduleEquiv : ULift.{u + 1} R ≃ₗ[R] R)
  intro r f g hf hfg hg
  have hfcont : Continuous f.hom := continuous_liftedPi_linearMap r f.hom
  have hgcont : Continuous g.hom := continuous_liftedPi_linearMap r g.hom
  have : CompactSpace R := PadicAlgCl.compactSpace_integers ell E.1
  have hfemb := hfcont.isClosedEmbedding hf
  let F : ∀ P : Profinite.{u},
      LiftedPointSections0 ell E P r →+ LiftedPointSections0 ell E P r := fun P ↦
    { toFun := fun b ↦ ULift.up ((⟨f.hom, hfcont⟩ : C(_, _)).comp b.down)
      map_zero' := by
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        exact map_zero f.hom
      map_add' := by
        intro a b
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        exact map_add f.hom _ _ }
  let G : ∀ P : Profinite.{u},
      LiftedPointSections0 ell E P r →+ LiftedPointSections2 P A := fun P ↦
    { toFun := fun b ↦ ULift.up ((⟨g.hom, hgcont⟩ : C(_, _)).comp b.down)
      map_zero' := by
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        exact map_zero g.hom
      map_add' := by
        intro a b
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        exact map_add g.hom _ _ }
  refine ⟨F, G, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro P c b s
    exact f.hom.map_smul (c s) (b.down s)
  · intro P c b s
    exact g.hom.map_smul (c s) (b.down s)
  · intro P a b hab
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact hf (congrArg (fun z : LiftedPointSections0 ell E P r ↦ z.down s) hab)
  · intro P a
    constructor
    · intro ha
      have hz (s : P) : g.hom (a.down s) = 0 :=
        congrArg (fun z : LiftedPointSections2 P A ↦ z.down s) ha
      choose b hb using fun s ↦ (hfg (a.down s)).mp (hz s)
      have hbc : Continuous b := hfemb.isEmbedding.continuous_iff.mpr (by
        simpa only [Function.comp_def, hb] using a.down.continuous)
      refine ⟨ULift.up (⟨b, hbc⟩ : C(P, Fin r → ULift.{u + 1} R)), ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      exact hb s
    · rintro ⟨b, rfl⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      exact (hfg (f.hom (b.down s))).mpr ⟨b.down s, rfl⟩
  · intro P a
    let k : C(ULift.{u + 1} A, Fin r → ULift.{u + 1} R) :=
      ⟨Function.surjInv hg, continuous_of_discreteTopology⟩
    refine ⟨ULift.up (k.comp a.down), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact Function.surjInv_eq hg (a.down s)

end AlgebraicGeometry.ProEtale.CondensedRing
