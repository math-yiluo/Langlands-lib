/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.SixFunctors.RestrictionLocal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionLine
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestrictionClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverBase
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Finite-open descent for integral restriction

Source: blueprint main-20261015, sk-thm-int-restriction-glue.proof.md,
expanded by theorem-f-shriek-ell-adic-coefficients.
-/

@[expose] public noncomputable section
set_option linter.privateModule false

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction

private def space (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] : Spaces k :=
  ⟨Over.mk (X ↘ Spec (.of k)),
    (show IsSeparated (X ↘ Spec (.of k)) from inferInstance),
    (show LocallyOfFiniteType (X ↘ Spec (.of k)) from inferInstance),
    (show QuasiCompact (X ↘ Spec (.of k)) from inferInstance)⟩

private def pullLift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ f).obj K)) :
    (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory :=
  (localizing Λ X).lift ((localizing Λ Y).ι ⋙ pull Λ f)
    (fun K ↦ h K.obj K.property)

private def openAdj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (h : ∀ K, localizing Λ X K → localizing Λ Y
      ((image Λ (Compactification.ofIsOpenImmersion j)).obj K))
    (hp : ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ j).obj K)) :
    lowerShriek Λ (Compactification.ofIsOpenImmersion j) h ⊣ pullLift Λ j hp := by
  let a := (openAdjunction Λ j).ofNatIsoLeft (mateOpenTrivialLowerShriek Λ j).symm
  exact a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl))

private theorem boundedConstructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {K L : Ambient Λ X}
    (e : K ≅ L) (hK : generators Λ X K) : generators Λ X L := by
  refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e hK.1, ?_⟩
  intro n
  let eh := (DerivedCategory.homologyFunctor _ n).mapIso e
  have hi {X : Scheme.{u}}
      {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
      (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
      IsFiniteConstantStratified Λ X N := by
    obtain ⟨S, hS⟩ := hM
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨U, hU⟩ := hS a
    refine ⟨U, fun b ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU b
    exact ⟨P, hP, ⟨((upperStar Λ (U.f b)).mapIso
      ((upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  have hk := hK.2 n
  unfold IsConstantModelConstructible at hk ⊢
  by_cases hqc : CompactSpace X ∧ QuasiSeparatedSpace X
  · rw [ite_eq_left hqc] at hk ⊢
    exact hi eh hk
  · rw [ite_eq_right hqc] at hk ⊢
    intro U hU
    exact hi ((upperStar Λ U.ι).mapIso eh) (hk U hU)

private def lowerCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (μ : Compositions Λ k)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f)
    (d : Compactification.BoundaryCompactification g)
    (e : Compactification.BoundaryCompactification (f ≫ g))
    (hf : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K))
    (hg : ∀ K, localizing Λ Y K → localizing Λ Z ((image Λ d.obj.obj).obj K))
    (hgf : ∀ K, localizing Λ X K → localizing Λ Z ((image Λ e.obj.obj).obj K)) :
    lowerShriek Λ c.obj.obj hf ⋙ lowerShriek Λ d.obj.obj hg ≅
      lowerShriek Λ e.obj.obj hgf := by
  let f' : space k X ⟶ space k Y := ObjectProperty.homMk (f.asOver (Spec (.of k)))
  let g' : space k Y ⟶ space k Z := ObjectProperty.homMk (g.asOver (Spec (.of k)))
  let e0 := μ f' g' c.obj d.obj e.obj
  refine NatIso.ofComponents (fun K ↦ (localizing Λ Z).isoMk (e0.app K)) ?_
  intro K L m
  apply ObjectProperty.hom_ext
  exact e0.hom.naturality m

private theorem image_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (h : Preservation Λ k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f) :
    ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K) := by
  exact h.maps_localizing (X := space k X) (Y := space k Y)
    (f := ObjectProperty.homMk (f.asOver (Spec (.of k)))) c.obj

private theorem pull_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {h : Preservation Λ k} {φ : Comparisons Λ k}
    {μ : Compositions Λ k} (hc : Coherence Λ k h φ μ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ f).obj K) := by
  exact hc.localizing_pull (X := space k X) (Y := space k Y)
    (ObjectProperty.homMk (f.asOver (Spec (.of k))))

private theorem affine_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (d : ℕ)
    (c : Compactification.BoundaryCompactification (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) Y) K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) Y)).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val)
      (AffineSpace (ULift.{u} (Fin d)) Y) (G.obj K).obj := by
  obtain ⟨hq, hp, hr, _, _, hb, _, hpres⟩ :=
    CondensedRing.IntegralRestriction.integralRestrictionLine ℓ E k Y d
  obtain ⟨e⟩ := hb c h G ⟨adj⟩
  exact boundedConstructible_iso _
    (((localizing (Profinite.padicIntegersRingObj ℓ E.val) _).ι).mapIso (e.app K)).symm
    (hpres K.obj hK)

private theorem closed_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsClosedImmersion f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val) X (G.obj K).obj := by
  obtain ⟨hadd, hgen, hpres, hcomp⟩ := integralRestrictionClosed ℓ E k f
  let := hadd
  obtain ⟨e⟩ := hcomp c h G adj
  exact boundedConstructible_iso _ (e.app ⟨K.obj, hK⟩).symm (hpres K.obj hK)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction
