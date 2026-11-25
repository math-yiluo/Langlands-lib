/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.FiniteTypeRingSystem
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import WeilConjectures.RingTheory.LocalizeFilteredRingSystem
import Mathlib.RingTheory.RingHom.EssFiniteType
@[expose] public section
universe u p
open CategoryTheory CategoryTheory.Limits
namespace RingHom
/-- Core ring descent assertion, retaining the transition and structure maps but omitting
explicit representatives of the cocone maps. Source: Stacks Project, Algebra, Tag 00QV,
using the localization-colimit construction in the proof of Tag 037D.
(blueprint: lem-weil-pbc-limit-module-ring-data-core)

Proof: Finite presentation implies finite type. After shrinking P to the base universe,
take the images of polynomial evaluation at fixed algebra generators over each stage.
Their directed union is P. Localize this system at the inverse images of the maximal
ideal of T; localization commutes with the filtered colimit. Compose the structure
maps. The resulting cocone maps are local, so their domains and all transition maps
are local. Locality of the original cocone and τ implies locality of the structure maps. -/
theorem exists_limit_module_ring_data_core
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
        (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
          (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
          (∀ i, (β.app i).hom.comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            (B.map (homOfLE h)).hom.comp (τ₀ i) =
              (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧
          (∀ i, IsLocalHom ((β.app i).hom)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) := by
  classical
  have _ := hF
  have : Small.{u} P := Algebra.FiniteType.small (R := c.pt) (S := P)
  let Q := Shrink.{u} P
  let r : Q ≃ₐ[c.pt] P := Shrink.algEquiv c.pt P
  have : Algebra.FiniteType c.pt Q := Algebra.FiniteType.equiv inferInstance r.symm
  obtain ⟨i₀, D, σ, eQ, hσfinite, hσcompQ, hσnat⟩ :=
    exists_finiteType_ring_system F c hc Q
  let e := eQ.trans r.toRingEquiv
  have hσcomp (i : {i : I // i₀ ≤ i}) :
      e.toRingHom.comp ((colimit.ι D i).hom.comp (σ i)) =
        (algebraMap c.pt P).comp (c.ι.app i.1).hom := by
    change r.toRingHom.comp (eQ.toRingHom.comp ((colimit.ι D i).hom.comp (σ i))) = _
    rw [hσcompQ]
    ext x
    exact r.commutes ((c.ι.app i.1).hom x)
  let J := {i : I // i₀ ≤ i}
  have : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let g : (colimit D : CommRingCat.{u}) →+* T := f.comp e.toRingHom
  let V := W.map e.symm.toMonoidHom
  have hV : letI := g.toAlgebra; IsLocalization V T := by
    let := f.toAlgebra
    let := g.toAlgebra
    have : IsLocalization W T := hT
    apply IsLocalization.of_ringEquiv_left (M₁ := W) (M₂ := V) e
    · ext x
      simp [V]
    · intro x
      rfl
  obtain ⟨B, β, ιB, hcol, hιfinite, hβlocal, hιcomp⟩ :=
    exists_localized_filtered_ring_system D T g V hV
  let τ₀ (i : J) : F.obj i.1 →+* B.obj i := (ιB.app i).hom.comp (σ i)
  have hcomp (i : J) :
      (β.app i).hom.comp (τ₀ i) = τ.comp (c.ι.app i.1).hom := by
    change (β.app i).hom.comp ((ιB.app i).hom.comp (σ i)) = _
    rw [← RingHom.comp_assoc, hιcomp]
    change f.comp (e.toRingHom.comp ((colimit.ι D i).hom.comp (σ i))) = _
    rw [hσcomp, ← RingHom.comp_assoc, hf]
  refine ⟨i₀, B, β, hcol, τ₀, ?_, ?_, hcomp, ?_, ?_, hβlocal, ?_⟩
  · intro i
    have : IsLocalHom (c.ι.app i.1).hom := hcLocal i.1
    have : IsLocalHom ((β.app i).hom.comp (τ₀ i)) := by
      rw [hcomp]
      infer_instance
    exact isLocalHom_of_comp (τ₀ i) (β.app i).hom
  · intro i
    exact (hσfinite i).essFiniteType.comp (hιfinite i)
  · intro i j h
    change (B.map (homOfLE h)).hom.comp ((ιB.app i).hom.comp (σ i)) = _
    have hnat := congrArg CommRingCat.Hom.hom (ιB.naturality (homOfLE h))
    change (ιB.app j).hom.comp (D.map (homOfLE h)).hom =
      (B.map (homOfLE h)).hom.comp (ιB.app i).hom at hnat
    rw [← RingHom.comp_assoc, ← hnat, RingHom.comp_assoc, hσnat]
    rfl
  · intro i
    have : IsLocalHom (β.app i).hom := hβlocal i
    exact (show B.obj i →+* T from (β.app i).hom).domain_isLocalRing
  · intro i j h
    have : IsLocalHom (β.app i).hom := hβlocal i
    have hnat := congrArg CommRingCat.Hom.hom (β.naturality (homOfLE h))
    change (β.app j).hom.comp (B.map (homOfLE h)).hom = (β.app i).hom at hnat
    have : IsLocalHom ((β.app j).hom.comp (B.map (homOfLE h)).hom) := by
      rw [hnat]
      infer_instance
    exact isLocalHom_of_comp (B.map (homOfLE h)).hom (β.app j).hom
end RingHom
