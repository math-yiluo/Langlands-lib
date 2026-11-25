/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Restriction of the origin adjunction
Source: Zheng, Section 5; integral reconstruction, step 2.
(blueprint: lem-sf-exceptional-integral-origin-adjunction-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Restrict the transported origin adjunction along the normalized full
subcategories and the two coordinate equivalences.
Source: Zheng, Lemma 5.22; the Hom-chain construction in the proof of the
normalized exceptional integral adjunction.
(blueprint: lem-sf-exceptional-integral-origin-adjunction-restriction).

Proof: lift the two coordinate equivalences to the origin subcategories and
use their counit isomorphisms to identify the transported proper/open and
exceptional functors with the normalized lifts. Apply the full-subcategory
adjunction restriction theorem. The displayed transpose is obtained by
expanding the restricted Hom equivalence and cancelling the coordinate
counit; it is exactly the transpose equation stored in SystemAdjunction.
-/
theorem exceptionalIntegralOriginAdjunctionRestriction
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s : Systems l E c)
    (hL : ∀ N, normalized l E X N → normalized l E Y ((s.left l E c).obj N))
    (hR : ∀ N, normalized l E Y N → normalized l E X ((s.exceptional l E c).obj N))
    (hX : ∀ N, normalized l E X N → s.siteX.origin ((coordinates l E X).functor.obj N))
    (hY : ∀ N, normalized l E Y N → s.siteY.origin ((coordinates l E Y).functor.obj N)) :
    Nonempty (SystemAdjunction l E c s) := by
  classical
  let PX := normalized l E X
  let PY := normalized l E Y
  let OX := s.siteX.origin
  let OY := s.siteY.origin
  let kX : PX.FullSubcategory ⥤ OX.FullSubcategory :=
    OX.lift (PX.ι ⋙ (coordinates l E X).functor) (fun M ↦ hX M.obj M.property)
  let kY : PY.FullSubcategory ⥤ OY.FullSubcategory :=
    OY.lift (PY.ι ⋙ (coordinates l E Y).functor) (fun M ↦ hY M.obj M.property)
  let L := PY.lift (PX.ι ⋙ s.left l E c) (fun M ↦ hL M.obj M.property)
  let R := PX.lift (PY.ι ⋙ s.exceptional l E c) (fun N ↦ hR N.obj N.property)
  let a := s.transport.val.systemAdjunction
  let F₀ := OY.lift (OX.ι ⋙ exceptionalProSupport s.properOpen)
    (fun M ↦ a.leftStable M.obj M.property)
  let G₀ := OX.lift (OY.ι ⋙ exceptionalSystemRight s.right s.siteX s.siteY)
    (fun N ↦ a.rightStable N.obj N.property)
  let comm1 : kX ⋙ F₀ ≅ L ⋙ kY := NatIso.ofComponents
    (fun M ↦ OY.isoMk ((coordinates l E Y).counitIso.symm.app
      ((exceptionalProSupport s.properOpen).obj ((coordinates l E X).functor.obj M.obj))))
    (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (coordinates l E Y).counitIso.inv.naturality
        ((exceptionalProSupport s.properOpen).map ((coordinates l E X).functor.map f.hom)))
  let comm2 : kY ⋙ G₀ ≅ R ⋙ kX := NatIso.ofComponents
    (fun N ↦ OX.isoMk ((coordinates l E X).counitIso.symm.app
      ((exceptionalSystemRight s.right s.siteX s.siteY).obj
        ((coordinates l E Y).functor.obj N.obj))))
    (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (coordinates l E X).counitIso.inv.naturality
        ((exceptionalSystemRight s.right s.siteX s.siteY).map
          ((coordinates l E Y).functor.map f.hom)))
  let adj := a.adjunction.restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful kX)
    (Functor.FullyFaithful.ofFullyFaithful kY) comm1 comm2
  refine ⟨{ leftStable := hL
            rightStable := hR
            adjunction := adj
            originX := hX
            originY := hY
            transpose := ?_ }⟩
  intro M N h
  have he : kX.map (adj.homEquiv M N h) =
      a.adjunction.homEquiv _ _ (comm1.hom.app M ≫ kY.map h) ≫ comm2.hom.app N := by
    dsimp only [adj]
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply,
      Functor.FullyFaithful.map_preimage]
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    simp only [Category.assoc]
  have ht := a.transpose (kX.obj M) (kY.obj N) (comm1.hom.app M ≫ kY.map h)
  have he' := congrArg (fun q ↦ q.hom ≫ (coordinates l E X).counitIso.hom.app
    ((exceptionalSystemRight s.right s.siteX s.siteY).obj
      ((coordinates l E Y).functor.obj N.obj))) he
  simp only [ObjectProperty.FullSubcategory.comp_hom] at he'
  change (coordinates l E X).functor.map (adj.homEquiv M N h).hom ≫
      (coordinates l E X).counitIso.hom.app _ =
    ((a.adjunction.homEquiv _ _ (comm1.hom.app M ≫ kY.map h)).hom ≫
      (coordinates l E X).counitIso.inv.app _) ≫
        (coordinates l E X).counitIso.hom.app _ at he'
  rw [Category.assoc, Iso.inv_hom_id_app] at he'
  erw [Category.comp_id] at he'
  change _ ≫ ((coordinates l E X).functor.map (adj.homEquiv M N h).hom ≫ _) = _
  erw [he']
  exact ht.symm

end WeilConjectures.ExceptionalIntegralReconstruction
