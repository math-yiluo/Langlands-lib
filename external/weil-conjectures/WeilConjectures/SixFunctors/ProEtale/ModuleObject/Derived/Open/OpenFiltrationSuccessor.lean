/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Natural successive open-extension quotients

Source: Stacks Project, Tags 09AH, 03DI and 03DJ
(blueprint: lem-sfb-open-filtration-successor).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

private instance (priority := 2000) essentiallySmallSelfInstance
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem map_cokernel_pi_iso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteColimits H]
    {A B : C} (f : A ⟶ B) (hz : IsZero (H.obj A)) :
    IsIso (H.map (cokernel.π f)) := by
  have hf : H.map f = 0 := hz.eq_of_src _ _
  have : IsIso (cokernel.π (H.map f)) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (cokernel.π (H.map f)) (cokernel.condition _))
      (cokernelIsCokernel (H.map f)) hf
  have : IsIso (H.map (cokernel.π f) ≫ (PreservesCokernel.iso H f).hom) := by
    rw [PreservesCokernel.π_iso_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso H f).hom

private theorem natural_open_closed_quotient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U S : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (t : S ⟶ X) [IsClosedImmersion t]
    (hjt : Set.range j = (Set.range t)ᶜ) :
    Nonempty (cokernel (openImmersionLowerShriekUpperStarAdjunction Λ j).counit ≅
      upperStar Λ t ⋙ lowerStar Λ t) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let ε := (openImmersionLowerShriekUpperStarAdjunction Λ j).counit
  let Q := cokernel ε
  let π : 𝟭 C ⟶ Q := cokernel.π ε
  have hq (M : C) : IsZero ((upperStar Λ j).obj (Q.obj M)) := by
    let e := PreservesCokernel.iso ((evaluation C C).obj M) ε
    exact (open_cokernel_zero Λ j M).of_iso ((upperStar Λ j).mapIso e)
  let η := whiskerLeft Q (upperStarLowerStarAdjunction Λ t).unit
  have hη : IsIso η := by
    have : ∀ M, IsIso (η.app M) := fun M ↦
      supported_unit Λ t j hjt (Q.obj M) (hq M)
    exact NatIso.isIso_of_isIso_app η
  let p := whiskerRight π (upperStar Λ t)
  have hp : IsIso p := by
    have : ∀ M, IsIso (p.app M) := fun M ↦
      map_cokernel_pi_iso (((evaluation C C).obj M) ⋙ upperStar Λ t) ε
        (closed_pull_open_zero Λ t j hjt ((upperStar Λ j).obj M))
    exact NatIso.isIso_of_isIso_app p
  exact ⟨asIso η ≪≫ Functor.isoWhiskerRight (asIso p).symm (lowerStar Λ t)⟩

private theorem successor_of_adjunctions
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D]
    {L : D ⥤ C} {R : C ⥤ D} {l : E ⥤ D} {r : D ⥤ E}
    {K : E ⥤ C} {T : C ⥤ E} (a : l ⊣ r) (b : L ⊣ R) (c : K ⊣ T)
    [L.Additive] [PreservesFiniteColimits L]
    (eR : R ⋙ r ≅ T) (H : D ⥤ D) (eQ : cokernel a.counit ≅ H) :
    ∃ d : T ⋙ K ⟶ R ⋙ L,
      d ≫ b.counit = c.counit ∧ Nonempty (cokernel d ≅ R ⋙ H ⋙ L) := by
  let ab := (a.comp b).ofNatIsoRight eR
  let eL := ab.leftAdjointUniq c
  let e : T ⋙ K ≅ R ⋙ r ⋙ l ⋙ L :=
    isoWhiskerLeft T eL.symm ≪≫ isoWhiskerRight eR.symm (l ⋙ L)
  let A := (whiskeringLeft C D D).obj R
  let B := (whiskeringRight C D C).obj L
  let f := B.map (A.map a.counit)
  let d := e.hom ≫ f
  refine ⟨d, ?_, ?_⟩
  · ext M
    have hc := ab.leftAdjointUniq_hom_app_counit c M
    apply (cancel_epi (eL.hom.app (T.obj M))).1
    dsimp only [d, e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hc]
    simp [ab, Adjunction.ofNatIsoRight_counit, Adjunction.comp_counit_app, f, A, B]
  · refine ⟨cokernel.mapIso d f e (Iso.refl _) (by simp [d]) ≪≫
      (PreservesCokernel.iso B (A.map a.counit)).symm ≪≫
      B.mapIso (PreservesCokernel.iso A a.counit).symm ≪≫
      isoWhiskerRight (isoWhiskerLeft R eQ) L⟩

/-- The quotient for two nested opens is the extension of the closed complement.
Source: Stacks Project, proetale.tex Tag 09AH and sites-modules.tex Tags 03DI--03DJ
(blueprint: lem-sfb-open-filtration-successor).

Proof in words. Put a : W → V. For the cokernel Q of the open counit on V,
restriction to W vanishes by the triangle identity and the fully faithful open
extension. Thus the closed-support theorem makes the closed adjunction unit on Q
invertible. Restriction to S kills a_! a^*, so it sends the cokernel projection to
an isomorphism. Whiskering these two natural isomorphisms identifies Q with t_* t^*.
Precompose with restriction to V and postcompose with exact extension by zero to X.
Composition of adjunctions and the pullback composition isomorphism identify the
first term with W_! W^*. The uniqueness comparison for left adjoints identifies the
composite counit with the W counit. Preservation of cokernels under both whiskering
functors gives the asserted natural quotient. Equal opens, empty opens, and empty
closed complements require no separate choices or nonemptiness hypotheses.
-/
theorem exists_openFiltrationSuccessor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (W V : X.Opens) (h : W ≤ V)
    [QuasiCompact W.ι] [QuasiSeparated W.ι]
    [QuasiCompact V.ι] [QuasiSeparated V.ι]
    [QuasiCompact (V.ι ⁻¹ᵁ W).ι] [QuasiSeparated (V.ι ⁻¹ᵁ W).ι]
    {S : Scheme.{u}} (t : S ⟶ V.toScheme) [IsClosedImmersion t]
    (ht : Set.range t = {x | V.ι x ∉ W}) :
    ∃ d : upperStar Λ W.ι ⋙ openImmersionLowerShriek Λ W.ι ⟶
        upperStar Λ V.ι ⋙ openImmersionLowerShriek Λ V.ι,
      d ≫ (openImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit =
        (openImmersionLowerShriekUpperStarAdjunction Λ W.ι).counit ∧
      Nonempty (cokernel d ≅
        upperStar Λ V.ι ⋙ upperStar Λ t ⋙ lowerStar Λ t ⋙
          openImmersionLowerShriek Λ V.ι) := by
  let j := X.homOfLE h
  have hjt : Set.range j = (Set.range t)ᶜ := by
    rw [ht]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    constructor
    · rintro ⟨w, rfl⟩
      change (j ≫ V.ι) w ∈ W
      rw [X.homOfLE_ι h]
      exact w.property
    · intro hx
      refine ⟨⟨x.val, hx⟩, ?_⟩
      apply V.ι.isEmbedding.injective
      change (j ≫ V.ι) _ = V.ι x
      rw [X.homOfLE_ι h]
      rfl
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ V.ι) := by
      change QuasiCompact (X.homOfLE h ≫ V.ι)
      rw [X.homOfLE_ι h]
      infer_instance
    exact QuasiCompact.of_comp j V.ι
  obtain ⟨eQ⟩ := natural_open_closed_quotient Λ j t hjt
  let eR := (upperStarComp Λ j V.ι).symm ≪≫
    upperStarCongr Λ (X.homOfLE_ι h)
  obtain ⟨d, hd, ⟨ed⟩⟩ := successor_of_adjunctions
    (openImmersionLowerShriekUpperStarAdjunction Λ j)
    (openImmersionLowerShriekUpperStarAdjunction Λ V.ι)
    (openImmersionLowerShriekUpperStarAdjunction Λ W.ι) eR
    (upperStar Λ t ⋙ lowerStar Λ t) eQ
  exact ⟨d, hd, ⟨ed ≪≫ isoWhiskerLeft (upperStar Λ V.ι)
    (associator (upperStar Λ t) (lowerStar Λ t) (openImmersionLowerShriek Λ V.ι))⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
