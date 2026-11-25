/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris

/-! Split endomorphisms of constructible adic sheaves are invertible. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.ProEtale

namespace WeilConjectures

private theorem lisse_splitEndo_isIso {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {F : ProEtale.AdicSheaf l X} (hF : ProEtale.IsAdicLisseSheaf F)
    (f : F ⟶ F) [IsSplitMono f] : IsIso f := by
  classical
  obtain ⟨R, hR, h⟩ := hF
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine ProEtale.isIso_of_isIso_adicUpperStar l g hR f fun i ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := h (g i) (.mk i)
  let a := e.inv ≫ (g i)^*ᵃ[l].map f ≫ e.hom
  let b := e.inv ≫ (g i)^*ᵃ[l].map (retraction f) ≫ e.hom
  have hab : a ≫ b = 𝟙 _ := by
    simp only [a, b, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, IsSplitMono.id, CategoryTheory.Functor.map_id]
    simp
  have hba : b ≫ a = 𝟙 _ := by
    apply ProEtale.AdicSheaf.unitMatrix_injective
    rw [ProEtale.AdicSheaf.unitMatrix_comp, ProEtale.AdicSheaf.unitMatrix_id]
    apply mul_eq_one_comm.mp
    rw [← ProEtale.AdicSheaf.unitMatrix_comp, hab,
      ProEtale.AdicSheaf.unitMatrix_id]
  have : IsIso a := ⟨⟨b, hab, hba⟩⟩
  have heq : (g i)^*ᵃ[l].map f = e.hom ≫ a ≫ e.inv := by simp [a]
  rw [heq]
  infer_instance

/-- A split monic endomorphism of a constructible adic sheaf is invertible.

Source: the finite-constructibility argument in the current blueprint,
`cor-coef-verdier-weil-equivariance.proof.md`, final exceptional-adjunction sentence.
On each lisse stratum, trivialize the sheaf on a pro-etale cover. The endomorphism
and its left inverse give square matrices over the commutative ring of locally
finite coefficient functions. A one-sided inverse of a square matrix is two-sided.
Thus each restriction is invertible. Finite jointly surjective quasi-compact
strata detect isomorphisms. This includes zero rank and empty strata.
(blueprint: lem-sf-constructible-split-endomorphism). -/
theorem constructible_splitEndo_isIso {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    {F : ProEtale.AdicSheaf l X} (hF : ProEtale.IsAdicConstructibleSheaf F)
    (f : F ⟶ F) [IsSplitMono f] : IsIso f := by
  obtain ⟨ι, hι, Z, g, hg, _, hcover, h⟩ := hF.isAdicStratifiedLisseSheaf
  have := hι
  have (i : ι) : IsImmersion (g i) := hg i
  have : IsNoetherian X := ⟨⟩
  have (i : ι) : TopologicalSpace.NoetherianSpace (Z i) :=
    (g i).isEmbedding.isInducing.noetherianSpace
  have (i : ι) : QuasiCompact (g i) := inferInstance
  exact ProEtale.isIso_of_forall_isIso_adicUpperStar_map g
    (fun x ↦ (hcover x).exists) f
    (fun i ↦ lisse_splitEndo_isIso (h i) ((g i)^*ᵃ[l].map f))

end WeilConjectures
