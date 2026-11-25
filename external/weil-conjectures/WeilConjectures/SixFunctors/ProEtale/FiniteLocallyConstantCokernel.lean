/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteLocallyConstantCokernel.ConstantPullback

/-!
# Cokernels of morphisms of constant pro-étale sheaves are locally constant

Let `Λ` be a commutative ring and `X` a scheme. This file shows that the cokernel of a
morphism `φ : M_X ⟶ N_X` between the constant pro-étale sheaves of `Λ`-modules of finitely
generated modules `M` and `N` is locally constant with finitely generated stalks
(`AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_cokernel`). The morphism `φ` is determined
by the global sections of `N_X` that are the images of generators of `M`; global sections of the
sheafification of the constant presheaf are locally constant, so on the members of a pro-étale
covering family `φ` is the constant morphism of a linear map `ψ : M ⟶ N`, and there the cokernel
is the constant sheaf of the finitely generated module `N ⧸ ψ(M)`.

## Main statements

- `AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant.of_cover`: being locally constant with
  finitely generated stalks is local for the pro-étale topology.
- `AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_cokernel`: the cokernel of a morphism of
  constant sheaves of finitely generated modules is locally constant with finitely generated
  stalks.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Being locally constant with finitely generated stalks is local for the pro-étale topology:
if the pullbacks of `F` along the members of a pro-étale covering family are locally constant
with finitely generated stalks, so is `F` (compose the covering families). -/
theorem IsFiniteLocallyConstant.of_cover {X : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} {ι : Type (u + 1)}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, IsFiniteLocallyConstant Λ (((g i))^*[ModuleCat.{u + 1} Λ].obj F)) :
    IsFiniteLocallyConstant Λ F := by
  choose ι' W' g' hg' hc using h
  refine ⟨Σ i, ι' i, fun p ↦ W' p.1 p.2, fun p ↦ g' p.1 p.2 ≫ g p.1,
    Precoverage.comp_mem_coverings g hg g' hg', fun p ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hc p.1 p.2
  exact ⟨M, hM, ⟨(upperStarComp _ (g' p.1 p.2) (g p.1)).app F ≪≫ e⟩⟩

/-- The cokernel of a morphism `(Λⁿ)_X ⟶ N_X` of constant pro-étale sheaves, with `N` finitely
generated, is locally constant with finitely generated stalks. The images `s_j ∈ Γ(X, N_X)` of
the basis vectors are constant on the members `V` of a pro-étale cover, `s_j|_V = n_j`; on `V`
the morphism is then the constant morphism of the linear map `ψ : Λⁿ ⟶ N` sending the `j`-th
basis vector to `n_j`, and the cokernel is the constant sheaf of `N ⧸ ψ(Λⁿ)`. -/
theorem isFiniteLocallyConstant_cokernel_of_free {X : Scheme.{u}} {n : ℕ}
    {N : ModuleCat.{u + 1} Λ} [Module.Finite Λ N]
    (φ : (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin n → Λ)) ⟶
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj N) :
    IsFiniteLocallyConstant Λ (cokernel φ) := by
  classical
  let adj := constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} Λ) (ProEt.isTerminalMkId X)
  obtain ⟨S, hS, hx⟩ := (ProEt.topology X).exists_mem_forall_exists_toSheafify_const_app_eq N
    (U := ProEt.mk (𝟙 X)) (fun j : Fin n ↦ (adj.homEquiv _ _ φ).hom (Pi.single j 1))
  obtain ⟨R, hR, hRS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : (f i).left = (Y i).hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w (f i))
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hR
  refine ⟨ι, fun i ↦ (Y i).left, fun i ↦ (Y i).hom, ?_, fun i ↦ ?_⟩
  · have e : (fun i ↦ (Y i).hom) = fun i ↦ (ProEt.forget X ⋙ Over.forget X).map (f i) :=
      funext fun i ↦ (hf i).symm
    rw [e]
    exact hR
  · have hn (j : Fin n) := hx (f i) (hRS _ _ (Presieve.ofArrows.mk i)) j
    choose m hm using hn
    let ψ : ModuleCat.of Λ (Fin n → Λ) ⟶ N :=
      ModuleCat.ofHom ((Pi.basisFun Λ (Fin n)).constr Λ m)
    have h : adj.homEquiv _ _ φ ≫ ((constantSheaf _ _).obj N).obj.map (f i).op =
        ψ ≫ adj.unit.app N ≫ ((constantSheaf _ _).obj N).obj.map (f i).op := by
      rw [constantSheafAdj_unit_app_comp_map]
      refine ModuleCat.hom_ext ((Pi.basisFun Λ (Fin n)).ext fun j ↦ ?_)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ψ, ModuleCat.hom_ofHom]
      rw [Module.Basis.constr_basis, Pi.basisFun_apply]
      exact (hm j).symm
    refine ⟨ModuleCat.of Λ (N ⧸ LinearMap.range ψ.hom),
      inferInstance, ⟨upperStarCokernelIsoOfEq _ φ ψ
        (constantSheafCompUpperStarMkIdIso_inv_app_comp_map_comp_hom_app _ _ (f i)
          (MorphismProperty.Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl)
            (pullback.lift_snd _ _ _)) φ ψ h)⟩⟩

/-- The cokernel of a morphism `M_X ⟶ N_X` of constant pro-étale sheaves, with `M` and `N`
finitely generated, is locally constant with finitely generated stalks. -/
theorem isFiniteLocallyConstant_cokernel {X : Scheme.{u}}
    {M N : ModuleCat.{u + 1} Λ} [Module.Finite Λ M] [Module.Finite Λ N]
    (φ : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj M ⟶
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj N) :
    IsFiniteLocallyConstant Λ (cokernel φ) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ M
  have : Epi (ModuleCat.ofHom π) := (ModuleCat.epi_iff_surjective _).2 hπ
  have := (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} Λ)
    (ProEt.isTerminalMkId X)).isLeftAdjoint
  exact isFiniteLocallyConstant_of_iso (cokernelEpiComp _ φ)
    (isFiniteLocallyConstant_cokernel_of_free
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).map (ModuleCat.ofHom π) ≫ φ))

end AlgebraicGeometry.ProEtale
