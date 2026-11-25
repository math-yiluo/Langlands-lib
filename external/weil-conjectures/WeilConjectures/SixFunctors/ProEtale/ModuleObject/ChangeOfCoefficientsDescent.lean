/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.KernelDescent

/-!
# Descending a locally free module along a change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, `S` a scheme and `L` a module
object over `Λ'_S`. Suppose given a finite pro-étale cover `{f_k : V_k ⟶ S}` and, on each `V_k`,
a free sub-`Λ_{V_k}`-module `σ_k : Λ_{V_k}^{n_k} ⟶ f_k^* Res L`, presented as the kernel of some
`π_k`, such that the `π_k` agree on the fibre products `V_j ×_S V_k` and the adjoints
`Λ'_{V_k} ⊗ Λ_{V_k}^{n_k} ⟶ f_k^* L` of the `σ_k` are isomorphisms. Then the kernel `L'` of the
`π_k` (`ProEtale.CondensedRing.kernelDescentMap`) is a locally free `Λ_S`-module with
`Λ'_S ⊗_{Λ_S} L' ≅ L` (`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- **Descent of a module along a change of coefficients, from compatible free submodules on a
finite pro-étale cover.** See the module docstring. -/
theorem exists_isLocallyFree_extendScalars_iso_of_cover {S : Scheme.{u}}
    (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) [Finite 𝒰.I₀]
    (Q : ∀ k, Mod (Sheaf (ProEt.topology (𝒰.X k)) Ab.{u + 1}) (condensedRingObj Λ (𝒰.X k)))
    (π : ∀ k, (𝒰.f k)^*⟦Λ⟧.obj ((Mod.comap (coefficientMap a S)).obj L) ⟶ Q k)
    {P : 𝒰.I₀ → 𝒰.I₀ → Scheme.{u}} {p₁ : ∀ j k, P j k ⟶ 𝒰.X j} {p₂ : ∀ j k, P j k ⟶ 𝒰.X k}
    (hP : ∀ j k, IsPullback (p₁ j k) (p₂ j k) (𝒰.f j) (𝒰.f k))
    (ψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.obj (Q j) ≅ (p₂ j k)^*⟦Λ⟧.obj (Q k))
    (hψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.map (π j) ≫ (ψ j k).hom =
      (upperStarSquareComparison Λ (hP j k).flip.toCommSq).hom.app
        ((Mod.comap (coefficientMap a S)).obj L) ≫
        (p₂ j k)^*⟦Λ⟧.map (π k))
    (hσ : ∀ k, ∃ (n : ℕ) (σ : Mod.finiteFree (condensedRingObj Λ (𝒰.X k)) n ⟶
        (𝒰.f k)^*⟦Λ⟧.obj ((Mod.comap (coefficientMap a S)).obj L))
      (hσ : σ ≫ π k = 0), Nonempty (IsLimit (KernelFork.ofι σ hσ)) ∧
      IsIso (((Mod.extendRestrictAdjunction (coefficientMap a (𝒰.X k))).homEquiv _ _).symm
        (σ ≫ (comapUpperStarIso a (𝒰.f k)).inv.app L))) :
    ∃ L' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
      IsLocallyFree (condensedRingObj Λ S) L' ∧
        Nonempty ((Mod.extendScalars (coefficientMap a S)).obj L' ≅ L) := by
  have (k : 𝒰.I₀) : WeaklyEtale (𝒰.f k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk k)
  choose n σ hσ₀ hl hiso using hσ
  choose e he using fun k ↦
    exists_iso_upperStar_kernel_kernelDescentMap hP hψ k (σ k) (hσ₀ k) (hl k).some
  have hK : IsIso (((Mod.extendRestrictAdjunction (coefficientMap a S)).homEquiv _ _).symm
      (kernel.ι (kernelDescentMap Λ 𝒰.f ((Mod.comap (coefficientMap a S)).obj L) π))) := by
    refine isIso_homEquiv_symm_of_cover a _ 𝒰 fun k ↦ ?_
    rw [(Iso.eq_inv_comp (e k)).2 (he k), Category.assoc,
      Adjunction.homEquiv_naturality_left_symm]
    have := hiso k
    infer_instance
  exact ⟨_, isLocallyFree_of_isFree_upperStar 𝒰 fun k ↦ ⟨n k, ⟨(e k).symm⟩⟩,
    ⟨@asIso _ _ _ _ _ hK⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
