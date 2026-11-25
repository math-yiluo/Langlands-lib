/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModuleMap
public import WeilConjectures.AlgebraicGeometry.Sites.GaloisCoverInvariantSections
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarEtaleSections
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.RepresentationTheory.DiscreteModule.Sylow
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyPullback

/-!
# One step of the dévissage of sheaves with finite `ℓ`-group monodromy

Let `c : P ⟶ V` be a Galois cover with group a finite `ℓ`-group `G` and connected total space,
and `H` a sheaf of `Λ`-modules on `V_ét` with `π^* H ≅ M_P` for a nonzero finite `Λ`-module `M`,
`ℓ` nilpotent in `Λ`. The group `G` acts on `H(P) ≅ M`, and a nonzero fixed vector killed by `ℓ`
descends to a nonzero global section `y` of `H` killed by `ℓ` (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, dévissage).

## Main statements

- `AlgebraicGeometry.Etale.exists_ne_zero_smul_eq_zero_of_connected_cover`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {V : Scheme.{u}} (ℓ : ℕ) {Λ : Type (u + 1)} [CommRing Λ]
  {G : Type (u + 1)} [Group G] [Finite G] (c : V.GaloisCover G) [ConnectedSpace c.P]

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1` (dévissage): if a sheaf `H` of
`Λ`-modules, `ℓ` nilpotent in `Λ`, is trivialized by a Galois cover with connected total space and
group a finite `ℓ`-group, with nonzero finite value `M`, then `H` has a nonzero global section
killed by `ℓ`: it descends from a nonzero fixed vector, killed by `ℓ`, of the group acting on
`H(P) ≅ M`. -/
theorem exists_ne_zero_smul_eq_zero_of_connected_cover [Fact ℓ.Prime]
    (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (hG : IsPGroup ℓ G) (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (M : ModuleCat.{u + 1} Λ) [Finite M] [Nontrivial M]
    (φ : (c.π)^*[ModuleCat.{u + 1} Λ].obj H ≅
      (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :
    ∃ y : H.obj.obj (op (⊤_ V.Etale)), y ≠ 0 ∧ (ℓ : Λ) • y = 0 := by
  have := c.etale
  let A := H.obj.obj (op c.etaleObj)
  let e : A ≅ M := ((upperStarCompSectionsIso c.π (ModuleCat.{u + 1} Λ)).app H).symm ≪≫
    ((sheafSections _ _).obj (op (⊤_ c.P.Etale))).mapIso φ ≪≫
    (asIso ((constantSheafAdj c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).unit.app M)).symm
  have : Finite A := Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm
  have : Nontrivial A := e.toLinearEquiv.toEquiv.nontrivial
  have h₁ (x : A) : H.obj.map (c.smulEtale 1⁻¹).op x = x := by
    rw [inv_one, Scheme.GaloisCover.smulEtale_one, op_id, H.obj.map_id]
    rfl
  have h₂ (g h : G) (x : A) : H.obj.map (c.smulEtale (g * h)⁻¹).op x =
      H.obj.map (c.smulEtale g⁻¹).op (H.obj.map (c.smulEtale h⁻¹).op x) := by
    rw [mul_inv_rev, Scheme.GaloisCover.smulEtale_mul, op_comp, Functor.map_comp]
    rfl
  let _ : DistribMulAction G A :=
    { smul g x := H.obj.map (c.smulEtale g⁻¹).op x
      one_smul := h₁
      mul_smul := h₂
      smul_zero _ := map_zero _
      smul_add _ _ _ := map_add _ _ _ }
  obtain ⟨n, hn⟩ := hΛ
  obtain ⟨v, hv0, hvℓ, hvG⟩ := exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup (A := A) ℓ ⊥
    (fun g hg a ↦ by rw [Subgroup.mem_bot.1 hg, one_smul])
    (fun g ↦ (hG g).imp fun j hj ↦ hj ▸ Subgroup.one_mem _) fun a ↦
    ⟨n, by rw [← Nat.cast_smul_eq_nsmul Λ, Nat.cast_pow, hn, zero_smul]⟩
  have hE : Presheaf.IsSheaf V.smallEtaleTopology (H.obj ⋙ forget (ModuleCat.{u + 1} Λ)) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ _).mp H.property
  have hsmul (g : G) (x : A) : g • x = H.obj.map (c.smulEtale g⁻¹).op x := rfl
  obtain ⟨y, hy⟩ := c.exists_map_eq_of_forall_smul hE v fun g ↦ by
    have := hvG g⁻¹
    rwa [hsmul, inv_inv] at this
  have hinj := Scheme.Etale.map_injective_of_surjective hE (terminal.from c.etaleObj)
    c.surjective_terminal_from_left
  have hy' : (H.obj.map (terminal.from c.etaleObj).op).hom y = v := hy
  refine ⟨y, fun h ↦ hv0 ?_, hinj ?_⟩
  · rw [← hy', h]
    exact map_zero _
  · rw [← Nat.cast_smul_eq_nsmul Λ] at hvℓ
    refine (map_smul (H.obj.map (terminal.from c.etaleObj).op).hom (ℓ : Λ) y).trans
      ((congrArg ((ℓ : Λ) • ·) hy').trans ?_)
    rw [hvℓ]
    exact (map_zero (H.obj.map (terminal.from c.etaleObj).op).hom).symm

variable [Finite Λ]

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1` (dévissage): let `H` be trivialized
by a Galois cover `c` with connected total space, `π^* H ≅ M_P`, and let `y` be a nonzero global
section of `H` killed by `ℓ`. The submodule `N = Λ y` gives a monomorphism `χ : N_V ⟶ H` whose
cokernel is trivialized by the same cover, with value a quotient `M'` of `M` of smaller
cardinality. -/
theorem exists_mono_constantSheaf_of_connected_cover
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (φ : (c.π)^*[ModuleCat.{u + 1} Λ].obj H ≅
      (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    (y : H.obj.obj (op (⊤_ V.Etale))) (hy0 : y ≠ 0) (hyℓ : (ℓ : Λ) • y = 0) :
    ∃ (N : ModuleCat.{u + 1} Λ) (_ : Finite N) (_ : ∀ n : N, (ℓ : Λ) • n = 0)
      (χ : (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ⟶ H) (_ : Mono χ)
      (M' : ModuleCat.{u + 1} Λ) (_ : Finite M'), Nat.card M' < Nat.card M ∧
      Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj (cokernel χ) ≅
        (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M') := by
  have := c.etale
  let N := ModuleCat.of Λ (Λ ∙ y)
  have : Finite N := Module.finite_of_finite Λ
  have : Nontrivial N := (Submodule.nontrivial_span_singleton hy0)
  let adj := constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal
  let χ := (adj.homEquiv N H).symm (ModuleCat.ofHom (Λ ∙ y).subtype)
  let adjP := constantSheafAdj c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal
  let r := terminal.from c.etaleObj
  have hE : Presheaf.IsSheaf V.smallEtaleTopology (H.obj ⋙ forget (ModuleCat.{u + 1} Λ)) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ _).mp H.property
  have hres : Function.Injective (H.obj.map r.op) :=
    Scheme.Etale.map_injective_of_surjective hE r c.surjective_terminal_from_left
  -- the composite `N ⟶ Γ(V, N_V) ⟶ N_V(P) ⟶ H(P)` is the restriction of `N ⊆ Γ(V, H)`
  have hχ : adj.unit.app N ≫ χ.hom.app (op (⊤_ V.Etale)) = ModuleCat.ofHom (Λ ∙ y).subtype :=
    (adj.homEquiv_unit N H χ).symm.trans ((adj.homEquiv N H).apply_symm_apply _)
  let ρ := adj.unit.app N ≫ ((constantSheaf V.smallEtaleTopology _).obj N).obj.map r.op
  have hcomp : Function.Injective (ρ ≫ χ.hom.app (op c.etaleObj)) := by
    rw [Category.assoc, χ.hom.naturality r.op, ← Category.assoc, hχ]
    exact hres.comp Subtype.val_injective
  have hcomp' : Function.Injective fun a ↦ χ.hom.app (op c.etaleObj) (ρ a) := hcomp
  -- `N_V(P) ≅ Γ(P, π^* N_V) ≅ Γ(P, N_P) ≅ N`, so `ρ` is bijective by counting
  let eN : ((constantSheaf V.smallEtaleTopology _).obj N).obj.obj (op c.etaleObj) ≅ N :=
    ((upperStarCompSectionsIso c.π (ModuleCat.{u + 1} Λ)).app _).symm ≪≫
      ((sheafSections _ _).obj (op (⊤_ c.P.Etale))).mapIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) c.π).app N) ≪≫
      (asIso (adjP.unit.app N)).symm
  have : Finite (((constantSheaf V.smallEtaleTopology _).obj N).obj.obj (op c.etaleObj)) :=
    Finite.of_equiv _ eN.toLinearEquiv.toEquiv.symm
  have hρ : Function.Bijective ρ := Function.Injective.bijective_of_nat_card_le
    (fun a b h ↦ hcomp' (congrArg _ h))
    (Nat.card_congr eN.toLinearEquiv.toEquiv).le
  have hχP : Function.Injective (χ.hom.app (op c.etaleObj)) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := hρ.2 a
    obtain ⟨b, rfl⟩ := hρ.2 b
    exact congrArg ρ (hcomp' hab)
  -- the pullback of `χ` to `P` is a morphism of constant sheaves, injective on sections
  let eNP := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) c.π).app N
  let ψ := eNP.inv ≫ (c.π)^*[ModuleCat.{u + 1} Λ].map χ ≫ φ.hom
  let Γ := (sheafSections c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (⊤_ c.P.Etale))
  have hπχ : Function.Injective (Γ.map ((c.π)^*[ModuleCat.{u + 1} Λ].map χ)) := by
    have h := (upperStarCompSectionsIso c.π (ModuleCat.{u + 1} Λ)).hom.naturality χ
    have h' : Function.Injective (Γ.map ((c.π)^*[ModuleCat.{u + 1} Λ].map χ) ≫
        (upperStarCompSectionsIso c.π (ModuleCat.{u + 1} Λ)).hom.app H) := by
      erw [h]
      exact hχP.comp (ConcreteCategory.bijective_of_isIso
        ((upperStarCompSectionsIso c.π (ModuleCat.{u + 1} Λ)).hom.app _)).injective
    exact fun a b hab ↦ h' (congrArg (ConcreteCategory.hom
      ((upperStarCompSectionsIso c.π (ModuleCat.{u + 1} Λ)).hom.app H)) hab)
  have hψ : Function.Injective (ψ.hom.app (op (⊤_ c.P.Etale))) :=
    ((ConcreteCategory.bijective_of_isIso (Γ.map φ.hom)).injective.comp hπχ).comp
      (ConcreteCategory.bijective_of_isIso (Γ.map eNP.inv)).injective
  obtain ⟨f, hf, hfψ⟩ := Scheme.exists_injective_constantSheaf_map_eq ψ hψ
  have : Mono f := (ModuleCat.mono_iff_injective f).2 hf
  have hπχ' : (c.π)^*[ModuleCat.{u + 1} Λ].map χ =
      eNP.hom ≫ (constantSheaf c.P.smallEtaleTopology _).map f ≫ φ.inv := by
    rw [hfψ]
    simp [ψ]
  have : Mono ((c.π)^*[ModuleCat.{u + 1} Λ].map χ) := by
    rw [hπχ']
    infer_instance
  have := Etale.faithful_upperStar_of_surjective Λ c.π c.surjective.surj
  have : Mono χ := Functor.mono_of_mono_map ((c.π)^*[ModuleCat.{u + 1} Λ]) inferInstance
  have : Finite (M ⧸ LinearMap.range f.hom) := Module.finite_of_finite Λ
  refine ⟨N, inferInstance, fun n ↦ ?_, χ, inferInstance,
    ModuleCat.of Λ (M ⧸ LinearMap.range f.hom),
    inferInstance, ?_, ⟨PreservesCokernel.iso ((c.π)^*[ModuleCat.{u + 1} Λ]) χ ≪≫
      cokernelIsoOfEq hπχ' ≪≫ cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
      (PreservesCokernel.iso (constantSheaf c.P.smallEtaleTopology _) f).symm ≪≫
      (constantSheaf c.P.smallEtaleTopology _).mapIso (ModuleCat.cokernelIsoRangeQuotient f)⟩⟩
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 n.2
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, ← ha, smul_comm, hyℓ, smul_zero, Submodule.coe_zero]
  · have h := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f.hom)
    have h₁ : Nat.card (LinearMap.range f.hom) = Nat.card N :=
      (Nat.card_congr (LinearEquiv.ofInjective f.hom hf).toEquiv).symm
    have h₂ : 1 < Nat.card N := Finite.one_lt_card_iff_nontrivial.2 inferInstance
    have h₃ : 0 < Nat.card (M ⧸ LinearMap.range f.hom) := Nat.card_pos
    rw [h, h₁]
    nlinarith

end AlgebraicGeometry.Etale
