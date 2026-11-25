/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverSetFLC
public import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitInducedMaps
public import WeilConjectures.Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The limit of a tower of finite modules as a group of compatible families

For a tower `G` of finite modules over a ring `Λ`, the limit `C(-, lim_n Gₙ)` of the abelian
tower underlying the constant sheaves `(Gₙ)_X`
(`AlgebraicGeometry.Scheme.UniversalCovers.exists_isLimit_towerComparisonUpperStar'`) is taken
with `lim_n Gₙ` the group `AlgebraicGeometry.ProEtale.towerLimitAddSubgroup` of compatible
families of the discrete groups `DiscreteShrink Gₙ`. This file identifies it with the limit of
`G` in `ModuleCat Λ`:

- `ModuleCat.limitAddEquivTowerLimit`: `lim G ≃ lim_n DiscreteShrink Gₙ` as abelian groups;
- `ModuleCat.towerLimitModule`: the induced `Λ`-module structure on the compatible families, for
  which `ModuleCat.limitLinearEquivTowerLimit` is `Λ`-linear, so that the compatible families
  form a finite `Λ`-module as soon as `lim G` does (`ModuleCat.towerLimit_finite`), e.g. by
  `AlgebraicGeometry.Etale.finite_limit_stalkHomologyRightDerivedLowerStar_of_flcProperty`;
- `ModuleCat.towerLimitModuleOf`: the module structure over a ring `R ≃ Λ` (e.g. `𝒪_E` for
  `Λ = Shrink 𝒪_E`), finite if `lim G` is (`ModuleCat.towerLimit_finite_of_ringEquiv`);
- `ModuleCat.towerLimit_isModuleTopology`: if `R` is compact and acts on each `Gₙ` through a
  discrete quotient, the limit topology is the module topology (the `ℓ`-adic topology for
  `R = 𝒪_E`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace ModuleCat

variable {Λ : Type (u + 1)} [Ring Λ] (G : ℕᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
  [∀ n : ℕ, Small.{0} (G.obj (op n))]

/-- The compatible families of the discrete groups `DiscreteShrink Gₙ` attached to a tower of
small modules. -/
noncomputable abbrev towerLimit : AddSubgroup (∀ n, DiscreteShrink (G.obj (op n))) :=
  AlgebraicGeometry.ProEtale.towerLimitAddSubgroup
    (Qs := fun n ↦ DiscreteShrink (G.obj (op n)))
    (fun n ↦ DiscreteShrink.map (G.map (homOfLE (n.le_add_right 1)).op).hom.toAddMonoidHom)

lemma mem_towerLimit_iff (x : ∀ n, DiscreteShrink (G.obj (op n))) :
    x ∈ towerLimit G ↔ ∀ n, G.map (homOfLE (n.le_add_right 1)).op
      ((DiscreteShrink.addEquiv _).symm (x (n + 1))) = (DiscreteShrink.addEquiv _).symm (x n) := by
  refine forall_congr' fun n ↦ ?_
  change DiscreteShrink.addEquiv _ _ = _ ↔ _
  rw [← (DiscreteShrink.addEquiv _).symm.injective.eq_iff, AddEquiv.symm_apply_apply]
  exact Iff.rfl

/-- The limit of a tower of small modules is the group of compatible families of the discrete
groups `DiscreteShrink Gₙ`. -/
noncomputable def limitAddEquivTowerLimit : ↑(limit G) ≃+ towerLimit G where
  toFun z := ⟨fun n ↦ DiscreteShrink.addEquiv _ (limit.π G (op n) z), (mem_towerLimit_iff G _).2
    fun n ↦ by
      simp only [AddEquiv.symm_apply_apply]
      rw [← ConcreteCategory.comp_apply, limit.w]⟩
  invFun x := towerLimitMk (fun n ↦ (DiscreteShrink.addEquiv _).symm (x.1 n))
    ((mem_towerLimit_iff G _).1 x.2)
  left_inv z := Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ by
    simp only [limit_π_towerLimitMk, AddEquiv.symm_apply_apply]
  right_inv x := Subtype.ext (funext fun n ↦ by
    simp only [limit_π_towerLimitMk, AddEquiv.apply_symm_apply])
  map_add' z z' := Subtype.ext (funext fun n ↦ by
    simp only [map_add]
    rfl)

@[simp]
lemma limitAddEquivTowerLimit_apply_coe (z : ↑(limit G)) (n : ℕ) :
    (limitAddEquivTowerLimit G z).1 n = DiscreteShrink.addEquiv _ (limit.π G (op n) z) :=
  rfl

/-- The `Λ`-module structure on the compatible families, transported from `lim G`. -/
noncomputable abbrev towerLimitModule : Module Λ (towerLimit G) :=
  letI : SMul Λ (towerLimit G) :=
    ⟨fun r x ↦ limitAddEquivTowerLimit G (r • (limitAddEquivTowerLimit G).symm x)⟩
  Function.Injective.module Λ (limitAddEquivTowerLimit G).symm.toAddMonoidHom
    (limitAddEquivTowerLimit G).symm.injective fun r x ↦ by
      change (limitAddEquivTowerLimit G).symm (limitAddEquivTowerLimit G _) = _
      rw [AddEquiv.symm_apply_apply]
      rfl

/-- `lim G` and the compatible families of the `DiscreteShrink Gₙ` are isomorphic `Λ`-modules. -/
noncomputable def limitLinearEquivTowerLimit :
    letI := towerLimitModule G
    ↑(limit G) ≃ₗ[Λ] towerLimit G :=
  let := towerLimitModule G
  (limitAddEquivTowerLimit G).toLinearEquiv fun r z ↦ by
    change _ = limitAddEquivTowerLimit G
      (r • (limitAddEquivTowerLimit G).symm (limitAddEquivTowerLimit G z))
    rw [AddEquiv.symm_apply_apply]

/-- The compatible families form a finite `Λ`-module if `lim G` is finite. -/
lemma towerLimit_finite [Module.Finite Λ ↑(limit G)] :
    letI := towerLimitModule G
    Module.Finite Λ (towerLimit G) :=
  let := towerLimitModule G
  Module.Finite.equiv (limitLinearEquivTowerLimit G)

section Scalars

variable {R : Type*} [CommRing R] (φ : R ≃+* Λ)

/-- The `R`-module structure on the compatible families, through a ring isomorphism
`φ : R ≃ Λ` (e.g. `𝒪_E ≃ Shrink 𝒪_E`). -/
noncomputable abbrev towerLimitModuleOf : Module R (towerLimit G) :=
  let := towerLimitModule G
  Module.compHom _ φ.toRingHom

lemma towerLimit_smul_apply (r : R) (x : towerLimit G) (n : ℕ) :
    letI := towerLimitModuleOf G φ
    (r • x).1 n = DiscreteShrink.addEquiv _
      (φ r • (DiscreteShrink.addEquiv _).symm (x.1 n)) := by
  change (limitAddEquivTowerLimit G (φ r • (limitAddEquivTowerLimit G).symm x)).1 n = _
  rw [limitAddEquivTowerLimit_apply_coe, map_smul]
  exact congrArg (fun z ↦ DiscreteShrink.addEquiv _ (φ r • z))
    (limit_π_towerLimitMk (fun n ↦ (DiscreteShrink.addEquiv _).symm (x.1 n))
      ((mem_towerLimit_iff G _).1 x.2) n)

/-- The compatible families form a finite `R`-module if `lim G` is a finite `Λ`-module. -/
lemma towerLimit_finite_of_ringEquiv [Module.Finite Λ ↑(limit G)] :
    letI := towerLimitModuleOf G φ
    Module.Finite R (towerLimit G) := by
  let := towerLimitModule G
  have := towerLimit_finite G
  let := towerLimitModuleOf G φ
  let f : towerLimit G →ₛₗ[φ.symm.toRingHom] towerLimit G :=
    { toFun := id
      map_add' _ _ := rfl
      map_smul' c x := by
        change _ = φ (φ.symm c) • x
        rw [RingEquiv.apply_symm_apply]
        rfl }
  have : RingHomSurjective φ.symm.toRingHom := ⟨φ.symm.surjective⟩
  exact (LinearMap.finite_iff_of_bijective f Function.bijective_id).1 inferInstance

variable [TopologicalSpace R]

/-- With the limit topology, the compatible families form a topological `R`-module as soon as
`R` acts on each `Gₙ` through a discrete quotient. -/
lemma towerLimit_continuousSMul
    (hG : ∀ n (m : G.obj (op n)), IsLocallyConstant fun r : R ↦ φ r • m) :
    letI := towerLimitModuleOf G φ
    ContinuousSMul R (towerLimit G) := by
  let := towerLimitModuleOf G φ
  refine ⟨Continuous.subtype_mk (continuous_pi fun n ↦ ?_) _⟩
  have hg : Continuous fun p : R × DiscreteShrink (G.obj (op n)) ↦
      DiscreteShrink.addEquiv _ (φ p.1 • (DiscreteShrink.addEquiv _).symm p.2) :=
    continuous_prod_of_discrete_right.2 fun d ↦
      ((hG n ((DiscreteShrink.addEquiv _).symm d)).comp (DiscreteShrink.addEquiv _)).continuous
  have hx : Continuous fun p : R × towerLimit G ↦ (p.1, p.2.1 n) :=
    continuous_fst.prodMk ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))
  exact (hg.comp hx).congr fun p ↦ (towerLimit_smul_apply G φ p.1 p.2 n).symm

/-- **The limit topology is the module topology**: over a compact ring `R` acting on each `Gₙ`
through a discrete quotient (e.g. `R = 𝒪_E` and `Gₙ` killed by `𝔪_Eⁿ⁺¹`), if `lim G` is a finite
`Λ`-module then the compatible families, with the limit topology, carry the module topology. -/
lemma towerLimit_isModuleTopology [IsTopologicalRing R] [CompactSpace R]
    [Module.Finite Λ ↑(limit G)]
    (hG : ∀ n (m : G.obj (op n)), IsLocallyConstant fun r : R ↦ φ r • m) :
    letI := towerLimitModuleOf G φ
    IsModuleTopology R (towerLimit G) :=
  let := towerLimitModuleOf G φ
  have := towerLimit_finite_of_ringEquiv G φ
  have := towerLimit_continuousSMul G φ hG
  IsModuleTopology.of_compactSpace

end Scalars

end ModuleCat
