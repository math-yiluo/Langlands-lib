/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.ProfiniteInvariants

/-!
# Duality commutes with invariants under a pro-`p` group

Let `G` be a compact topological group and `A` a commutative ring in which the index of every
open normal subgroup of `G` is invertible (e.g. `G` pro-`p` and `p` invertible in `A`). Let `ρ`
be a *discrete* representation of `G` on an `A`-module `E` and let `ω` be an `A`-module with
trivial action. The group `G` acts on `Hom_A(E, ω)` by the contragredient action
`(g • f)(v) = f(ρ g⁻¹ v)` (`Representation.linHom ρ (Representation.trivial A G ω)`).
We show
(`Representation.invariantsDualEquiv`) that restriction to the invariants is an isomorphism
```
Hom_A(E, ω)^G ≃ Hom_A(E^G, ω),
```
with inverse `φ ↦ φ ∘ avg`, where `avg = Representation.discreteAverage` is the averaging
retraction `E → E^G`. This is the module-level profinite step of blueprint
`lemma-duality-invariants-pro-p--1`; the finite-group core in an arbitrary linear category is
`CategoryTheory.invariantsDualIso`. Note that no finiteness hypothesis on `E` is needed: an
invariant functional is automatically constant on the fibres of the averaging map
(`Representation.map_discreteAverage_of_mem_invariants`).

The corresponding pairing `E^G × Hom_A(E, ω)^G → ω` is evaluation restricted to the invariant
direct summands (`Representation.invariantsDualEquiv_apply`), and an invariant functional is
determined by this pairing: `f v = ⟨avg v, f⟩`
(`Representation.apply_eq_invariantsDualEquiv_discreteAverage`).
-/

@[expose] public section

namespace Representation

variable {G A E ω : Type*} [Group G] [CommRing A] [AddCommGroup E] [Module A E]
  [AddCommGroup ω] [Module A ω] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ρ : Representation A G E}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
/-- A functional `f : E → ω` is invariant for the contragredient action iff `f ∘ ρ g = f` for
all `g`. -/
lemma mem_linHom_trivial_invariants_iff (f : E →ₗ[A] ω) :
    f ∈ (linHom ρ (trivial A G ω)).invariants ↔ ∀ g v, f (ρ g v) = f v := by
  refine ⟨fun hf g v ↦ ?_, fun hf g ↦ ?_⟩
  · have := LinearMap.congr_fun (hf g⁻¹) v
    simpa using this
  · ext v
    simp [hf]

/-- The averaging retraction of a discrete representation is invariant: `avg (ρ g v) = avg v`. -/
lemma discreteAverage_apply_apply
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) (g : G) (v : E) :
    discreteAverage hA hρ (ρ g v) = discreteAverage hA hρ v := by
  obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
  have hgv (h : G) (hh : h ∈ U) : ρ h (ρ g v) = ρ g v := by
    have hconj : h * g = g * (g⁻¹ * h * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply,
      hU _ (Subgroup.Normal.conj_mem' inferInstance h hh g)]
  ext
  rw [discreteAverage_eq hA hρ hgv, discreteAverage_eq hA hρ hU, cosetSum_apply_apply hU]

/-- An invariant functional factors through the averaging retraction: if `f ∘ ρ g = f` for all
`g`, then `f (avg v) = f v`. -/
lemma map_discreteAverage_of_mem_invariants
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) {f : E →ₗ[A] ω} (hf : f ∈ (linHom ρ (trivial A G ω)).invariants)
    (v : E) : f (discreteAverage hA hρ v) = f v := by
  rw [mem_linHom_trivial_invariants_iff] at hf
  obtain ⟨U, hU⟩ := hρ.exists_openNormalSubgroup v
  have hπ : ∀ g, f ∘ₗ ρ g = trivial A G ω g ∘ₗ f := fun g ↦ by
    ext w
    simp [hf]
  rw [discreteAverage_eq hA hρ hU, map_smul, map_cosetSum (ρ' := trivial A G ω) f hπ,
    cosetSum_of_mem_invariants (fun g ↦ by simp), ← Nat.cast_smul_eq_nsmul A, smul_smul,
    IsUnit.val_inv_mul, one_smul]

/-- **Duality commutes with invariants under a pro-`p` group** (blueprint
`lemma-duality-invariants-pro-p--1`, module level). Let `G` be a compact group in which the index of
every open normal subgroup is invertible in `A`, `ρ` a discrete representation of `G` on `E` and `ω`
an `A`-module with trivial action. Then restriction to the invariants is an isomorphism
`Hom_A(E, ω)^G ≃ Hom_A(E^G, ω)` for the contragredient action on `Hom_A(E, ω)`; its inverse is
precomposition with the averaging retraction `Representation.discreteAverage`. -/
noncomputable def invariantsDualEquiv
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) :
    (linHom ρ (trivial A G ω)).invariants ≃ₗ[A] (ρ.invariants →ₗ[A] ω) where
  toFun f := f.1 ∘ₗ ρ.invariants.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨φ ∘ₗ discreteAverage hA hρ, by
    rw [mem_linHom_trivial_invariants_iff]
    intro g v
    simp [discreteAverage_apply_apply]⟩
  left_inv f := by
    ext v
    exact map_discreteAverage_of_mem_invariants hA hρ f.2 v
  right_inv φ := by
    ext v
    exact congr_arg φ (Subtype.ext (discreteAverage_apply_of_mem_invariants hA hρ v.2))

/-- The pairing `E^G × Hom_A(E, ω)^G → ω` corresponding to
`Representation.invariantsDualEquiv` is
evaluation restricted to the invariants. -/
@[simp]
lemma invariantsDualEquiv_apply
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) (f : (linHom ρ (trivial A G ω)).invariants) (v : ρ.invariants) :
    invariantsDualEquiv hA hρ f v = (f : E →ₗ[A] ω) v :=
  rfl

@[simp]
lemma invariantsDualEquiv_symm_apply
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) (φ : ρ.invariants →ₗ[A] ω) (v : E) :
    ((invariantsDualEquiv hA hρ).symm φ : E →ₗ[A] ω) v = φ (discreteAverage hA hρ v) :=
  rfl

/-- An invariant functional is determined by the invariant pairing: `f v = ⟨avg v, f⟩`, where
`avg : E → E^G` is the averaging retraction. -/
lemma apply_eq_invariantsDualEquiv_discreteAverage
    (hA : ∀ U : OpenNormalSubgroup G, IsUnit ((U.toSubgroup.index : ℕ) : A))
    (hρ : ρ.IsDiscrete) (f : (linHom ρ (trivial A G ω)).invariants) (v : E) :
    (f : E →ₗ[A] ω) v = invariantsDualEquiv hA hρ f (discreteAverage hA hρ v) :=
  (map_discreteAverage_of_mem_invariants hA hρ f.2 v).symm

end Representation
