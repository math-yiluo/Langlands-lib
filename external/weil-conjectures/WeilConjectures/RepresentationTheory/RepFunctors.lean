/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RepresentationTheory.Intertwining
public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization

/-!
# Functors between categories of representations

* `Rep.uliftFunctor`: the universe lift `Rep.{w} k G ⥤ Rep.{max w w'} k G`, `V ↦ ULift V`;
* `Rep.tprodFunctor`: the tensor product `(V, W) ↦ V ⊗ W` of representations, as a bifunctor
  (the category `Rep.{w} k G` is only monoidal in Mathlib when `w` is the universe of `k`);
* `Representation.Equiv.tprodEquivLinHomOfDual_map`: the naturality of the identification
  `ρ ⊗ σ ≅ Hom(ρ', σ)` for `ρ' ≅ ρ^∨`.
-/

@[expose] public section

universe w w' v

open CategoryTheory

namespace Rep

variable (k : Type v) [CommRing k] (G : Type*) [Monoid G]

/-- The universe lift `V ↦ ULift V` of representations. -/
noncomputable def uliftFunctor : Rep.{w} k G ⥤ Rep.{max w w'} k G where
  obj X := Rep.of (X.ρ.transport (ULift.moduleEquiv (R := k) (M := X.V)).symm)
  map {X Y} f := Rep.ofHom
    ⟨(ULift.moduleEquiv (R := k) (M := Y.V)).symm.toLinearMap ∘ₗ f.hom.toLinearMap ∘ₗ
      (ULift.moduleEquiv (R := k) (M := X.V)).toLinearMap, fun g ↦ LinearMap.ext fun x ↦
        congrArg ULift.up (Rep.hom_comm_apply f g x.down)⟩
  map_id _ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl))
  map_comp _ _ :=
    Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl))

lemma uliftFunctor_map_hom_apply {X Y : Rep.{w} k G} (f : X ⟶ Y) (x : ULift.{w'} X.V) :
    ((uliftFunctor.{w, w'} k G).map f).hom x = ULift.up (f.hom x.down) :=
  rfl

/-- The tensor product of representations, as a bifunctor. -/
noncomputable def tprodFunctor :
    Rep.{max v w} k G × Rep.{max v w} k G ⥤ Rep.{max v w} k G where
  obj X := Rep.of (X.1.ρ.tprod X.2.ρ)
  map f := Rep.ofHom (f.1.hom.tensor f.2.hom)
  map_id _ := Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ ↦ rfl))
  map_comp _ _ :=
    Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ ↦ rfl))

lemma tprodFunctor_map_hom_tmul {X Y : Rep.{max v w} k G × Rep.{max v w} k G} (f : X ⟶ Y)
    (x : X.1.V) (y : X.2.V) :
    ((tprodFunctor.{w} k G).map f).hom (x ⊗ₜ y) = f.1.hom x ⊗ₜ f.2.hom y :=
  rfl

end Rep

namespace Representation

variable {k G V V' W W₂ V₂ V₂' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W] [Module k W] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₂'] [Module k V₂'] [AddCommGroup W₂] [Module k W₂]
  {ρ : Representation k G V} {ρ' : Representation k G V'} {σ : Representation k G W}
  {ρ₂ : Representation k G V₂} {ρ₂' : Representation k G V₂'} {σ₂ : Representation k G W₂}

/-- The identification `ρ ⊗ σ ≅ Hom(ρ', σ)` sends `v ⊗ w` to `d ↦ b(d)(v) • w`. -/
lemma Equiv.tprodEquivLinHomOfDual_tmul [FiniteDimensional k V] (b : ρ'.Equiv ρ.dual) (v : V)
    (w : W) (d : V') :
    Equiv.tprodEquivLinHomOfDual (σ := σ) b (v ⊗ₜ w) d = b d v • w :=
  rfl

/-- **Naturality of `ρ ⊗ σ ≅ Hom(ρ', σ)`**: for linear maps `α : V → V₂`, `β : W → W₂` and
`γ : V₂' → V'` such that `γ` is dual to `α` under `ρ' ≅ ρ^∨` and `ρ₂' ≅ ρ₂^∨`, the identification
sends `(α ⊗ β) x` to `β ∘ x ∘ γ`. -/
lemma Equiv.tprodEquivLinHomOfDual_map [FiniteDimensional k V] [FiniteDimensional k V₂]
    (b : ρ'.Equiv ρ.dual) (b₂ : ρ₂'.Equiv ρ₂.dual) (α : V →ₗ[k] V₂) (β : W →ₗ[k] W₂)
    (γ : V₂' →ₗ[k] V') (h : ∀ d v, b (γ d) v = b₂ d (α v)) (x : TensorProduct k V W) :
    Equiv.tprodEquivLinHomOfDual (σ := σ₂) b₂ (TensorProduct.map α β x) =
      β ∘ₗ Equiv.tprodEquivLinHomOfDual (σ := σ) b x ∘ₗ γ := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    ext d
    simp only [TensorProduct.map_tmul, LinearMap.comp_apply, tprodEquivLinHomOfDual_tmul, h,
      map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp, LinearMap.comp_add]

end Representation
