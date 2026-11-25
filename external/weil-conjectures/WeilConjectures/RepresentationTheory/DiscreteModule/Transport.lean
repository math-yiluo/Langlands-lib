/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Transport of continuous cohomology along isomorphisms of topological groups

An isomorphism of topological groups `e : G ≃ₜ* G'` induces an equivalence of categories
`DiscreteModule G' ≌ DiscreteModule G` by restriction, and hence isomorphisms of cohomology
groups `Hⁿ(G, A) ≃ Hⁿ(G', A)` for trivial modules `A`.

## Main definitions and statements

- `DiscreteModule.resEquivalence`: the equivalence of categories given by restriction.
- `DiscreteModule.HTrivialAddEquiv`: the isomorphism `Hⁿ(G, A) ≃+ Hⁿ(G', A)`.
- `DiscreteModule.subsingleton_H_trivialZMod_of_continuousMulEquiv`: vanishing of `Hⁿ(-, 𝔽_ℓ)`
  is invariant under isomorphisms of topological groups.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Action

/-- The underlying monoid homomorphism of a continuous multiplicative equivalence is
continuous. -/
lemma ContinuousMulEquiv.continuous_toMonoidHom {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') : Continuous e.toMulEquiv.toMonoidHom :=
  e.continuous

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- Restriction of a trivial module is the trivial module. -/
def resTrivialIso (φ : G →* G') (hφ : Continuous φ) (A : AddCommGrpCat.{max u w}) :
    (res.{w} φ hφ).obj (trivial G' A) ≅ trivial G A :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun _ ↦ rfl)

/-- Restriction along `φ` and then along `ψ` is the identity if `φ ∘ ψ = id`. -/
def resCompResIso (φ : G →* G') (hφ : Continuous φ) (ψ : G' →* G) (hψ : Continuous ψ)
    (h : ∀ g, φ (ψ g) = g) : res.{w} φ hφ ⋙ res ψ hψ ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun g ↦ by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact congrArg (fun g ↦ (M.obj.ρ g).asHom) (h g)))
    fun _ ↦ rfl

/-- An isomorphism of topological groups `e : G ≃ₜ* G'` induces an equivalence of categories
of discrete modules, by restriction along `e.symm` and `e`. -/
def resEquivalence (e : G ≃ₜ* G') : DiscreteModule.{w} G ≌ DiscreteModule.{w} G' :=
  CategoryTheory.Equivalence.mk (res e.symm.toMulEquiv.toMonoidHom e.symm.continuous_toMonoidHom)
    (res e.toMulEquiv.toMonoidHom e.continuous_toMonoidHom)
    (resCompResIso _ _ _ _ fun g ↦ e.symm_apply_apply g).symm
    (resCompResIso _ _ _ _ fun g ↦ e.apply_symm_apply g)

/-- The adjunction `res e.symm ⊣ res e` of the equivalence `DiscreteModule.resEquivalence`. -/
def resAdjunction (e : G ≃ₜ* G') :
    res.{w} e.symm.toMulEquiv.toMonoidHom e.symm.continuous_toMonoidHom ⊣
      res.{w} e.toMulEquiv.toMonoidHom e.continuous_toMonoidHom :=
  (resEquivalence.{w} e).toAdjunction

/-- **Invariance of cohomology of trivial modules.** An isomorphism of topological groups
`e : G ≃ₜ* G'` induces isomorphisms `Hⁿ(G, A) ≃+ Hⁿ(G', A)` for every abelian group `A` with
the trivial actions. -/
noncomputable def HTrivialAddEquiv (e : G ≃ₜ* G') (A : AddCommGrpCat.{max u w}) (n : ℕ) :
    H G (trivial G A) n ≃+ H G' (trivial G' A) n :=
  (Abelian.Ext.postcompAddEquiv _ (resTrivialIso _ _ A) n).symm.trans <|
    ((resAdjunction.{w} e).extAddEquiv (intTrivial G) (trivial G' A) n).trans <|
    Abelian.Ext.precompAddEquiv (resTrivialIso _ _ _).symm _ n

/-- Vanishing of `Hⁿ(-, 𝔽_ℓ)` is invariant under isomorphisms of topological groups. -/
lemma subsingleton_H_trivialZMod_of_continuousMulEquiv (e : G ≃ₜ* G') (ℓ : ℕ) [Fact ℓ.Prime]
    (n : ℕ) [Subsingleton (H G' (trivialZMod.{w} G' ℓ) n)] :
    Subsingleton (H G (trivialZMod.{w} G ℓ) n) :=
  (HTrivialAddEquiv.{w} e _ n).injective.subsingleton

end DiscreteModule
