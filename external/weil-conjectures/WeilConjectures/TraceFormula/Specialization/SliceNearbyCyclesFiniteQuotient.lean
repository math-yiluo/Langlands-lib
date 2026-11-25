/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericAutModEll
public import WeilConjectures.TraceFormula.Specialization.GenericAutPow
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessInertia
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Separated

/-!

# Reductions of the finiteness of the action of `P'` on slice nearby cycles

Formal reductions of the two halves of
`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom` (SGA 4½, [Th. finitude],
§3.7) to their geometric inputs.

* **(A) with finite coefficients**
  (`NearbyCyclesModel.exists_normal_finiteIndex_autAction_baseChangeAut_eq_id`):
  if `Ψ_{M''} A` is bounded constructible over a scheme of finite type over a separably
  closed field, a normal subgroup of finite index of `P'` acts trivially on it.
* **(A) integrally** (`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_derivedComplete`):
  if `Ψ_{M''} A` is derived complete with `𝒪_E`-coefficients, a normal subgroup of finite
  index of `P'` acting trivially on `Ψ_{M''}` of the reduction of `A` modulo `ℓ` acts
  trivially on `Ψ_{M''} A`, by the divisibility of `P'` and the `ℓ`-adic separatedness of
  derived complete complexes (`ProEtale.eq_zero_of_forall_exists_eq_pow_zsmul`).
* **(B2)** (`CategoryTheory.exists_retraction_comp_eq_of_eq_comp`): a morphism `α = u ≫ β`, with
  `u` an isomorphism and `β` split by `t` with `c • (t ≫ β) = e`, has a retraction `s` with
  `e ≫ s ≫ α = e`; this applies to `α_θ` once it is identified with the exchange of a finite
  Galois layer, split by the Galois average
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom'`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **(B2) from a Galois-layer factorisation**: if `α = u ≫ β` with `u` an isomorphism and
`β ≫ t = 𝟙` with `c • (t ≫ β) = e`, then `s = t ≫ u⁻¹` is a retraction of `α` with
`e ≫ s ≫ α = e`. -/
theorem exists_retraction_comp_eq_of_eq_comp {Z W Y : C} (α : Z ⟶ Y) (u : Z ≅ W) (β : W ⟶ Y)
    (hα : α = u.hom ≫ β) (t : Y ⟶ W) (ht : β ≫ t = 𝟙 W) (c : ℕ) (e : Y ⟶ Y)
    (he : c • (t ≫ β) = e) : ∃ s : Y ⟶ Z, α ≫ s = 𝟙 Z ∧ e ≫ s ≫ α = e := by
  refine ⟨t ≫ u.inv, by simp [hα, reassoc_of% ht], ?_⟩
  rw [hα, Category.assoc, Iso.inv_hom_id_assoc, ← he, Preadditive.nsmul_comp, Category.assoc,
    reassoc_of% ht]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)

/-- **(A) with finite coefficients**: if `Ψ_{M''} A` is bounded constructible over a
scheme of finite type over a separably closed field, a normal subgroup of finite index of the
generic automorphisms acts trivially on it. -/
theorem exists_normal_finiteIndex_autAction_baseChangeAut_eq_id
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
    [Finite T] {k : Type u} [Field k] [IsSepClosed k]
    [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k))]
    (s : (baseChangeSpecial b v).left ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    [IsSeparated s]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hA : boundedConstructible _ (((baseChange hM b hb v hv).nearbyCycles
      (Profinite.continuousMapRingObj T)).obj A)) :
    ∃ V : Subgroup (GenericAut k' K), V.Normal ∧ V.FiniteIndex ∧ ∀ σ ∈ V,
      (baseChangeAut hM b hb v hv σ).autAction (Profinite.continuousMapRingObj T) A = 𝟙 _ := by
  have := finite_hom_of_boundedConstructible_of_finite T s hA hA
  obtain ⟨V, hV, hVt⟩ := CategoryTheory.exists_finiteIndex_eq_id_of_finite_end _
    (fun σ ↦ (baseChangeAut hM b hb v hv σ).autAction (Profinite.continuousMapRingObj T) A)
    (autAction_baseChangeAut_one hM b hb v hv _ A)
    (fun σ τ ↦ autAction_baseChangeAut_mul hM b hb v hv _ σ τ A)
  exact ⟨V.normalCore, inferInstance, inferInstance,
    fun σ hσ ↦ hVt σ (V.normalCore_le hσ)⟩

/-- **(A) integrally**: for `K` algebraically closed and `ℓ` invertible in `k'`, if `Ψ_{M''} A`
is derived complete with `𝒪_E`-coefficients and the groups `Hom(Ψ A⟦1⟧, Res_n (red_n Ψ A))` are
finite, a normal subgroup of finite index of `P'` acting trivially on `Ψ_{M''}` of the
reduction `A --ℓ--> A ⟶ Z` modulo `ℓ` acts trivially on `Ψ_{M''} A`. -/
theorem autAction_baseChangeAut_eq_id_of_derivedComplete [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : (ℓ : k') ≠ 0) {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]
    {A Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (π : A ⟶ Z)
    (δ : Z ⟶ A⟦(1 : ℤ)⟧) (hT : Triangle.mk (ℓ • 𝟙 A) π δ ∈ distTriang _)
    (hc : derivedCompleteIntegers ℓ E _
      (((baseChange hM b hb v hv).nearbyCycles (Profinite.padicIntegersRingObj ℓ E)).obj A))
    [∀ n : ℕ, Finite ((shiftFunctor _ (1 : ℤ)).obj (((baseChange hM b hb v hv).nearbyCycles
        (Profinite.padicIntegersRingObj ℓ E)).obj A) ⟶
      (Mod.comap (integersModPowReduction (baseChangeSpecial b v).left ℓ E
          (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction (baseChangeSpecial b v).left ℓ E
          (n + 1))).leftDerivedFunctor.obj
          (((baseChange hM b hb v hv).nearbyCycles (Profinite.padicIntegersRingObj ℓ E)).obj A)))]
    (V : Subgroup (GenericAut k' K)) [V.Normal] [V.FiniteIndex]
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction
      (Profinite.padicIntegersRingObj ℓ E) Z = 𝟙 _) {σ : GenericAut k' K} (hσ : σ ∈ V) :
    (baseChangeAut hM b hb v hv σ).autAction (Profinite.padicIntegersRingObj ℓ E) A = 𝟙 _ :=
  autAction_baseChangeAut_eq_id_of_distinguished_of_separated hM b hb v hv _ π δ hT
    (fun f hf ↦ by
      apply End.ext
      apply ProEtale.eq_zero_of_forall_exists_eq_pow_zsmul hc
      intro m
      obtain ⟨g, hg⟩ := hf m
      refine ⟨g.asHom, ?_⟩
      rw [← Nat.cast_pow, natCast_zsmul]
      exact congrArg End.asHom hg)
    (GenericAut.exists_pow_ell_pow_eq hℓ) V hV hσ

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
