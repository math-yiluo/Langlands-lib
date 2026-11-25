/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessInertia
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup

/-!

# The generic automorphisms act through a finite quotient, finite coefficients

Let `M` be a model of finite type over the trait `S = Spec k'⟦t⟧` whose identification factors
through the total space, `M''` its base change along `Spec K⟦t⟧ ⟶ Y` for `K` separably closed
(`NearbyCyclesModel.baseChange`), and `P'` the group of generic automorphisms
(`NearbyCyclesModel.GenericAut`), acting on the nearby cycles of `M''`
(`NearbyCyclesModel.baseChangeAut`). With finite coefficients `T̲`, a subgroup of finite index of
`P'` acts trivially on `Ψ_{M''} C` for every bounded constructible `C`
(`NearbyCyclesModel.exists_finiteIndex_autAction_baseChangeAut_eq_id_of_finite`).

Indeed `M''` is a model of finite type over `Spec K⟦t⟧`
(`NearbyCyclesModel.IsTraitModelOver.baseChange`), so `Ψ_{M''} C` is bounded constructible by
Deligne's finiteness theorem with finite coefficients
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel_of_finite`). Its endomorphisms
then form a finite set (`ProEtale.CondensedRing.finite_hom_of_boundedConstructible_of_finite`), and
the kernel of the action has finite index (`CategoryTheory.exists_finiteIndex_eq_id_of_finite_end`).

This is the finite-coefficient case of the finiteness of the action of `P'` in the
generic-slicing identification (blueprint `proposition-external-kunneth-formula-nearby-cycles`,
"Facts about traits", identification (2); SGA 4½, [Th. finitude], §3.7).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsSepClosed K]
  [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of K))] {p : ℕ} [Fact p.Prime]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {s : Y ⟶ trait k'}
  [IsSeparated s] (hb : b ≫ s = q) (v : trait K ⟶ Y) (hv : v ≫ s = traitMap k' K)

/-- **The generic automorphisms act on the nearby cycles of the base change through a finite
quotient, finite coefficients**: for a model `M` of finite type over the trait whose
identification factors as `ε = j ≫ e` through the total space, a bounded constructible complex
`C` of `T̲`-modules and the base change `M''` of `M` along `Spec K⟦t⟧ ⟶ Y`, a subgroup of
finite index of the generic automorphisms acts trivially on `Ψ_{M''} C`. -/
theorem exists_finiteIndex_autAction_baseChangeAut_eq_id_of_finite
    (hp : ∀ m : ℕ, (m : K) = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hC : boundedConstructible _ C) :
    ∃ V : Subgroup (GenericAut k' K), V.FiniteIndex ∧ ∀ σ ∈ V,
      (baseChangeAut hM b hb v hv σ).autAction (Profinite.continuousMapRingObj T) C = 𝟙 _ := by
  have hT := IsTraitModelOver.baseChange hM b hb v hv
  have hM'' := hT.isTraitModel
  have := hT.locallyOfFiniteType
  have := hT.quasiCompact
  have := hT.isSeparated
  have hi := hT.isPullback_i
  obtain ⟨e, he⟩ := hε
  have hΨ := preservesBoundedConstructible_of_isTraitModel_of_finite T hp hpT _ hM''
    ⟨pullback.fst _ _ ≫ e, by
      rw [baseChange_ε, ← he, baseChange_j, baseChangeGenericMap_j_assoc]⟩ C hC
  have : LocallyOfFiniteType (baseChangeSpecial b v).hom :=
    MorphismProperty.of_isPullback hi ‹_›
  have : QuasiCompact (baseChangeSpecial b v).hom := MorphismProperty.of_isPullback hi ‹_›
  have : IsSeparated (baseChangeSpecial b v).hom := MorphismProperty.of_isPullback hi ‹_›
  have := finite_hom_of_boundedConstructible_of_finite T (baseChangeSpecial b v).hom hΨ hΨ
  exact exists_finiteIndex_eq_id_of_finite_end _ _
    (autAction_baseChangeAut_one hM b hb v hv _ C)
    (fun σ τ ↦ autAction_baseChangeAut_mul hM b hb v hv _ σ τ C)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
