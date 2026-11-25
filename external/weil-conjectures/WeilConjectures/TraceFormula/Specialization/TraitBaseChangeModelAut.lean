/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom

/-!

# Automorphisms of the geometric generic point acting on base change models

Let `M''` be the base change of a model `M` over `S = Spec k'⟦t⟧` to the trait `Spec K⟦t⟧`
(`NearbyCyclesModel.baseChange`), with geometric generic fibre over `Spec Ω_K`. An automorphism
`τ` of `Spec Ω_K` over `Spec K⟦t⟧` and over the geometric generic point `Spec Ω` of `S`
(`NearbyCyclesModel.GenericAut`; an element of the kernel `P` of the map of inertia groups) acts on
`M''` by a morphism of models over the identities (`NearbyCyclesModel.baseChangeAut`), which does
not change the projection `M'' ⟶ M` (`NearbyCyclesModel.baseChangeAut_generic_comp`) and commutes
with base changes of morphisms of models
(`NearbyCyclesModel.baseChangeAut_generic_comp_baseChange`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

/-- An automorphism of `Spec Ω_K` over `Spec K⟦t⟧` and over `Spec Ω`, where `Ω_K` and `Ω` are the
fields of the geometric generic points of the traits `Spec K⟦t⟧` and `Spec k'⟦t⟧`. -/
structure GenericAut (k' K : Type u) [Field k'] [Field K] [Algebra k' K] where
  /-- the automorphism of `Spec Ω_K`. -/
  τ : Spec (.of (traitGenericField K)) ⟶ Spec (.of (traitGenericField K))
  isIso : IsIso τ
  over_trait : τ ≫ traitGenericPoint K = traitGenericPoint K
  over_base : τ ≫ traitGenericPointMap k' K = traitGenericPointMap k' K

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

section Model

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K) (σ : GenericAut k' K)

/-- The action of a generic automorphism `τ` on the base change model `M''`: the morphism of
models over the identities which is the identity on the total space and `τ` on the geometric
generic fibre `𝒳'' ×_{K⟦t⟧} Spec Ω_K`. -/
noncomputable def baseChangeAut :
    (baseChange hM b hb v hv).Hom (baseChange hM b hb v hv) (𝟙 X) (𝟙 _) where
  total := 𝟙 _
  generic := pullback.map _ _ _ _ (𝟙 _) σ.τ (𝟙 _) (by simp) (by simp [σ.over_trait])
  comm_j := by simp
  comm_i := by simp
  comm_ε := by
    simp only [baseChange_ε, Category.comp_id]
    rw [← Category.assoc]
    congr 1
    refine hM.isPullback_j.hom_ext ?_ ?_
    · simp
    · simp [σ.over_base]

@[simp]
lemma baseChangeAut_total : (baseChangeAut hM b hb v hv σ).total = 𝟙 _ := rfl

/-- The action of a generic automorphism does not change the projection `M'' ⟶ M` on geometric
generic fibres. -/
lemma baseChangeAut_generic_comp :
    (baseChangeAut hM b hb v hv σ).generic ≫ (baseChangeHom hM b hb v hv).generic =
      (baseChangeHom hM b hb v hv).generic := by
  refine hM.isPullback_j.hom_ext ?_ ?_
  · simp [baseChangeAut]
  · simp [baseChangeAut, σ.over_base]

end Model

section Hom

variable {X Z : Scheme.{u}} {X' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {P : NearbyCyclesModel Z Z'.left} {f : Z ⟶ X} {f' : Z'.left ⟶ X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qP : P.total ⟶ trait k'} {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hP : P.IsTraitModelOver qP gP)
  {YM YP : Scheme.{u}} {bM : M.total ⟶ YM} {pM : YM ⟶ trait k'} (hbM : bM ≫ pM = qM)
  {vM : trait K ⟶ YM} (hvM : vM ≫ pM = traitMap k' K)
  {bP : P.total ⟶ YP} {pP : YP ⟶ trait k'} (hbP : bP ≫ pP = qP)
  {vP : trait K ⟶ YP} (hvP : vP ≫ pP = traitMap k' K)
  (φ : P.Hom M f f') (κ : YP ⟶ YM) (hκb : bP ≫ κ = φ.total ≫ bM) (hκv : vP ≫ κ = vM)
  (hgP : gP = φ.generic ≫ gM) (σ : GenericAut k' K)

/-- The action of a generic automorphism commutes with base changes of morphisms of models, on
geometric generic fibres. -/
lemma baseChangeAut_generic_comp_baseChange :
    (baseChangeAut hP bP hbP vP hvP σ).generic ≫
        (φ.baseChange hM hP hbM hvM hbP hvP κ hκb hκv hgP).generic =
      (φ.baseChange hM hP hbM hvM hbP hvP κ hκb hκv hgP).generic ≫
        (baseChangeAut hM bM hbM vM hvM σ).generic := by
  apply pullback.hom_ext <;> simp [baseChangeAut]

end Hom

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
