/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.MinimalAxioms
public import WeilConjectures.Mathlib.GroupTheory.Index
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionComp
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAut

/-!

# The group of generic automorphisms and its action on nearby cycles

The automorphisms `τ` of the geometric generic point `Spec Ω_K` of the trait `Spec K⟦t⟧` over
`Spec K⟦t⟧` and over the geometric generic point `Spec Ω` of `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.GenericAut`) form a group under composition: the kernel `P'` of the map of
inertia groups of the generic-slicing step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Facts about traits"). Its action on the
nearby cycles of a base change model (`NearbyCyclesModel.baseChangeAut`,
`NearbyCyclesModel.Hom.autAction`) is an anti-homomorphism
(`NearbyCyclesModel.autAction_baseChangeAut_mul`) sending `1` to the identity
(`NearbyCyclesModel.autAction_baseChangeAut_one`). Hence, if a subgroup `V` acts trivially, the sum
of the actions over representatives of `P' ⧸ U` for `U ≤ V` is `[V : U]` times the sum over
representatives of `P' ⧸ V` (`NearbyCyclesModel.sum_autAction_baseChangeAut_eq_relIndex_nsmul`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

namespace GenericAut

@[ext]
lemma ext {σ τ : GenericAut k' K} (h : σ.τ = τ.τ) : σ = τ := by
  cases σ
  cases τ
  subst h
  rfl

attribute [instance] GenericAut.isIso

/-- The composite `σ.τ ≫ τ.τ` of generic automorphisms. -/
noncomputable instance : Mul (GenericAut k' K) where
  mul σ τ :=
    { τ := σ.τ ≫ τ.τ
      isIso := inferInstance
      over_trait := by rw [Category.assoc, τ.over_trait, σ.over_trait]
      over_base := by rw [Category.assoc, τ.over_base, σ.over_base] }

/-- The identity generic automorphism. -/
noncomputable instance : One (GenericAut k' K) where
  one :=
    { τ := 𝟙 _
      isIso := inferInstance
      over_trait := Category.id_comp _
      over_base := Category.id_comp _ }

/-- The inverse of a generic automorphism. -/
noncomputable instance : Inv (GenericAut k' K) where
  inv σ :=
    { τ := inv σ.τ
      isIso := inferInstance
      over_trait := by rw [IsIso.inv_comp_eq, σ.over_trait]
      over_base := by rw [IsIso.inv_comp_eq, σ.over_base] }

@[simp]
lemma mul_τ (σ τ : GenericAut k' K) : (σ * τ).τ = σ.τ ≫ τ.τ := rfl

@[simp]
lemma one_τ : (1 : GenericAut k' K).τ = 𝟙 _ := rfl

@[simp]
lemma inv_τ (σ : GenericAut k' K) : σ⁻¹.τ = inv σ.τ := rfl

/-- The generic automorphisms form a group under composition. -/
noncomputable instance : Group (GenericAut k' K) :=
  Group.ofLeftAxioms (fun _ _ _ ↦ ext (by simp)) (fun _ ↦ ext (by simp))
    (fun _ ↦ ext (by simp))

end GenericAut

section Model

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)

lemma baseChangeAut_mul_generic (σ τ : GenericAut k' K) :
    (baseChangeAut hM b hb v hv (σ * τ)).generic =
      (baseChangeAut hM b hb v hv σ).generic ≫ (baseChangeAut hM b hb v hv τ).generic := by
  apply pullback.hom_ext <;> simp [baseChangeAut]

lemma baseChangeAut_one_generic :
    (baseChangeAut hM b hb v hv 1).generic = 𝟙 _ := by
  apply pullback.hom_ext <;> simp only [baseChangeAut, GenericAut.one_τ, Category.comp_id,
    Category.id_comp, limit.lift_π, PullbackCone.mk_π_app]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The action of generic automorphisms on the nearby cycles of a base change model is an
anti-homomorphism. -/
lemma autAction_baseChangeAut_mul (σ τ : GenericAut k' K)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (baseChangeAut hM b hb v hv (σ * τ)).autAction Λ C =
      (baseChangeAut hM b hb v hv τ).autAction Λ C ≫
        (baseChangeAut hM b hb v hv σ).autAction Λ C :=
  Hom.autAction_comp_of_eq Λ _ _ _ (Category.id_comp _)
    (baseChangeAut_mul_generic hM b hb v hv σ τ).symm C

/-- The identity generic automorphism acts trivially on nearby cycles. -/
lemma autAction_baseChangeAut_one
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (baseChangeAut hM b hb v hv 1).autAction Λ C = 𝟙 _ :=
  Hom.autAction_of_eq_id Λ _ rfl (baseChangeAut_one_generic hM b hb v hv) C

/-- **Sums of the actions over coset representatives**: if every element of a subgroup `V` of
the generic automorphisms acts trivially on `Ψ_{M''} C`, then for `U ≤ V` the sum of the actions
of representatives of `P' ⧸ U` is `[V : U]` times the sum over representatives of `P' ⧸ V`. -/
lemma sum_autAction_baseChangeAut_eq_relIndex_nsmul {U V : Subgroup (GenericAut k' K)}
    (hUV : U ≤ V) [Fintype (GenericAut k' K ⧸ U)] [Fintype (GenericAut k' K ⧸ V)]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction Λ C = 𝟙 _) :
    ∑ σ : GenericAut k' K ⧸ U, (baseChangeAut hM b hb v hv σ.out).autAction Λ C =
      U.relIndex V • ∑ σ : GenericAut k' K ⧸ V,
        (baseChangeAut hM b hb v hv σ.out).autAction Λ C :=
  Subgroup.sum_quotient_out_eq_relIndex_nsmul hUV
    (fun σ ↦ (baseChangeAut hM b hb v hv σ).autAction Λ C) fun σ τ hτ ↦ by
      simp only [autAction_baseChangeAut_mul, hV τ hτ, Category.id_comp]

end Model

/-- `Subgroup.card_nsmul_eq_sum_fin_of_le` for endomorphisms of `Ψ (L A)`, with the left-hand side
stated for `(L ⋙ Ψ) A`, the form in which averaged pullback exchanges occur. -/
lemma card_nsmul_eq_sum_fin_of_le_comp_obj {G : Type*} [Group G] {DX DS : Type*} [Category DX]
    [Category DS] [Preadditive DS] (L : DX ⥤ DX) (Ψ : DX ⥤ DS) (A : DX) {U V : Subgroup G}
    (hUV : U ≤ V) [Fintype (G ⧸ U)] [Fintype (G ⧸ V)]
    (act : G → (Ψ.obj (L.obj A) ⟶ Ψ.obj (L.obj A))) (hact : ∀ g, ∀ v ∈ V, act (g * v) = act g)
    (a : (L ⋙ Ψ).obj A ⟶ (L ⋙ Ψ).obj A)
    (ha : Fintype.card (G ⧸ V) • a = ∑ q : G ⧸ V, act q.out) :
    Fintype.card (G ⧸ U) • a =
      ∑ i : Fin (Fintype.card (G ⧸ U)), act ((Fintype.equivFin (G ⧸ U)).symm i).out :=
  Subgroup.card_nsmul_eq_sum_fin_of_le hUV act hact a ha

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
