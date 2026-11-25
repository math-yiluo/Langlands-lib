/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.CategoryTheory.Preadditive.ActionTrivialModEll
public import WeilConjectures.Mathlib.Topology.Algebra.Group.PowSurjective

/-!

# Generic automorphisms acting trivially modulo `ℓ`

Let `M''` be a base change model of a trait model `M` and `P'` the group of generic automorphisms
(`NearbyCyclesModel.GenericAut`) acting on `Ψ_{M''}` (`NearbyCyclesModel.baseChangeAut`). Let
`A ⟶ Z` be the reduction of a complex `A` modulo `ℓ`, the cone of `ℓ • 𝟙 A`, and suppose every
element of `P'` is an `ℓ ^ m`-th power for every `m` (`P'` is pro-`p`, `p ≠ ℓ`,
`NearbyCyclesModel.GenericAut.exists_pow_ell_pow_eq`). Then a normal subgroup `V` of finite index
of `P'` acting trivially on `Ψ_{M''} Z` acts trivially on `Ψ_{M''} A`, provided no nonzero
endomorphism of `Ψ_{M''} A` is divisible by every power of `ℓ`, e.g. with `𝒪_E`-coefficients
(`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished_of_separated`). This holds
in particular for `A` killed by `ℓ ^ m`, e.g. with `𝒪_E / ℓ ^ m`-coefficients
(`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished`).

This is the step of the finiteness of the action of `P'` on `ℚ̄_ℓ`-nearby cycles (SGA 4½,
[Th. finitude], §3.7) which makes the subgroup `V`, obtained from the finiteness of the
endomorphisms of `Ψ_{M''} Z`
(`NearbyCyclesModel.exists_finiteIndex_autAction_eq_id_of_finite`), independent of the level
`m`.

-/


@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The action of the generic automorphisms on `Ψ_{M''} A`, as a homomorphism to the
endomorphism monoid. -/
noncomputable def baseChangeAutActionHom
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    GenericAut k' K →* End (((baseChange hM b hb v hv).nearbyCycles Λ).obj A) where
  toFun σ := .of ((baseChangeAut hM b hb v hv σ).autAction Λ A)
  map_one' := End.ext (autAction_baseChangeAut_one hM b hb v hv Λ A)
  map_mul' σ τ := by
    apply End.ext
    rw [End.mul_asHom]
    dsimp only
    exact autAction_baseChangeAut_mul hM b hb v hv Λ σ τ A

@[simp]
lemma baseChangeAutActionHom_apply
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (σ : GenericAut k' K) :
    (baseChangeAutActionHom hM b hb v hv Λ A σ).asHom =
      (baseChangeAut hM b hb v hv σ).autAction Λ A :=
  rfl

/-- **Generic automorphisms trivial modulo `ℓ` are trivial, integral case**: let `A` be such that
no nonzero endomorphism of `Ψ_{M''} A` is divisible by every power of `ℓ` (e.g. with
`𝒪_E`-coefficients), and suppose every generic automorphism is an `ℓ ^ m`-th power for every `m`.
Let `V` be a normal subgroup of finite index acting trivially on `Ψ_{M''} Z`, for a distinguished
triangle
```
      ℓ        π        δ
  A ────▶ A ────▶ Z ────▶ A⟦1⟧
```
By naturality of the action, every `σ ∈ V` makes the square
```
             σ
  Ψ A ─────────▶ Ψ A
   │              │
   │ Ψ π          │ Ψ π
   ▼              ▼
  Ψ Z ─────────▶ Ψ Z
         σ = id
```
commute, so `σ` acts trivially on `Ψ_{M''} A` (`End.eq_one_of_distinguished_of_separated`). -/
theorem autAction_baseChangeAut_eq_id_of_distinguished_of_separated {ℓ : ℕ}
    {A Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (π : A ⟶ Z) (δ : Z ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ℓ • 𝟙 A) π δ ∈ distTriang _)
    (hsep : ∀ f : End (((baseChange hM b hb v hv).nearbyCycles Λ).obj A),
      (∀ m : ℕ, ∃ g : End (((baseChange hM b hb v hv).nearbyCycles Λ).obj A),
        f = (ℓ ^ m) • g) → f = 0)
    (hdiv : ∀ (m : ℕ) (σ : GenericAut k' K), ∃ τ, τ ^ ℓ ^ m = σ) (V : Subgroup (GenericAut k' K))
    [V.Normal] [V.FiniteIndex]
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction Λ Z = 𝟙 _) {σ : GenericAut k' K}
    (hσ : σ ∈ V) : (baseChangeAut hM b hb v hv σ).autAction Λ A = 𝟙 _ := by
  let Ψ := (baseChange hM b hb v hv).nearbyCycles Λ
  have hdivV : ∀ (m : ℕ) (τ : V), ∃ τ' : V, τ' ^ ℓ ^ m = τ := fun m τ ↦ by
    obtain ⟨τ', hτ', h⟩ := V.exists_mem_pow_eq_of_forall_exists_pow (hdiv m) τ.2
    exact ⟨⟨τ', hτ'⟩, Subtype.ext (by rwa [Subgroup.coe_pow])⟩
  have hT' : Triangle.mk (Ψ.map (ℓ • 𝟙 A)) (Ψ.map π) _ ∈ distTriang _ := Ψ.map_distinguished _ hT
  have key := End.eq_one_of_distinguished_of_separated (Ψ.map π) _ hT'
    (by simp) hsep
    ((baseChangeAutActionHom hM b hb v hv Λ A).comp V.subtype)
    (fun τ ↦ by
      dsimp only [MonoidHom.comp, baseChangeAutActionHom, MonoidHom.coe_mk, OneHom.coe_mk, Ψ]
      rw [Hom.autAction_naturality, Subgroup.coe_subtype, hV _ τ.2, Category.comp_id]) hdivV ⟨σ, hσ⟩
  have key' := congrArg End.asHom key
  dsimp only [MonoidHom.comp, baseChangeAutActionHom, End.one_asHom, Ψ] at key'
  exact key'

/-- **Generic automorphisms trivial modulo `ℓ` are trivial, torsion case**: the same as
`autAction_baseChangeAut_eq_id_of_distinguished_of_separated` for `A` killed by `ℓ ^ m`, for
which no nonzero endomorphism of `Ψ_{M''} A` is divisible by `ℓ ^ m`. -/
theorem autAction_baseChangeAut_eq_id_of_distinguished {ℓ m : ℕ}
    {A Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (π : A ⟶ Z) (δ : Z ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ℓ • 𝟙 A) π δ ∈ distTriang _) (hℓ : (ℓ ^ m) • 𝟙 A = 0)
    (hdiv : ∀ (m : ℕ) (σ : GenericAut k' K), ∃ τ, τ ^ ℓ ^ m = σ) (V : Subgroup (GenericAut k' K))
    [V.Normal] [V.FiniteIndex]
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction Λ Z = 𝟙 _) {σ : GenericAut k' K}
    (hσ : σ ∈ V) : (baseChangeAut hM b hb v hv σ).autAction Λ A = 𝟙 _ := by
  let Ψ := (baseChange hM b hb v hv).nearbyCycles Λ
  have hℓ' : (ℓ ^ m) • 𝟙 (Ψ.obj A) = 0 := by
    rw [← Ψ.map_id, ← Functor.map_nsmul, hℓ, Functor.map_zero]
  refine autAction_baseChangeAut_eq_id_of_distinguished_of_separated hM b hb v hv Λ π δ hT
    (fun f hf ↦ ?_) hdiv V hV hσ
  obtain ⟨g, rfl⟩ := hf m
  apply End.ext
  change (ℓ ^ m) • g.asHom = 0
  rw [← Category.id_comp g.asHom, ← Preadditive.nsmul_comp, hℓ', zero_comp]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
