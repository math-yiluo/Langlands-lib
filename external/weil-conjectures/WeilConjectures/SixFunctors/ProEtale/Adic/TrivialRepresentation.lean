/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Trivial lisse sheaves on a connected scheme

On a connected scheme `V` a locally finite continuous function `V → ℚ̄_ℓ` is constant, `ℚ̄_ℓ`
being totally disconnected (`PadicAlgCl.locallyFiniteFunctionsEquiv`). Hence a morphism
`ℚ̄_ℓ,V^ι ⟶ ℚ̄_ℓ,V^κ` of trivial lisse sheaves is a `κ × ι` matrix over `ℚ̄_ℓ`, compatibly with
composition (`AlgebraicGeometry.ProEtale.AdicSheaf.freeHomEquiv`): this is the full faithfulness,
on trivial representations, of the correspondence between lisse sheaves and continuous
`π₁`-representations (Bhatt–Scholze, §7).
-/

@[expose] public section

universe u

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

/-- A locally finite function on a preconnected space is constant. -/
lemma locallyFiniteFunctions_apply_eq [PreconnectedSpace T] (f : locallyFiniteFunctions l T)
    (x y : T) : f.1 x = f.1 y :=
  (isPreconnected_univ.image f.1 f.1.continuous.continuousOn).subsingleton
    ⟨x, trivial, rfl⟩ ⟨y, trivial, rfl⟩

lemma locallyFiniteFunctions_eq_algebraMap [PreconnectedSpace T] (f : locallyFiniteFunctions l T)
    (x : T) : f = algebraMap (PadicAlgCl l) (locallyFiniteFunctions l T) (f.1 x) :=
  Subtype.ext (ContinuousMap.ext fun y ↦ locallyFiniteFunctions_apply_eq f y x)

variable (l T) in
/-- On a connected space the locally finite functions are the constants. -/
noncomputable def locallyFiniteFunctionsEquiv [ConnectedSpace T] :
    locallyFiniteFunctions l T ≃ₐ[PadicAlgCl l] PadicAlgCl l :=
  (AlgEquiv.ofBijective (Algebra.ofId (PadicAlgCl l) (locallyFiniteFunctions l T))
    ⟨fun a b h ↦ by
      have x : T := Classical.arbitrary T
      simpa using congrArg (fun f : locallyFiniteFunctions l T ↦ f.1 x) h,
    fun f ↦ ⟨f.1 (Classical.arbitrary T),
      (locallyFiniteFunctions_eq_algebraMap f _).symm⟩⟩).symm

end PadicAlgCl

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {l : ℕ} [Fact l.Prime] {V : Scheme.{u}} [ConnectedSpace V]
  {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

/-- On a connected scheme, morphisms between trivial lisse sheaves `ℚ̄_ℓ,V^ι ⟶ ℚ̄_ℓ,V^κ` are the
`κ × ι` matrices over `ℚ̄_ℓ`. -/
noncomputable def freeHomEquiv :
    ((⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V) ≃ Matrix κ ι (PadicAlgCl l) where
  toFun ψ := (unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEquiv l V)
  invFun N := ofUnitMatrix (N.map (PadicAlgCl.locallyFiniteFunctionsEquiv l V).symm)
  left_inv ψ := by
    simp only [Matrix.map_map]
    convert ofUnitMatrix_unitMatrix ψ
    ext i j : 1
    simp
  right_inv N := by
    simp only [unitMatrix_ofUnitMatrix, Matrix.map_map]
    ext i j : 1
    simp

lemma freeHomEquiv_comp (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V)
    (ψ' : (⨁ fun _ : κ ↦ unit l V) ⟶ ⨁ fun _ : ν ↦ unit l V) :
    freeHomEquiv (ψ ≫ ψ') = freeHomEquiv ψ' * freeHomEquiv ψ := by
  simp only [freeHomEquiv, Equiv.coe_fn_mk, unitMatrix_comp]
  exact Matrix.map_mul (f := (PadicAlgCl.locallyFiniteFunctionsEquiv l V).toRingHom)

lemma freeHomEquiv_id [DecidableEq ι] :
    freeHomEquiv (𝟙 (⨁ fun _ : ι ↦ unit l V)) = 1 := by
  simp only [freeHomEquiv, Equiv.coe_fn_mk, unitMatrix_id]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end AlgebraicGeometry.ProEtale.AdicSheaf
