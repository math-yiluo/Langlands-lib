/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Correspondence

/-!
# Frobenius correspondences and their operators

Let `Φ : X ⟶ X` be an endomorphism of a separated `k`-scheme of finite type and
`ψ : LΦ^* K ⟶ K` a *Frobenius correspondence*, an arbitrary morphism. Its iterates
`ψ_m : LΦ_m^* K ⟶ K` (`ProEtale.CondensedRing.frobeniusCoefficientIterate`) are defined by the
recursion `ψ_{m+1} = ψ ∘ LΦ^* ψ_m`. We prove the general cocycle identity
`ψ_{m+n} = ψ_n ∘ LΦ_n^* ψ_m` and, as its special case, the recursion
`ψ_{m+1} = ψ_m ∘ LΦ_m^* ψ` of the blueprint, so that
`ψ_m = ψ ∘ LΦ^* ψ ∘ ⋯ ∘ L(Φ^{m-1})^* ψ` (blueprint
`definition-frobenius-correspondences-their-operators`).

For the model Frobenius of a model `X₀` over a finite field, `Φ` is finite, hence proper, so the
graph correspondence `c_m = (𝟙, Φ_m)` with coefficient map `ψ_m`
(`ProEtale.CondensedRing.Correspondence.frobeniusGraph`) has global operator
`T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ Φ_m^♯`
(`ProEtale.CondensedRing.Correspondence.globalOperator_frobeniusGraph`).

In this library a Weil structure of `K` is an isomorphism `φ : LΦ^* K ≅ K` for the scheme
Frobenius `Φ` itself, so that the comparison `κ_m` of blueprint
`lemma-scheme-frobenius-geometric-frobenius` is the identity, `ψ_m = φ_m`
(`ProEtale.CondensedRing.WeilBoundedConstructible.iterateStr_hom_eq_frobeniusCoefficientIterate`),
and we prove `T_{c_m}(φ_m) = Frob^m`.

## Main statements

- `ProEtale.CondensedRing.frobeniusCoefficientIterate_add`: `ψ_{m+n} = ψ_n ∘ LΦ_n^* ψ_m`.
- `ProEtale.CondensedRing.frobeniusCoefficientIterate_succ'`: `ψ_{m+1} = ψ_m ∘ LΦ_m^* ψ`.
- `ProEtale.CondensedRing.IsModelFrobenius.isProper`: the model Frobenius is proper.
- `ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_graph_eq_pow`:
  `T_{c_m}(φ_m) = Frob^m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

section Iterate

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {K : Dᵇc(X.left)⟦Λ⟧}

variable {ℓ} in
/-- Blueprint `definition-frobenius-correspondences-their-operators`: the iterates of a Frobenius
correspondence `ψ : LΦ^* K ⟶ K` satisfy the cocycle identity
```
ψ_{m+n} : LΦ_{m+n}^* K = L(Φ_n ≫ Φ_m)^* K ≅ LΦ_n^* LΦ_m^* K --LΦ_n^* ψ_m--> LΦ_n^* K
  --ψ_n--> K.
```
-/
theorem frobeniusCoefficientIterate_add (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K)
    (m n : ℕ) :
    frobeniusCoefficientIterate ψ (m + n) =
      eqToHom (by rw [frobeniusIterate_add]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ
          (frobeniusIterate Φ n) (frobeniusIterate Φ m)).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ n)).map
          (frobeniusCoefficientIterate ψ m) ≫
        frobeniusCoefficientIterate ψ n := by
  induction n with
  | zero =>
    exact (boundedConstructibleUpperStarComp_id_aux _ ℓ (frobeniusIterate_zero Φ)
      (frobeniusIterate_add Φ m 0) (frobeniusCoefficientIterate ψ m)).symm
  | succ n ih =>
    exact boundedConstructibleUpperStarComp_cocycle_aux Λ ℓ
      (frobeniusIterate_succ Φ (m + n)) (frobeniusIterate_add Φ m n)
      (frobeniusIterate_add Φ m (n + 1)) (frobeniusIterate_succ Φ n)
      (frobeniusCoefficientIterate ψ m) (frobeniusCoefficientIterate ψ n) ψ
      (frobeniusCoefficientIterate ψ (m + n)) ih

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The iterates `Φ_{m+1} = Φ_m ≫ Φ` of an endomorphism. -/
lemma frobeniusIterate_succ' (Φ : X ⟶ X) (m : ℕ) :
    frobeniusIterate Φ (m + 1) = frobeniusIterate Φ m ≫ Φ :=
  (frobeniusIterate_succ Φ m).trans (comp_frobeniusIterate_comm Φ m)

/-- `frobeniusCoefficientIterate_add` for `ψ_{1+m}`, with the index generalized. -/
private lemma frobeniusCoefficientIterate_eq_of_eq_one_add
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) {N m : ℕ} (hN : N = 1 + m)
    (e : frobeniusIterate Φ N = frobeniusIterate Φ m ≫ frobeniusIterate Φ 1) :
    frobeniusCoefficientIterate ψ N =
      eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ
          (frobeniusIterate Φ m) (frobeniusIterate Φ 1)).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ m)).map
          (frobeniusCoefficientIterate ψ 1) ≫
        frobeniusCoefficientIterate ψ m := by
  subst hN
  exact frobeniusCoefficientIterate_add ψ 1 m

/-- The recursion `ψ_{m+1} = ψ_m ∘ LP^* ψ` for an endomorphism `P = Φ`, in a form with `P`
generalized so that the equation `P = Φ` can be substituted. -/
private lemma frobeniusCoefficientIterate_succ'_aux {P F G : X ⟶ X} (hP : P = Φ)
    (e : G = F ≫ P) (e' : G = F ≫ Φ)
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K)
    (ψP : (boundedConstructibleUpperStar Λ ℓ P).obj K ⟶ K) (hψP : ψP = eqToHom (by rw [hP]) ≫ ψ)
    (χ : (boundedConstructibleUpperStar Λ ℓ F).obj K ⟶ K) :
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ G).obj K = _ by rw [e]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ F P).hom.app K ≫
      (boundedConstructibleUpperStar Λ ℓ F).map ψP ≫ χ =
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ G).obj K = _ by rw [e']) ≫
      (boundedConstructibleUpperStarComp Λ ℓ F Φ).hom.app K ≫
      (boundedConstructibleUpperStar Λ ℓ F).map ψ ≫ χ := by
  subst hψP hP e
  simp

variable {ℓ} in
/-- Blueprint `definition-frobenius-correspondences-their-operators`: the iterates of a Frobenius
correspondence `ψ : LΦ^* K ⟶ K` satisfy `ψ_{m+1} = ψ_m ∘ LΦ_m^* ψ`, that is
```
ψ_{m+1} : LΦ_{m+1}^* K = L(Φ_m ≫ Φ)^* K ≅ LΦ_m^* LΦ^* K --LΦ_m^* ψ--> LΦ_m^* K --ψ_m--> K,
```
so that `ψ_m = ψ ∘ LΦ^* ψ ∘ ⋯ ∘ L(Φ^{m-1})^* ψ`. -/
theorem frobeniusCoefficientIterate_succ' (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    frobeniusCoefficientIterate ψ (m + 1) =
      eqToHom (by rw [frobeniusIterate_succ']) ≫
        (boundedConstructibleUpperStarComp Λ ℓ (frobeniusIterate Φ m) Φ).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ m)).map ψ ≫
        frobeniusCoefficientIterate ψ m := by
  rw [← frobeniusCoefficientIterate_succ'_aux ℓ (frobeniusIterate_one Φ)
    (by rw [add_comm, frobeniusIterate_add]) (frobeniusIterate_succ' Φ m) ψ _
    (frobeniusCoefficientIterate_one ψ)]
  exact frobeniusCoefficientIterate_eq_of_eq_one_add ℓ ψ (add_comm m 1)
    (by rw [add_comm, frobeniusIterate_add])

end Iterate

/-! ### The model Frobenius -/

section Model

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- Blueprint `definition-frobenius-correspondences-their-operators`: the model Frobenius `Φ_X`
of a model locally of finite type is proper (it is finite,
`ProEtale.CondensedRing.IsModelFrobenius.isFinite`), so that its graph correspondences
`c_m = (𝟙, Φ_m)` have proper ordinary leg and act on compactly supported cohomology. -/
lemma IsModelFrobenius.isProper [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) :
    IsProper Φ.left := by
  have := hΦ.isFinite 1
  rw [frobeniusIterate_one] at this
  infer_instance

end Model

/-! ### Weil structures -/

namespace WeilBoundedConstructible

variable {ℓ}

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius`, in the setting where a Weil structure
is an isomorphism `φ : LΦ^* K ≅ K` for the scheme Frobenius `Φ` (so that `κ_m` is the identity
and `ψ_m = φ_m`, `WeilBoundedConstructible.iterateStr_hom_eq_frobeniusCoefficientIterate`): the
global operator of the graph correspondence `c_m = (𝟙, Φ_m)` with coefficient map `φ_m` is the
`m`-th power of the Frobenius operator on compactly supported cohomology,
`T_{c_m}(φ_m) = Frob_{X,K}^m`. -/
theorem globalOperator_graph_eq_pow (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left]
    [IsFinite (frobeniusIterate Φ 1).left] [IsUniversalHomeomorphism (frobeniusIterate Φ 1).left] :
    (K.graph m).globalOperator =
      (End.of (K.globalOperator 1) ^ m).asHom :=
  (globalOperator_eq_correspondenceGlobalOperator K m).symm.trans (globalOperator_eq_pow K m)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
