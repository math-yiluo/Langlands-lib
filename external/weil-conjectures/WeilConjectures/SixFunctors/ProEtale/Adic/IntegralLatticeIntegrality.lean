/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersApproximation
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeApproximation
public import WeilConjectures.SixFunctors.ProEtale.Adic.LatticeLocallyConstant

/-!
# Semilinearity of integral lattices from their integrality

Let `F` be a sheaf of `ℚ̄_ℓ,X`-modules, `M` a finite `𝒪_E`-module with `ℤ_ℓ → 𝒪_E` surjective
(`E = ℚ_ℓ`), `𝒪_E` with its `ℓ`-adic topology, and `ψ_U : C(U, M) → F(U)` natural additive
maps. A function `f ∈ C(U, 𝒪_E)` acts on `F(U)` by `v ↦ ι(f) • v`
(`AlgebraicGeometry.ProEtale.AdicSheaf.integersAct`). Then `ψ(f • m) = ι(f) • ψ(m)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.map_smul_of_integral`) provided

- the kernels of the `ψ_U` consist of `ℓ`-power torsion functions;
- the action of every `f ∈ C(U, 𝒪_E)` preserves the image of `ψ_U` (integrality).

This is `PadicAlgCl.map_smul_of_forall_exists_approx`, whose remaining inputs hold in general:
`F(U)` has no `ℓ`-torsion, being a `ℚ̄_ℓ`-vector space, every `f` is `g + ℓᵏ s` with `g`
locally constant with values in `ℕ` (`PadicAlgCl.exists_locally_natCast_add_pow_smul`), and
`ψ` is semilinear for such `g` (`AlgebraicGeometry.ProEtale.AdicSheaf.map_smul_of_locally_natCast`).
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale.AdicSheaf

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} (E : FiniteIntermediateField l)
  [TopologicalSpace (integers l E.1)] [IsTopologicalRing (integers l E.1)]
  (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
  (F : AdicSheaf l X) {M : Type} [AddCommGroup M] [Module (integers l E.1) M]
  [Module.Finite (integers l E.1) M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul (integers l E.1) M]

/-- The action `v ↦ ι(f) • v` of a function `f ∈ C(U, 𝒪_E)` on the sections of `F` over `U`. -/
noncomputable def integersAct (U : X.ProEt) (f : C(U.left, integers l E.1)) :
    F.X.obj.obj (op U) →+ F.X.obj.obj (op U) where
  toFun v := sectionAct F (ULift.up (ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f)) v
  map_zero' := sectionAct_zero F _
  map_add' := sectionAct_add F _

lemma integersAct_add (U : X.ProEt) (f g : C(U.left, integers l E.1))
    (v : F.X.obj.obj (op U)) :
    integersAct E hι F U (f + g) v = integersAct E hι F U f v + integersAct E hι F U g v := by
  refine (congrArg (fun a ↦ sectionAct F a v) ?_).trans (add_sectionAct F _ _ v)
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  change algebraMap _ (PadicAlgCl l) ((f + g) x) =
    algebraMap _ (PadicAlgCl l) (f x) + algebraMap _ (PadicAlgCl l) (g x)
  exact map_add _ _ _

lemma integersAct_nsmul (U : X.ProEt) (n : ℕ) (f : C(U.left, integers l E.1))
    (v : F.X.obj.obj (op U)) :
    integersAct E hι F U (n • f) v = n • integersAct E hι F U f v := by
  induction n with
  | zero =>
    rw [zero_smul, zero_smul]
    refine (congrArg (fun a ↦ sectionAct F a v) ?_).trans (zero_sectionAct F v)
    refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
    change algebraMap _ (PadicAlgCl l) ((0 : C(U.left, integers l E.1)) x) = 0
    exact map_zero _
  | succ n ih => rw [succ_nsmul, integersAct_add, ih, succ_nsmul]

omit [TopologicalSpace (integers l E.1)] [IsTopologicalRing (integers l E.1)] in
lemma eq_zero_of_natCast_smul_eq_zero {U : X.ProEt} (v : F.X.obj.obj (op U)) (h : l • v = 0) :
    v = 0 := by
  have hl : (ULift.up (l : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) ≠ 0 := fun h0 ↦
    Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero (congrArg ULift.down h0)
  have h' : (ULift.up (l : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) • v = 0 := by
    rw [← h, ← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (PadicAlgCl l))]
    rfl
  exact (smul_eq_zero.1 h').resolve_left hl

/-- **Semilinearity of integral lattices**: let `ψ_U : C(U, M) → F(U)` be natural additive maps,
`M` a finite `𝒪_E`-module, with `ℤ_ℓ → 𝒪_E` surjective and `𝒪_E` with its `ℓ`-adic topology.
If the kernels of the `ψ_U` consist of `ℓ`-power torsion functions and the action of the functions
`f ∈ C(U, 𝒪_E)` on `F(U)` preserves the image of `ψ_U`, then `ψ(f • m) = ι(f) • ψ(m)`. -/
theorem map_smul_of_integral
    (hτ : ‹TopologicalSpace (integers l E.1)› = integersLAdicTopology l E.1)
    (hsurj : Function.Surjective (integersPadicIntHom l E.1))
    (ψ : ∀ U : X.ProEt, C(U.left, M) →+ F.X.obj.obj (op U))
    (hψ : ∀ ⦃U V : X.ProEt⦄ (f : V ⟶ U) (m : C(U.left, M)),
      ψ V (m.comp f.left.base.hom) = F.X.obj.map f.op (ψ U m))
    (hker : ∀ (U : X.ProEt) (t : C(U.left, M)), ψ U t = 0 → ∃ n : ℕ, l ^ n • t = 0)
    (hint : ∀ (U : X.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
      ∃ e : C(U.left, M), integersAct E hι F U f (ψ U m) = ψ U e)
    (U : X.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)) :
    ψ U (f • m) = integersAct E hι F U f (ψ U m) := by
  refine map_smul_of_forall_exists_approx E (ψ U) (integersAct E hι F U)
    (integersAct_add E hι F U) (fun n f v ↦ integersAct_nsmul E hι F U n f v)
    (eq_zero_of_natCast_smul_eq_zero F) (hint U) (hker U) (fun f k ↦ ?_) f m
  obtain ⟨g, s, hfgs, hg⟩ := exists_locally_natCast_add_pow_smul hτ hsurj k f
  refine ⟨g, s, ContinuousMap.ext hfgs, fun m ↦ ?_⟩
  exact map_smul_of_locally_natCast _ hι (algebraMap_integers_mem l E.1) F ψ hψ g
    (fun x ↦ (hg x).elim fun O ⟨hO, hxO, n, hn⟩ ↦ ⟨⟨O, hO⟩, hxO, n, hn⟩) m

end AlgebraicGeometry.ProEtale.AdicSheaf
