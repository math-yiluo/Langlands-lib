/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators

/-! Lattice filtration step for topological Noetherian integral generators.
Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2), together with the
ordered lattice filtration in the topological Noetherian integral-model argument
(blueprint: lem-sfb-topological-lisse-integral-closure).

The missing argument constructs a finite stratified integral lattice filtration of a
lisse finite-coefficient module and identifies each quotient with an integral generator.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.SixFunctors

/-- A lisse finite-coefficient extension `v_! t_* L` belongs to the triangulated,
isomorphism-closed closure of the integral locally free generators.

Source: Bhatt--Scholze, Lemma 6.8.13 (first paragraph) and Proposition 6.8.14(2);
steps 1 and 3 of the plan of lem-sfb-topological-integral-generators
(blueprint: lem-sfb-topological-lisse-integral-closure).

Proof:
1. `T` is topologically Noetherian, as a subspace of `X`. By
   lem-sfb-topological-stratified-lattices choose an ordered finite stratification
   `T = ⊔ T_k` with opens `U_k = T_1 ∪ ... ∪ T_k` (`u_k : U_k → T`, `b_k : T_k → T`,
   `c_k : T_k → U_k` closed) and `O_E`-lattices `L_{0,k} ⊆ b_k^* L` with
   `E ⊗ L_{0,k} ≅ b_k^* L`.
2. Put `L_k = u_{k!} u_k^* L`. The open-closed localization sequence
   (lem-weil-pbc-proetale-ringed-open-closed) makes `L_{k-1} → L_k` monic, and by
   lem-sfb-open-filtration-successor `L_k / L_{k-1} ≅ u_{k!} c_{k*} (b_k^* L)`, with
   `L_0 = 0` and `L_m = L`.
3. `v_!` and `t_*` are exact, so applying them gives a finite filtration of `v_! t_* L`;
   by the composition comparisons of lem-sfb-topological-locally-closed-extension each
   quotient is `a_{k!}(b_k^* L)` for the locally closed `a_k : T_k → X`, written as an
   open immersion followed by a closed immersion (all opens are quasi-compact by
   lem-sfb-noetherian-space-compact-subsets).
4. `E_X` is flat over `O_{E,X}` (lemma-comparison-completed-coefficients--2), and the open and
   closed projection formulas (lem-sfb-condensed-support-projection-formula) give
   `E ⊗ a_{k!} L_{0,k} ≅ a_{k!}(E ⊗ L_{0,k}) ≅ a_{k!}(b_k^* L)`: each quotient in degree
   zero is isomorphic to an integral generator.
5. Each short exact sequence of the filtration is a distinguished triangle
   (lem-sf-derived-ses-triangle); induction on `k`, starting from the zero object, puts
   `v_! t_* L [0]` in the closure. -/
theorem topological_lisse_integral_closure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (T V : Scheme.{u}) (t : T ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion t] [IsOpenImmersion v]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (finiteCoefficientObject T ℓ E))
    (hL : IsLocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E.1) T) L) :
    (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
      P.IsClosedUnderIsomorphisms})
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj E.1) v).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) t).obj L))) := by
  sorry

end WeilConjectures.SixFunctors
