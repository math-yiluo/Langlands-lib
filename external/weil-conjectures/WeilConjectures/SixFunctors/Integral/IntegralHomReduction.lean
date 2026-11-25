/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomModelsExist
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomComparisonIsIso
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomRoosTransport

/-! # Integral internal Hom and reduction

Source: blueprint order 2134; Stacks Tags 08J9, 07A6, 07A4 and 08TC
(blueprint: proposition-six-operations-change-coefficients--7).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

set_option backward.isDefEq.respectTransparency false in
/-- Integral internal Hom commutes with every positive reduction and preserves
completeness in the second variable, without a condition on the first variable.
The existential presentations supply, rather than assume, derived tensor and its
canonical evaluation and coefficient comparisons. Their representative equations
fix the constructions on local sections. The comparison itself is a defined
transpose; the following clauses assert its invertibility, its evaluation equation,
and compatibility with every transpose.

Source: blueprint, chap-The-six-operations-on-Dbctf, sk-prop-sf-biduality-general,
proposition-six-operations-change-coefficients--7, order 2134
(blueprint: proposition-six-operations-change-coefficients--7).

Proof:
1. The valuation ring is a DVR and hence Noetherian
   (lem-weil-l-adic-extension-integers-dvr). The standard perfect quotient
   resolution and completed-constant-sheaf reduction identify the restricted
   quotient with Q_n=[B --t^(n+1)--> B]. It is K-flat by the bounded-flat lemma.
   The maps Q_m to Q_n are (t^(m-n),1) and preserve the degree-zero unit.
2. Ringed internal-Hom currying and RHom global sections give tensor-Hom
   adjunction on each ambient unbounded category. Total tensor on K-flat
   representatives fixes tensor, and ordinary chain evaluation fixes its counit.
   These are precisely the TensorPresentation fields, including the Koszul sign.
3. Apply derived coefficient extension/restriction adjunction and canonical
   tensor pullback to the limit projection. The ordinary unit is x maps to
   1 tensor x; the inverse tensor comparison multiplies the coefficient factors.
   This gives the normalization of ReductionPresentation. Exact restriction is
   conservative because it leaves the underlying cohomology sheaves unchanged.
4. Adjunction and Yoneda identify restricted finite internal Hom with
   H_B(K,U_n N). This uses arbitrary K, not a perfectness assumption.
5. Represent K by a K-flat complex P and L by a K-injective complex I.
   Tensor I with Q_n; it is K-injective by the split-perfect tensor lemma.
   Both H_B(K,L) tensor Q_n and H_B(K,L tensor Q_n) therefore have the
   Hom-complex models specified in the node's proof.
6. The chain comparison sends f tensor q to
   (x maps to (-1)^(degree(q)*degree(x)) f(x) tensor q). It is an isomorphism:
   only two coefficient degrees interchange with the Hom products. The Hom
   and total-tensor differentials give equal signs on all three terms.
   This remains valid for unbounded P and is natural in Q_n and its unit.
7. The coefficient adjunction identifies the restriction of the defined
   comparison with that chain map. Conservativity proves invertibility in
   D(B_n). Its definition as a transpose gives the evaluation equation;
   naturality of tensor comparison gives the displayed equation for every
   other transpose, by injectivity of the adjunction bijection.
8. Apply H_B(K,-), an exact right adjoint, to the actual Roos triangle of L.
   Right-adjoint preservation of products identifies all projections and hence
   the endomorphism 1-s. The comparisons from steps 5-6 preserve the quotient
   units and transitions. Transporting the triangle therefore gives the Roos
   triangle of H_B(K,L), exactly IsDerivedComplete. K need not be complete. -/
theorem integralHomReduction :
    ∃ a : IntegralHom.TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl),
      (∀ K L : completedIntegralDerivedCategory l E Y D hl,
        IsDerivedComplete l E Y D hl L →
          IsDerivedComplete l E Y D hl
            ((IntegralHom.hom.{t, u} Y
              (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L))) ∧
      ∀ n : ℕ, ∃ m : IntegralHom.ReductionPresentation l E Y D hl a n,
        ∀ K L : completedIntegralDerivedCategory l E Y D hl,
          IsIso (IntegralHom.comparison l E Y D hl m K L) ∧
          (m.target.tensor.map (Prod.mkHom
              (𝟙 ((integralDerivedReduction l E Y D hl n).obj K))
              (IntegralHom.comparison l E Y D hl m K L)) ≫
            (m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).counit.app
              ((integralDerivedReduction l E Y D hl n).obj L) =
            m.mu.inv.app (K,
              (IntegralHom.hom.{t, u} Y
                (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) ≫
            (integralDerivedReduction l E Y D hl n).map ((a.adjunction K).counit.app L)) ∧
          ∀ (T : completedIntegralDerivedCategory l E Y D hl)
            (f : T ⟶
              (IntegralHom.hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)),
            (m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).homEquiv
                ((integralDerivedReduction l E Y D hl n).obj T)
                ((integralDerivedReduction l E Y D hl n).obj L)
                (m.mu.inv.app (K, T) ≫ (integralDerivedReduction l E Y D hl n).map
                  (((a.adjunction K).homEquiv T L).symm f)) =
              (integralDerivedReduction l E Y D hl n).map f ≫
                IntegralHom.comparison l E Y D hl m K L := by
  classical
  obtain ⟨a, ha⟩ := IntegralHom.models_exist l E Y D hl
  refine ⟨a, ?_, ?_⟩
  · intro K L hL
    exact IntegralHom.hom_roosTransport l E Y D hl a K L hL
  · intro n
    obtain ⟨m⟩ := ha n
    refine ⟨m, ?_⟩
    intro K L
    refine ⟨?_, ?_, ?_⟩
    · exact IntegralHom.comparison_isIso l E Y D hl a n m K L
    · exact (m.target.adjunction
        ((integralDerivedReduction l E Y D hl n).obj K)).homEquiv _ _
          |>.symm_apply_apply _
    · intro T f
      dsimp only [IntegralHom.comparison]
      rw [← Adjunction.homEquiv_naturality_left]
      congr 1
      rw [Adjunction.homEquiv_counit, Functor.map_comp]
      simp only [← Category.assoc]
      simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id,
        Functor.curry_obj_obj_map,
        (integralDerivedReduction l E Y D hl n).map_id] using
        congrArg (fun g ↦ g ≫
          (integralDerivedReduction l E Y D hl n).map ((a.adjunction K).counit.app L))
          (m.mu.inv.naturality (Prod.mkHom (𝟙 K) f)).symm

end WeilConjectures
