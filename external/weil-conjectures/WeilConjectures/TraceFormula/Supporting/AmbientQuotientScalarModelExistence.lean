/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Supporting.AmbientQuotientScalarNormalizationExistence

/-! # Ambient coherent scalar quotient realization

Source: Stacks 06YY and 0941; the scalar quotient construction in the final
common-stage transport paragraph of the trace-transport blueprint.
(blueprint: lem-trf-ambient-quotient-scalar-model-existence)
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Completed scalar change has a natural realization using the entire reduction
system, normalized on every whole-system adjunction-coherent quotient presentation.
No invertibility condition on the characteristic of the scheme is needed.
Source: Stacks 06YY, 0941, and the strict quotient scalar construction in the
trace-transport common-stage argument.
(blueprint: lem-trf-ambient-quotient-scalar-model-existence)

Proof: use the ordinary quotient extension/restriction adjunction and its derived
comparison with the supplied reduction calculus. On a flat-term K-flat complex,
extend its strict quotient system through the actual map of quotient coefficient
sheaves. At level n the balanced association sends (x tensor a) tensor b to
x tensor iota(a)b. Its inverse sends x tensor b to (x tensor 1) tensor b.
These are chain isomorphisms commuting with all horizontal quotient transitions
and all vertical restrictions. Applying the fixed normalized Roos comparison
identifies the resulting total limit with the defining completed scalar tower.
The derived change-of-rings counit is invertible on these K-flat systems, so this
comparison is a natural isomorphism on the resolving class. Fully faithful
whiskering along its localization descends it to a natural realization on the
ambient derived category. For any coherent presentation (C,e,kappa), the two
adjunction Hom bijections identify e with the canonical derived comparison
followed by the unique strict quotient isomorphism fixed by kappa. Transport the
balanced chain isomorphism along that strict isomorphism. Its value on each
tensor-unit generator is exactly the specified scalar tensor section; naturality
of the derived counit and Roos comparison gives the normalization equation in
the whole derived category. This uses neither faithfulness of finite derived
evaluation nor flatness of maps between quotient rings. Equal fields, identity
embeddings, exponent one, zero complexes and the empty scheme satisfy the same
balanced association and unit equations. -/
theorem ambientQuotientScalarModel_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X) :
    Nonempty (IntegralComparisonScalarModel l E L ι X S ρ) := by
  obtain ⟨realization, hnormalization⟩ :=
    ambientQuotientScalarModel_normalization_exists l E L ι X S ρ
  exact ⟨⟨realization, hnormalization⟩⟩

end WeilConjectures
