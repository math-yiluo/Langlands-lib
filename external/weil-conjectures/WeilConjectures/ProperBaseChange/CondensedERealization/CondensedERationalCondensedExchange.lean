/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions

/-! # Normalization of canonical realization exchange
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Tag 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.CondensedERealization
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
variable (D : Data l E k)
variable {X' X Y' Y : Base k}
variable {g' : X'.scheme ⟶ X.scheme} {f' : X'.scheme ⟶ Y'.scheme}
  {f : X.scheme ⟶ Y.scheme} {g : Y'.scheme ⟶ Y.scheme}
variable [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

end WeilConjectures.CondensedERealization
