/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The pushforward of a lisse Weil sheaf along a finite étale morphism is lisse

For a finite étale morphism `g : Y ⟶ X` of `k₀`-schemes, the underlying `ℓ`-adic sheaf of
`g_* F` is the pushforward along the base change `ḡ : Ȳ ⟶ X̄` of `g` to the geometric fibres,
which is again finite étale; so `g_* F` is lisse for `F` lisse
(`AlgebraicGeometry.WeilSheaf.IsLisse.lowerStar_of_finite_etale`), by
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.lowerStar_of_finite_etale`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- **The pushforward of a lisse Weil sheaf along a finite étale morphism is lisse**: the base
change of `g` to the geometric fibres is finite étale. This is the lissity part of the blueprint
lemmas `lemma-finite-generically-etale-map-line--2` and
`lemma-finite-quasi-finite-direct-images--3`. -/
theorem IsLisse.lowerStar_of_finite_etale (g : Y ⟶ X) [g.IsOver (Spec (CommRingCat.of k₀))]
    [IsFinite g] [Etale g] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l Y} (hF : F.IsLisse) : ((lowerStar (k₀ := k₀) g).obj F).IsLisse := by
  have : IsFinite (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) g _ ‹_›
  have : Etale (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale) g _ ‹_›
  exact IsAdicLisseSheaf.lowerStar_of_finite_etale _ hF

end AlgebraicGeometry.WeilSheaf
