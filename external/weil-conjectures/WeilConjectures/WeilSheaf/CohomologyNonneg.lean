/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology

/-!
# Cohomology of a Weil sheaf vanishes in negative degrees

The ordinary and the compactly supported cohomology `Hʳ(X ⊗ k̄, F)`, `Hʳ_c(X ⊗ k̄, F)` of a Weil
sheaf `F` vanish for `r < 0`: the derived pushforward `Rφ_*` of a complex concentrated in
degree `0` is concentrated in degrees `≥ 0`, and the extension by zero is exact.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_of_neg`
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_neg`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The global sections of a zero Weil sheaf vanish. -/
theorem WeilSheaf.subsingleton_globalSections_of_isZero {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : IsZero F) : Subsingleton F.globalSections.carrier :=
  ModuleCat.subsingleton_of_isZero <| Functor.map_isZero
    (ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l) ⋙ WeilCoefficients.toModuleCat l) hF

/-- The cohomology `Hʳ(Spec k̄, M)` of a Weil complex on `Spec k₀` concentrated in degrees `≥ a`
vanishes in degrees `r < a`. -/
theorem WeilComplex.subsingleton_cohomologyFrobeniusModule_of_isGE
    (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) {a : ℤ}
    (ha : _root_.DerivedCategory.IsGE ((ObjectProperty.ι _).obj M) a) {r : ℤ} (hr : r < a) :
    Subsingleton (M.cohomologyFrobeniusModule r).carrier :=
  WeilSheaf.subsingleton_globalSections_of_isZero
    (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (_root_.DerivedCategory.isZero_of_isGE (hX := ha) _ a r hr))

section LowerShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

omit [Fact (ringChar k₀ ≠ l)] in
/-- The direct image with compact support `Rf_! = Rḡ_* ∘ ī_!` of a pro-étale Weil sheaf placed
in degree `0` is concentrated in degrees `≥ 0`. -/
lemma ProEtaleWeilSheaf.isGE_rightDerivedLowerShriek_singleFunctor (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) (G : ProEtaleWeilSheaf k₀ l X) :
    _root_.DerivedCategory.IsGE ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) 0 := by
  have : _root_.DerivedCategory.TStructure.t.IsGE
      ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i ⋙ _root_.DerivedCategory.singleFunctor _ 0).obj
          G)) 0 :=
    Functor.isGE_rightDerivedFunctor_obj_singleFunctor (ProEtaleWeilSheaf.lowerStar k₀ l c.g)
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj G)
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app
        G).symm) 0

end LowerShriek

namespace WeilSheaf

section Ordinary

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology `Hʳ(Y ⊗ k̄, F)` of a Weil sheaf vanishes for `r < 0`. -/
theorem subsingleton_cohomology_of_neg (F : WeilSheaf k₀ l Y) {r : ℤ} (hr : r < 0) :
    Subsingleton (F.cohomology r).carrier :=
  WeilComplex.subsingleton_cohomologyFrobeniusModule_of_isGE _
    (Functor.isGE_rightDerivedFunctor_obj_singleFunctor _ F.obj) hr

end Ordinary

section CompactSupport

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology `Hʳ_c(X ⊗ k̄, F)` of a Weil sheaf vanishes for `r < 0`:
for the chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀`, `Rf_! F = Rg_*(i_! F)` with `i_!` exact,
so `Rf_! F` is `Rg_*` of a sheaf placed in degree `0`. -/
theorem subsingleton_compactlySupportedCohomology_of_neg (F : WeilSheaf k₀ l X) {r : ℤ}
    (hr : r < 0) : Subsingleton (F.compactlySupportedCohomology r).carrier :=
  WeilComplex.subsingleton_cohomologyFrobeniusModule_of_isGE _
    (ProEtaleWeilSheaf.isGE_rightDerivedLowerShriek_singleFunctor _ _ F.obj) hr

end CompactSupport

end WeilSheaf

end AlgebraicGeometry
