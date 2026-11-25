/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Composition of pushforwards of pro-étale Weil sheaves

The pushforward `φ_*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes is
the pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
the exchange isomorphism `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*`. The composition isomorphisms
`φ̄_* ⋙ ψ̄_* ≅ (φ̄ ≫ ψ̄)_*` are compatible with these exchange isomorphisms
(`AlgebraicGeometry.ProEtale.lowerStarComp_exchange`), hence induce an isomorphism of
pushforwards of pro-étale Weil sheaves.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompIso`: `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCongr`: pushforwards along equal morphisms are
  isomorphic.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The composition isomorphism `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*` of pushforwards of pro-étale Weil
sheaves: the composition isomorphism of pushforwards along the base changes, which is compatible
with the Weil structures. -/
noncomputable def ProEtaleWeilSheaf.lowerStarCompIso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ⋙ ProEtaleWeilSheaf.lowerStar k₀ l ψ ≅
      ProEtaleWeilSheaf.lowerStar k₀ l (φ ≫ ψ) :=
  IsoAlgebra.mapOfNatIsoCompIso _ _ ≪≫ IsoAlgebra.mapOfNatIsoIsoOfIso
    (adicLowerStarComp l _ _ ≪≫ adicLowerStarCongr l
      (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ _) (comp_over ψ _)).symm) (by
      ext K : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        IsoAlgebra.compCommIso_hom_app, Iso.trans_hom,
        adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.symm_hom, Category.assoc]
      exact ProEtale.adicLowerStarComp_exchange _ _ _
        (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ _) (comp_over ψ _)).symm _ _ _
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ _)
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv ψ _)
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv (φ ≫ ψ) _) K)

variable (k₀ l) in
/-- Pushforwards of pro-étale Weil sheaves along equal morphisms are isomorphic. -/
noncomputable def ProEtaleWeilSheaf.lowerStarCongr {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ≅ ProEtaleWeilSheaf.lowerStar k₀ l φ' := by
  subst h
  exact Iso.refl _

end AlgebraicGeometry
