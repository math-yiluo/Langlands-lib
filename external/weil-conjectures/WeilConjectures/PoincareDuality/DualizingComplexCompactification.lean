/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence

/-!
# The dualizing complex through a compactification over an isomorphic base

Let `f : X ⟶ Y` be a morphism of separated schemes of finite type over a field `k` whose base
`Y ⟶ Spec k` is an isomorphism (in the application, `Y` is the geometric fibre of `Spec k₀` over
`Spec k̄₀`). For every compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the exceptional inverse
image `Rf^!(c) = i^* Rg^!` of the unit is the dualizing complex `ω_X`
(`AlgebraicGeometry.ProEtale.CondensedRing.nonempty_upperShriekOfCompactification_obj_unit_iso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The dualizing complex through a compactification**: if the structure morphism of `Y` is an
isomorphism, then for every compactification `c` of `f : X ⟶ Y`, `Rf^!(c) ℚ̄_ℓ ≅ ω_X`. -/
theorem nonempty_upperShriekOfCompactification_obj_unit_iso [IsIso Y.hom] {f : X ⟶ Y}
    (c : Compactification f.left) :
    Nonempty ((boundedConstructibleUpperShriekOfCompactification ℓ c).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≅ dualizingComplex ℓ X) := by
  have : IsIso (Over.mkIdTerminal.from Y).left := by
    rw [Over.mkIdTerminal_from_left]
    infer_instance
  exact ⟨(conjugateIsoEquiv (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ c)
      (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ _ c)).app _ ≪≫
    (boundedConstructibleUpperShriek ℓ f).mapIso
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ (Over.mkIdTerminal.from Y)).symm ≪≫
    upperShriekDualizingComplexIso ℓ f⟩

end AlgebraicGeometry.ProEtale.CondensedRing
