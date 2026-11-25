/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric

/-!
# The co-projection map of the exceptional inverse image of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type
and a Weil complex `L` on `Y`, the co-projection map
`f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L` of Weil complexes is natural in `L` and lies over the geometric
co-projection map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekUnitTensorMap`) on the geometric fibres
(`AlgebraicGeometry.WeilComplex.exists_coprojection_forget_eq_upperShriekUnitTensorMap`).
The tensor product is the native derived tensor product of Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`).

## Unfinished

The statement is proved with `sorry`. The map itself is the adjoint under `Rf₀! ⊣ Rf^!` of
`Rf₀!(f^* L ⊗ Rf^! ℚ̄_ℓ) ≅ L ⊗ Rf₀! Rf^! ℚ̄_ℓ ⟶ L ⊗ ℚ̄_ℓ ≅ L`, built from the compact-support
projection formula (`AlgebraicGeometry.WeilComplex.nonempty_nativeCompactProjectionLeft_iso`) and
the counit. That it lies over the geometric map needs the compatibility of forgetting the Weil
structure with the native tensor product, the projection formula, and the counit of
`Rf₀! ⊣ Rf^!`. Part of this compatibility is
`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`, but only as
an existence statement. The main obstruction is the projection formula: the Weil isomorphism
`Rf₀!(M ⊗ f^* T) ≅ Rf₀! M ⊗ T` is only known to exist, through the proper projection formula
`AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso`, which is
itself stated with `sorry`. Nothing is known about it after forgetting the Weil structure, and an
arbitrary isomorphism there changes the adjoint map by an automorphism of
`Rf₀!(f^* L ⊗ Rf^! ℚ̄_ℓ)` which need not come from `Rf₀!`. A proof needs the canonical
projection morphism of Weil complexes (built from the native pullback–tensor comparison and
`g^* ⊣ Rg_*` for the proper factor `g`) together with its comparison with the geometric one.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- **The co-projection map of Weil complexes lies over the geometric one** (blueprint:
`proposition-purity-trace-commute-frobenius`, the Weil equivariance of the map
`φ_{f,K} : Lf^* K ⊗ ω_f ⟶ Rf^! K` of `prose-09-07`, at the coefficient stage `ℚ̄_ℓ`): for a
separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type, there is
a morphism of Weil complexes `f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L`, natural in `L`, which on the geometric
fibre `X̄` is the geometric co-projection map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekUnitTensorMap`), up to isomorphisms `ψ_L`
of the sources and `φ_L` of the targets.

The isomorphism `φ_L` is the identification of the underlying complex of `Rf^! L` with
`Rf̄^! L̄` (`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`),
and `ψ_L` is the comparison of pullback and tensor product with forgetting the Weil structure,
together with `φ` at `ℚ̄_ℓ`; here both are only required to exist. -/
theorem exists_coprojection_forget_eq_upperShriekUnitTensorMap :
    ∃ π : upperStar f ⋙ (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))) ⋙
          nativeConstructibleTensor k₀ l X ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y,
        ∃ (φ : (adicSheafDerivedEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
              (forget.obj ((upperShriek f).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperShriek l (geometricFiberHom (k₀ := k₀) f)).obj
            (geometricFiberBoundedConstructibleObj L)).obj)
          (ψ : (adicSheafDerivedEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
              (forget.obj ((upperStar f ⋙ (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
                ((upperShriek f).obj (WeilSheaf.toComplex.obj
                  (WeilSheaf.adicConstant k₀ l Y)))) ⋙
                nativeConstructibleTensor k₀ l X).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)).obj
              (geometricFiberBoundedConstructibleObj L) ⊗
            (CondensedRing.boundedConstructibleUpperShriek l
              (geometricFiberHom (k₀ := k₀) f)).obj (𝟙_ _)).obj),
        (adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (π.app L)) ≫ φ.hom =
          ψ.hom ≫ (ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
            (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)) :=
  sorry

end AlgebraicGeometry.WeilComplex
