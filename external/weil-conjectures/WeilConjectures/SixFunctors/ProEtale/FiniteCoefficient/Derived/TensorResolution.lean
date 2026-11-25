/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Resolution independence and functoriality of the pro-étale derived tensor product

The derived tensor product `- ⊗ᴸ -` of `D(X_proét)`
(`AlgebraicGeometry.ProEtale.derivedTensor`) is the left derived bifunctor of the tensor product
of complexes of pro-étale sheaves along the K-flat left derivability structure. This file
records the two properties of blueprint `prose-03-02` and
`lem-weil-derived-tensor-functorial`:

* a quasi-isomorphism `P ⟶ P'` between K-flat complexes stays a quasi-isomorphism after
  tensoring with any complex (Stacks `064L`), so that `K₁ ⊗ᴸ K₂` may be computed as `P ⊗ K₂` for
  any K-flat resolution `P` of `K₁`;
* the derived tensor product is a functor in each variable, and the two ways of applying a pair
  of morphisms agree.

## Main statements

- `AlgebraicGeometry.ProEtale.quasiIso_whiskerRight_of_kFlat`: Stacks `064L` for complexes of
  pro-étale sheaves.
- `AlgebraicGeometry.ProEtale.isIso_μ_Qh_of_kFlat`: `Qh(P) ⊗ᴸ Qh(K₂) ≅ Qh(P ⊗ K₂)`
  for a K-flat `P`.
- `AlgebraicGeometry.ProEtale.derivedTensor_map_app_comp_map`: functoriality in both variables.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- Blueprint `prose-03-02`: Resolution independence of the
derived tensor product.

For complexes of `A`-valued sheaves on the small pro-étale site of `X`, a quasi-isomorphism
`α : P ⟶ P'` between K-flat complexes induces a quasi-isomorphism `P ⊗ K₂ ⟶ P' ⊗ K₂` for every
complex `K₂` (Stacks `064L`). In particular, for two K-flat resolutions `P ⟶ K₁` and `P' ⟶ K₁`,
any lift `P ⟶ P'` of the identity of `K₁` in the homotopy category is a quasi-isomorphism, and so
is the induced map `P ⊗ K₂ ⟶ P' ⊗ K₂`; the object `P ⊗ K₂` computing `K₁ ⊗ᴸ K₂`
(`AlgebraicGeometry.ProEtale.isIso_μ_Qh_of_kFlat`) does not depend on the resolution. -/
theorem quasiIso_whiskerRight_of_kFlat
    {P P' : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)}
    (α : P ⟶ P') (hα : HomotopyCategory.quasiIso _ _ α)
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P)
    (hP' : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P')
    (K₂ : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)) :
    HomotopyCategory.quasiIso _ _ (α ▷ K₂) := by
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology X) A) := inferInstance
  have := IsGrothendieckAbelian.hasColimits (C := Sheaf (Scheme.ProEt.topology X) A)
  have : HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X) A) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have (Y : Sheaf (Scheme.ProEt.topology X) A) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj Y) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z) (by intros; simp [curriedTensor]))
  exact MorphismProperty.whiskerRight_of_kFlat _ α hα hP hP' K₂

/-- Blueprint `prose-03-02`: for a K-flat complex `P` of
pro-étale sheaves, the comparison `Qh(P) ⊗ᴸ Qh(K₂) ⟶ Qh(P ⊗ K₂)` is an isomorphism, so that the
derived tensor product `K₁ ⊗ᴸ K₂` is computed by `P ⊗ K₂` for any K-flat resolution `P` of
`K₁`. -/
theorem isIso_μ_Qh_of_kFlat
    (P : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ))
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P)
    (K₂ : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh P K₂) :=
  DerivedCategory.isIso_μ_Qh_of_kFlat P K₂ hP

/-- Blueprint `lem-weil-derived-tensor-functorial`: Functoriality of the derived tensor product.

For morphisms `φ : K₁ ⟶ K₁'` and `ψ : K₂ ⟶ K₂'` in `D(X_proét)`, applying the derived tensor
product first in the first and then in the second variable agrees with the other order; the
common value is the induced morphism `φ ⊗ ψ : K₁ ⊗ᴸ K₂ ⟶ K₁' ⊗ᴸ K₂'`. The derived tensor product
being a bifunctor `D(X_proét) ⥤ D(X_proét) ⥤ D(X_proét)`, the assignment carries identities to
identities and composites to composites in each variable (`Functor.map_id`, `Functor.map_comp`,
`MonoidalCategory.tensor_comp`). -/
theorem derivedTensor_map_app_comp_map
    {K₁ K₁' K₂ K₂' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (φ : K₁ ⟶ K₁')
    (ψ : K₂ ⟶ K₂') :
    ((derivedTensor A X).map φ).app K₂ ≫ ((derivedTensor A X).obj K₁').map ψ = φ ⊗ₘ ψ ∧
      ((derivedTensor A X).obj K₁).map ψ ≫ ((derivedTensor A X).map φ).app K₂' = φ ⊗ₘ ψ :=
  ⟨(tensorHom_def φ ψ).symm, (tensorHom_def' φ ψ).symm⟩

end AlgebraicGeometry.ProEtale
