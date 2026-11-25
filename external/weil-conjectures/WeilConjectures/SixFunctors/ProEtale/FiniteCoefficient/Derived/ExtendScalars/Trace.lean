/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
public import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# Derived scalar extension preserves traces

Let `S` be an algebra over a commutative ring `R`, not necessarily flat, and
`Ψ = L(S ⊗_R -) : D(X_proét, R) ⥤ D(X_proét, S)` derived extension of scalars of pro-étale
sheaves, which preserves flat sheaves
(`AlgebraicGeometry.ProEtale.preservesFlat_sheafExtendScalars`). Then `Ψ` is a braided monoidal
functor for the Koszul braidings `DerivedCategory.braidedCategory'`, its comonoidal structure
being the tensor comparison `Functor.leftDerivedTensorComparison`. Hence `Ψ` preserves categorical
traces, and the induced map on the endomorphisms of the unit sends `a • 𝟙` to
`algebraMap R S a • 𝟙`: the trace over `S` of `Ψ v` is the image of the trace of `v` over `R`
(blueprint `theorem-grothendieck-lefschetz-trace-formula--7`, using item (3) of
`proposition-properties-trace`).

## Main definitions and results

- `AlgebraicGeometry.ProEtale.sheafExtendScalars_map_braiding_hom_δ`: extension of scalars of
  sheaves is compatible with the braidings, by doctrinal adjunction, restriction of scalars
  being lax braided.
- `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsMonoidal`: the monoidal structure on
  `Ψ`, with comonoidal structure `Functor.leftDerivedTensorComparison`.
- `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsBraided`: `Ψ` is braided.
- `AlgebraicGeometry.ProEtale.trace_leftDerivedSheafExtendScalars_map`: `Ψ` preserves traces.
- `AlgebraicGeometry.ProEtale.ε_comp_leftDerivedSheafExtendScalars_map_smul_id_comp_η`: on the
  endomorphisms of the unit, `Ψ` is the ring map `algebraMap R S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

section Sheaf

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Extension of scalars of pro-étale sheaves is compatible with the braidings:
`(S ⊗_R -) β_{F, G} ≫ δ_{G, F} = δ_{F, G} ≫ β_{S ⊗_R F, S ⊗_R G}`. Its comonoidal structure is
obtained by doctrinal adjunction from the lax monoidal structure of restriction of scalars, which
is lax braided. -/
lemma sheafExtendScalars_map_braiding_hom_δ
    (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (sheafExtendScalars φ X).map (β_ F G).hom ≫ δ (sheafExtendScalars φ X) G F =
      δ (sheafExtendScalars φ X) F G ≫
        (β_ ((sheafExtendScalars φ X).obj F) ((sheafExtendScalars φ X).obj G)).hom :=
  ((sheafExtendScalarsAdjunction φ X).leftAdjointOplaxMonoidal_δ_braiding F G).symm

/-- Restriction of scalars of pro-étale sheaves along `φ` sends `φ a • 𝟙` to `a • 𝟙`. -/
lemma sheafComposeRestrictScalars_map_smul_id
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} S)) (a : R) :
    (sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ)).map
        (φ a • 𝟙 F) = a • 𝟙 _ := by
  ext U x
  rfl

/-- Extension of scalars of pro-étale sheaves along `φ` sends `a • 𝟙` to `φ a • 𝟙`. -/
lemma sheafExtendScalars_map_smul_id
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) (a : R) :
    (sheafExtendScalars φ X).map (a • 𝟙 F) = φ a • 𝟙 _ := by
  apply ((sheafExtendScalarsAdjunction φ X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← (sheafExtendScalarsAdjunction φ X).unit.naturality]
  rw [sheafComposeRestrictScalars_map_smul_id, Functor.id_map]
  simp

end Sheaf

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- Derived scalar extension `Ψ = L(S ⊗_R -) : D(X_proét, R) ⥤ D(X_proét, S)` as a monoidal
functor, with comonoidal structure the tensor comparison `Functor.leftDerivedTensorComparison`. -/
@[instance_reducible]
noncomputable def leftDerivedSheafExtendScalarsMonoidal :
    L(sheafExtendScalars (algebraMap R S) X).Monoidal :=
  (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorMonoidal

attribute [local instance] DerivedCategory.braidedCategory'

/-- The braided structure on derived scalar extension `Ψ = L(S ⊗_R -)`, for the Koszul braidings
`DerivedCategory.braidedCategory'`, whose monoidal structure is
`leftDerivedSheafExtendScalarsMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedSheafExtendScalarsBraided :
    L(sheafExtendScalars (algebraMap R S) X).Braided :=
  (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorBraided
    (sheafExtendScalars_map_braiding_hom_δ (algebraMap R S) X)

/-- **Derived scalar extension preserves traces** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`, via item (3) of `proposition-properties-trace`).
For the monoidal structure `leftDerivedSheafExtendScalarsMonoidal` of `Ψ = L(S ⊗_R -)` and the
Koszul braidings `DerivedCategory.braidedCategory'`, the trace over `S` of `Ψ v` is the image of the
trace over `R` of `v`: `tr(Ψ v) = ε ≫ Ψ(tr v) ≫ η`, for an endomorphism `v` of a dualizable `P` such
that `Ψ P` is dualizable. -/
theorem trace_leftDerivedSheafExtendScalars_map
    {P : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    [HasRightDual P] [HasRightDual (L(sheafExtendScalars (algebraMap R S) X).obj P)]
    (v : P ⟶ P) :
    letI := leftDerivedSheafExtendScalarsMonoidal (R := R) (S := S) X
    trace (L(sheafExtendScalars (algebraMap R S) X).map v) =
      ε L(sheafExtendScalars (algebraMap R S) X) ≫
        L(sheafExtendScalars (algebraMap R S) X).map (trace v) ≫
          η L(sheafExtendScalars (algebraMap R S) X) :=
  (sheafExtendScalars (algebraMap R S) X).trace_leftDerivedFunctor_map
    (sheafExtendScalars_map_braiding_hom_δ (algebraMap R S) X) v

/-- On the endomorphisms of the unit, derived scalar extension `Ψ = L(S ⊗_R -)` is the ring map
`algebraMap R S`: `ε ≫ Ψ (a • 𝟙) ≫ η = algebraMap R S a • 𝟙` (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`). Together with
`AlgebraicGeometry.ProEtale.trace_leftDerivedSheafExtendScalars_map`, this says that `ρ(tr_R) =
tr_S` for traces which are scalars. -/
lemma ε_comp_leftDerivedSheafExtendScalars_map_smul_id_comp_η (a : R) :
    letI := leftDerivedSheafExtendScalarsMonoidal (R := R) (S := S) X
    ε L(sheafExtendScalars (algebraMap R S) X) ≫
        L(sheafExtendScalars (algebraMap R S) X).map (a • 𝟙 (𝟙_ _)) ≫
          η L(sheafExtendScalars (algebraMap R S) X) =
      algebraMap R S a • 𝟙 (𝟙_ _) :=
  (sheafExtendScalars (algebraMap R S) X).ε_comp_leftDerivedFunctor_map_smul_id_comp_η
    (algebraMap R S) (sheafExtendScalars_map_smul_id (algebraMap R S) X) a

end AlgebraicGeometry.ProEtale
