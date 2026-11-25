/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethBraided
public import WeilConjectures.TraceFormula.Specialization.KernelPullbackDeformation
public import WeilConjectures.Tactic.TransportExact

/-!

# Nearby cycles on bounded constructible complexes are lax braided

The lax tensor maps of nearby cycles on bounded constructible complexes
(`ProEtale.CondensedRing.NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal`) commute
with the Koszul braidings (`ProEtale.CondensedRing.boundedConstructibleBraiding`): this is the
symmetry of `μ` of blueprint `sec-Base-change-for-nearby-cycles` on `Dᵇc`
(`ProEtale.CondensedRing.NearbyCyclesModel.boundedConstructibleNearbyCycles_μ_braiding`), from
the ambient `ProEtale.CondensedRing.NearbyCyclesModel.tensorMap_braiding`. It is the hypothesis
`hbr` of the first identity of blueprint `lemma-nearby-cycles-universal-kernel`
(`CategoryTheory.map_curry_kunnethPairing_comp_eq`) for the specialization of `X ⨯ X`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C D : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [Category D]
  [MonoidalCategory D] [BraidedCategory D] {P : ObjectProperty C} [P.IsMonoidal]
  {Q : ObjectProperty D} [Q.IsMonoidal]

/-- The restriction of a lax braided functor to full monoidal subcategories is lax braided. -/
lemma ObjectProperty.laxMonoidalLift_μ_braiding (F : C ⥤ D) [F.LaxMonoidal]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (h : ∀ X Y : C, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ F Y X) (X Y : P.FullSubcategory) :
    letI := ObjectProperty.laxMonoidalLift F hF
    Functor.LaxMonoidal.μ (Q.lift (P.ι ⋙ F) hF) X Y ≫ (Q.lift (P.ι ⋙ F) hF).map (β_ X Y).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ (Q.lift (P.ι ⋙ F) hF) Y X :=
  ObjectProperty.hom_ext _ (h X.obj Y.obj)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] DerivedCategory.braidedCategory' boundedConstructibleBraiding
  NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k] [Field k'] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- The tensor maps of the lax monoidal structure of nearby cycles on bounded constructible
complexes are `NearbyCyclesModel.boundedConstructibleTensorMap`. -/
lemma boundedConstructibleNearbyCycles_μ
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hP) A B =
      boundedConstructibleTensorMap hP A B := by
  apply ObjectProperty.hom_ext
  exact nearbyCyclesLaxMonoidal_μ _ M A.obj B.obj

omit [IsSeparated X.hom] [IsSeparated X'.hom] in
/-- **Nearby cycles on bounded constructible complexes are lax braided** (blueprint
`sec-Base-change-for-nearby-cycles`, "`μ` is symmetric"). -/
lemma boundedConstructibleNearbyCycles_μ_braiding
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hP) A B ≫
        (boundedConstructibleNearbyCycles hP).map (β_ A B).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hP) B A := by
  let := M.nearbyCyclesLaxMonoidal (Profinite.padicAlgClRingObj ℓ)
  refine ObjectProperty.laxMonoidalLift_μ_braiding (M.nearbyCycles _) _ (fun X Y ↦ ?_) A B
  rw [nearbyCyclesLaxMonoidal_μ, nearbyCyclesLaxMonoidal_μ]
  exact (M.tensorMap_braiding _ X Y).symm

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
