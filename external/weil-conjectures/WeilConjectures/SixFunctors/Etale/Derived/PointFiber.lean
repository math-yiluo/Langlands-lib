/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# Constructible complexes over a geometric point

Let `Λ` be a commutative ring and `k` a separably closed field. Étale sheaves of `Λ`-modules on
`Spec k` are `Λ`-modules: the global sections functor `Γ = Γ(Spec k, -)` is an exact equivalence
with inverse the constant sheaf functor (`constantSheafEquivalenceOfIsSepClosed`). A sheaf `F`
on `Spec k` is constructible if and only if `Γ(F)` is a finitely generated `Λ`-module: it is the
constant sheaf on `Γ(F)`, whose stalks are `Γ(F)`. Since `D(Γ)` commutes with homology and
preserves and reflects boundedness, the equivalence `D(Γ) : D((Spec k)_ét, Λ) ≌ D(Λ)`
restricts to an equivalence between `Dᵇc(Spec k, Λ)` and the full subcategory `Dᵇ_fin(Λ)` of
`D(Λ)` of bounded complexes with finitely generated (for `Λ` finite: finite) cohomology modules.

## Main definitions

- `DerivedCategory.boundedFiniteCohomology`: the object property `Dᵇ_fin(Λ)` of `D(Λ)`.
- `AlgebraicGeometry.Etale.pointFiber`: the evaluation
  `Fib_s : Dᵇc(Spec k, Λ) ⥤ Dᵇ_fin(Λ)` at the geometric point `s = Spec k`, the restriction
  of `D(Γ)`.
- `AlgebraicGeometry.Etale.pointFiberEquivalence` (`lemma-perfect-complexes-geometric-point`, finite
  coefficient stage): `Fib_s` is an equivalence. The integral stage `𝒪_E` is
  `AlgebraicGeometry.Etale.pointFiberIntegerRingEquivalence`
  (`WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The object property `Dᵇ_fin(Λ)` of the derived category `D(Λ)` of `Λ`-modules: bounded
complexes all of whose cohomology modules are finitely generated. For a finite ring `Λ` these are
the bounded complexes with finite cohomology modules
(`DerivedCategory.boundedFiniteCohomology_iff_finite`). -/
noncomputable def boundedFiniteCohomology :
    ObjectProperty (DerivedCategory (ModuleCat.{u + 1} Λ)) :=
  DerivedCategory.TStructure.t.bounded ⊓
    fun K ↦ ∀ n : ℤ, Module.Finite Λ ((homologyFunctor (ModuleCat.{u + 1} Λ) n).obj K)

variable {Λ} in
lemma boundedFiniteCohomology_iff (K : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    boundedFiniteCohomology Λ K ↔ DerivedCategory.TStructure.t.bounded K ∧
      ∀ n : ℤ, Module.Finite Λ ((homologyFunctor (ModuleCat.{u + 1} Λ) n).obj K) :=
  Iff.rfl

variable {Λ} in
/-- Over a finite ring, `Dᵇ_fin(Λ)` consists of the bounded complexes with finite cohomology. -/
lemma boundedFiniteCohomology_iff_finite [Finite Λ] (K : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    boundedFiniteCohomology Λ K ↔ DerivedCategory.TStructure.t.bounded K ∧
      ∀ n : ℤ, Finite ((homologyFunctor (ModuleCat.{u + 1} Λ) n).obj K) := by
  refine and_congr Iff.rfl
    (forall_congr' fun n ↦ ⟨fun _ ↦ Module.finite_of_finite Λ, fun _ ↦ ?_⟩)
  exact Module.Finite.of_finite

instance : (boundedFiniteCohomology Λ).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1, fun n ↦
      have := h.2 n
      Module.Finite.equiv ((homologyFunctor (ModuleCat.{u + 1} Λ) n).mapIso e).toLinearEquiv⟩

/-- The full subcategory `Dᵇ_fin(Λ)` of `D(Λ)` of bounded complexes with finitely generated
cohomology modules. -/
noncomputable abbrev BoundedFiniteCohomology : Type _ :=
  (boundedFiniteCohomology Λ).FullSubcategory

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (k : Type u) [Field k] [IsSepClosed k]

/-- The global sections `Γ(Spec k, -)` of étale sheaves of `Λ`-modules on `Spec k`, that is the
sections over the geometric point `Spec k ⟶ Spec k`. -/
noncomputable abbrev pointSections :
    Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (etalePoint k))

variable {Λ k}

/-- Over a separably closed field `k`, an étale sheaf `F` of `Λ`-modules on `Spec k` is
constructible if and only if its global sections form a finitely generated `Λ`-module: `F` is the
constant sheaf on `Γ(F)`, whose stalks are `Γ(F)`. -/
lemma isConstructibleSheaf_iff_moduleFinite_pointSections
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleSheaf F ↔ Module.Finite Λ ((pointSections Λ k).obj F) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let e : (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((pointSections Λ k).obj F) ≅ F :=
    (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).counitIso.app F
  constructor
  · intro hF
    have := hF.isFiniteSheaf
    have := IsFiniteSheaf.of_iso e.symm
    exact moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Spec (.of k)) _
  · intro hM
    have : IsFiniteLocallyConstantSheaf
        ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          ((pointSections Λ k).obj F)) :=
      { toIsFiniteSheaf := ⟨fun Ω _ _ s ↦
          ((ModuleCat.isFinitelyGenerated_iff _).2 hM).of_iso
            ((pointSmallEtale s).sheafFiberConstantSheafIso _).symm⟩ }
    have := this.isConstructibleSheaf
    exact IsConstructibleSheaf.of_iso e

/-- An object `K` of `D((Spec k)_ét, Λ)`, `k` separably closed, is bounded constructible if and
only if `D(Γ)(K) = RΓ(Spec k, K)` is bounded with finitely generated cohomology modules. -/
lemma boundedConstructible_iff_boundedFiniteCohomology
    (K : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) K ↔
      DerivedCategory.boundedFiniteCohomology Λ
        ((pointSections Λ k).mapDerivedCategory.obj K) := by
  refine and_congr ⟨(pointSections Λ k).bounded_mapDerivedCategory_obj,
    (pointSections Λ k).bounded_of_bounded_mapDerivedCategory_obj⟩
    (forall_congr' fun n ↦ ?_)
  rw [isConstructibleSheaf_iff_moduleFinite_pointSections]
  let e := ((pointSections Λ k).mapDerivedCategoryHomologyFunctorIso n).app K
  exact ⟨fun _ ↦ Module.Finite.equiv
      (M := (pointSections Λ k).obj
        ((DerivedCategory.homologyFunctor (Sheaf _ (ModuleCat.{u + 1} Λ)) n).obj K))
      e.toLinearEquiv,
    fun _ ↦ Module.Finite.equiv
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj
        ((pointSections Λ k).mapDerivedCategory.obj K))
      e.toLinearEquiv.symm⟩

variable (Λ k)

/-- The evaluation at the geometric point `s = Spec k ⟶ Spec k` (`k` separably closed),
`Fib_s : Dᵇc(Spec k, Λ) ⥤ Dᵇ_fin(Λ)`: the restriction of the functor `D(Γ)` induced on
derived categories by the exact global sections functor `Γ(Spec k, -)`; equivalently, of the
derived global sections `RΓ(Spec k, -)` (`AlgebraicGeometry.Etale.pointFiberCompιIso`). -/
noncomputable def pointFiber :
    DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) ⥤
      DerivedCategory.BoundedFiniteCohomology Λ :=
  (DerivedCategory.boundedFiniteCohomology Λ).lift
    ((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))).ι ⋙
      (pointSections Λ k).mapDerivedCategory)
    (fun K ↦ (boundedConstructible_iff_boundedFiniteCohomology K.obj).1 K.property)

/-- `Fib_s` is the restriction of the derived global sections `RΓ(Spec k, -)`. -/
noncomputable def pointFiberCompιIso :
    pointFiber Λ k ⋙ (DerivedCategory.boundedFiniteCohomology Λ).ι ≅
      DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) (Spec (.of k)) ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k)) :=
  Functor.isoWhiskerLeft _ (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ (k := k)).symm

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finite coefficient categories over a point
(finite coefficient stage `A_{E,n}`).

For a commutative ring `Λ` (in the blueprint the finite ring `A_{E,n} = 𝒪_E / ϖ_Eⁿ`) and a
separably closed field `k`, the evaluation at the geometric point of `s = Spec k`,
`Fib_s : Dᵇc(s, Λ) ⥤ Dᵇ_fin(Λ)` (`AlgebraicGeometry.Etale.pointFiber`, see
`AlgebraicGeometry.Etale.pointFiberEquivalence_functor`), is an equivalence onto the bounded
complexes of `Λ`-modules with finitely generated (for `Λ` finite, equivalently finite,
`DerivedCategory.boundedFiniteCohomology_iff_finite`) cohomology modules. It is the restriction
of the equivalence `D(Γ) : D(s_ét, Λ) ≌ D(Λ)` induced by the exact equivalence `Γ(s, -)`
between étale sheaves of `Λ`-modules on `s` and `Λ`-modules, a sheaf on `s` being constructible
if and only if its global sections are finitely generated.

The other coefficient stages of the blueprint node are
`AlgebraicGeometry.Etale.pointFiberIntegerRingEquivalence` (`𝒪_E`),
`AlgebraicGeometry.Etale.pointFiberFieldEquivalence` (`E`) and
`AlgebraicGeometry.Etale.pointFiberCocone_isFilteredTwoColimit` (`ℚ̄_ℓ`). As in the rest of the
repository the categories are those of the small étale site; the pro-étale comparison
(`WeilConjectures.SixFunctors.ProEtale.Comparison`) identifies them with the pro-étale
categories of the blueprint on bounded below objects of étale origin. -/
noncomputable def pointFiberEquivalence :
    DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) ≌
      DerivedCategory.BoundedFiniteCohomology Λ :=
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.functor.Additive :=
    additive_sheafSections_obj Λ _
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.inverse.Additive :=
    additive_constantSheaf Λ _
  (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).symm.mapDerivedCategory.congrFullSubcategory
    (by ext K; exact (boundedConstructible_iff_boundedFiniteCohomology K).symm)

lemma pointFiberEquivalence_functor : (pointFiberEquivalence Λ k).functor = pointFiber Λ k :=
  rfl

instance : (pointFiber Λ k).IsEquivalence :=
  inferInstanceAs (pointFiberEquivalence Λ k).functor.IsEquivalence

end Etale

end AlgebraicGeometry
