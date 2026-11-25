/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologyHom
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionTriangle

/-!
# Integral constructible complexes over a geometric point: common definitions

Shared definitions for `WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral`: the
constant sheaf `Λ` on a geometric point `Spec k`, placed in degree `j`, and the reduction
triangles `K ⟶ K ⟶ K ⊗ᴸ Λ/Iⁿ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-! ### The constant sheaf `Λ` on a geometric point -/

section Point

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

instance : (pointSections Λ k).Linear Λ where
  map_smul _ _ := rfl

variable (Λ k) in
/-- The constant sheaf `Λ` on `Spec k`. -/
noncomputable abbrev unitSheaf : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)

variable (Λ k) in
/-- The constant sheaf `Λ` on `Spec k` placed in degree `j`. -/
noncomputable abbrev unitSingle (j : ℤ) :
    DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.singleFunctor _ j).obj (unitSheaf Λ k)

end Point

/-! ### The reduction triangles -/

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. This single instance is used throughout this file and
the files `PointFiberIntegral*` importing it (as a local instance), so that all statements about
derived completeness use the same instance. -/
local instance essentiallySmall_etale_pointFiberIntegral (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section Reduction

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {X : Scheme.{u}}

include hϖ hI in
/-- The reduction `K ⊗ᴸ (Λ/Iⁿ)_X` is the cone of the multiplication by `ϖⁿ` on `K`: the
triangle `Λ ⟶ Λ ⟶ Λ/Iⁿ ⟶ Λ⟦1⟧` tensored with `K`. -/
lemma exists_distTriang_reductionModIdeal
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℕ) :
    ∃ (g : K ⟶ (reductionModIdeal Λ X (I ^ n)).obj K)
      (h : (reductionModIdeal Λ X (I ^ n)).obj K ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk (ϖ ^ n • 𝟙 K) g h ∈ distTriang _ := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let T := DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI n
  have hT : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished _ (DerivedCategory.quotPowTriangle_distinguished _ hϖ hI n)
  let u : F.obj T.obj₁ ≅ K := derivedTensorSingleUnitIso K
  have hmor : F.map T.mor₁ = ϖ ^ n • 𝟙 (F.obj T.obj₁) := by
    rw [DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul, CategoryTheory.Functor.map_id]
  refine ⟨u.inv ≫ F.map T.mor₂,
    F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫ u.hom⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ u.symm u.symm (Iso.refl _) ?_ ?_ ?_)⟩
  · change (ϖ ^ n • 𝟙 K) ≫ u.inv = u.inv ≫ F.map T.mor₁
    rw [hmor, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  · change (u.inv ≫ F.map T.mor₂) ≫ 𝟙 _ = u.inv ≫ F.map T.mor₂
    rw [Category.comp_id]
  · change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫ u.hom⟦(1 : ℤ)⟧') ≫
      u.inv⟦(1 : ℤ)⟧' = 𝟙 _ ≫ F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app _
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    simp

include hϖ hI in
/-- The terms `K ⊗ᴸ Λ/Iⁿ` of the tower of reductions of `DerivedCategory.derivedCompletionDiagram`
are the reductions `AlgebraicGeometry.Etale.reductionModIdeal`: both are cones of the
multiplication by `ϖⁿ` on `K`. -/
lemma nonempty_iso_derivedCompletionDiagram_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℕ) :
    Nonempty ((DerivedCategory.derivedCompletionDiagram X.smallEtaleTopology I K).obj (op n) ≅
      (reductionModIdeal Λ X (I ^ n)).obj K) := by
  obtain ⟨h, hT⟩ := DerivedCategory.exists_distTriang_derivedCompletionCone hϖ hI K n
  obtain ⟨g', h', hT'⟩ := exists_distTriang_reductionModIdeal hϖ hI K n
  obtain ⟨e, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ hT hT' (Iso.refl _)
  exact ⟨Triangle.π₃.mapIso e⟩

end Reduction

end Etale

end AlgebraicGeometry
