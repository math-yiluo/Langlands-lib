/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TensorSingle

/-!
# The top homology sheaf of a derived tensor product with a sheaf

For a sheaf `B` on `X_ét` placed in degree `0` and an object `M` of `D(X_ét)` concentrated in
degrees `≤ q`, the top homology sheaf of the derived tensor product is the underived tensor
product with the top homology sheaf: `Hᵠ(B[0] ⊗ᴸ M) ≅ B ⊗ Hᵠ(M)`, naturally in `B`
(`AlgebraicGeometry.Etale.singleFunctorTensorRightHomologyIso`). Indeed `M ⟶ τ^{≥q} M` induces an
isomorphism on `Hᵠ(B[0] ⊗ᴸ -)` (the fibre `τ^{≤q-1} M` gives objects in degrees `≤ q - 1`),
`τ^{≥q} M ≅ Hᵠ(M)[-q]`, and `H⁰(B[0] ⊗ᴸ C[0]) ≅ B ⊗ C`
(`AlgebraicGeometry.Etale.isIso_homologyFunctor_map_singleFunctorTensorToSingle_app`).
This is used in the proof of blueprint `lemma-kunneth-field-coefficients--1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` with `X₁` concentrated in degrees
`≤ q - 1`, the map `Hᵠ(X₂) ⟶ Hᵠ(X₃)` is an isomorphism. -/
lemma isIso_homologyFunctor_map_mor₂_of_isLE (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (q : ℤ) [T.obj₁.IsLE (q - 1)] :
    IsIso ((homologyFunctor C q).map T.mor₂) := by
  have : Mono ((homologyFunctor C q).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT q).2
      ((T.obj₁.isZero_of_isLE (q - 1) q (by lia)).eq_of_src _ _)
  have : Epi ((homologyFunctor C q).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT q (q + 1)).2
      ((T.obj₁.isZero_of_isLE (q - 1) (q + 1) (by lia)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- An object of the derived category concentrated in degree `n` is isomorphic to its `n`-th
homology object placed in degree `n`. -/
noncomputable def isoSingleFunctorObjHomologyOfIsGEOfIsLE (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K) :=
  let Y := (K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n).choose
  let e : K ≅ (singleFunctor C n).obj Y :=
    (K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n).choose_spec.some
  e ≪≫ (singleFunctor C n).mapIso
    (((singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫ (homologyFunctor C n).mapIso e.symm)

/-- For `M` concentrated in degrees `≤ q`, the truncation `τ^{≥q} M` is isomorphic to
`Hᵠ(M)` placed in degree `q`. -/
noncomputable def truncGEIsoSingleFunctorObjHomology (M : DerivedCategory C) (q : ℤ)
    [M.IsLE q] :
    (TStructure.t.truncGE q).obj M ≅ (singleFunctor C q).obj ((homologyFunctor C q).obj M) :=
  have : ((TStructure.t.truncGE q).obj M).IsLE q :=
    inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE q).obj M) q)
  have : ((TStructure.t.truncGE q).obj M).IsGE q :=
    inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE q).obj M) q)
  have := isIso_homologyFunctor_map_truncGEπ_app M q q le_rfl
  isoSingleFunctorObjHomologyOfIsGEOfIsLE _ q ≪≫ (singleFunctor C q).mapIso
    (asIso ((homologyFunctor C q).map ((TStructure.t.truncGEπ q).app M))).symm

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- `H⁰(B[0] ⊗ᴸ N[0]) ≅ B ⊗ N`, naturally in the sheaf `B`. -/
noncomputable def singleFunctorTensorRightSingleHomologyZeroIso
    (N : Sheaf X.smallEtaleTopology A) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj N) ⋙
          DerivedCategory.homologyFunctor _ 0 ≅
      tensorRight N :=
  have (B : Sheaf X.smallEtaleTopology A) : IsIso ((Functor.whiskerRight
      (singleFunctorTensorToSingle N) (DerivedCategory.homologyFunctor _ 0)).app B) :=
    isIso_homologyFunctor_map_singleFunctorTensorToSingle_app N B
  have : IsIso (Functor.whiskerRight (singleFunctorTensorToSingle N)
      (DerivedCategory.homologyFunctor _ 0)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight (singleFunctorTensorToSingle N)
      (DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerLeft (tensorRight N)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0)

/-- The truncation map `M ⟶ τ^{≥q} M` induces an isomorphism
`Hᵠ(B[0] ⊗ᴸ M) ≅ Hᵠ(B[0] ⊗ᴸ τ^{≥q} M)`, naturally in the sheaf `B`: the fibre `τ^{≤q-1} M`
gives `B[0] ⊗ᴸ τ^{≤q-1} M` concentrated in degrees `≤ q - 1`. -/
noncomputable def singleFunctorTensorRightTruncGEHomologyIso
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (q : ℤ) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙ tensorRight M ⋙
        DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
        tensorRight ((DerivedCategory.TStructure.t.truncGE q).obj M) ⋙
          DerivedCategory.homologyFunctor _ q :=
  have (B : Sheaf X.smallEtaleTopology A) : IsIso ((Functor.whiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
      (Functor.whiskerRight ((tensoringRight _).map
        ((DerivedCategory.TStructure.t.truncGEπ q).app M))
          (DerivedCategory.homologyFunctor _ q))).app B) := by
    let K := (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj B
    let T := (DerivedCategory.TStructure.t.triangleLTGE q).obj M
    have hle := DerivedCategory.isLE_tensor K T.obj₁ 0 (q - 1)
    rw [zero_add] at hle
    have : (((derivedTensor A X).obj K).mapTriangle.obj T).obj₁.IsLE (q - 1) := hle
    exact DerivedCategory.isIso_homologyFunctor_map_mor₂_of_isLE _
      (((derivedTensor A X).obj K).map_distinguished _
        (DerivedCategory.TStructure.t.triangleLTGE_distinguished q M)) q
  have : IsIso (Functor.whiskerLeft
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
      (Functor.whiskerRight ((tensoringRight _).map
        ((DerivedCategory.TStructure.t.truncGEπ q).app M))
          (DerivedCategory.homologyFunctor _ q))) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
    (Functor.whiskerRight ((tensoringRight _).map
      ((DerivedCategory.TStructure.t.truncGEπ q).app M)) (DerivedCategory.homologyFunctor _ q)))

/-- The top homology of a derived tensor product with a sheaf: for `M` concentrated in degrees
`≤ q`, `Hᵠ(B[0] ⊗ᴸ M) ≅ B ⊗ Hᵠ(M)`, naturally in the sheaf `B`. -/
noncomputable def singleFunctorTensorRightHomologyIso
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (q : ℤ) [M.IsLE q] :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙ tensorRight M ⋙
        DerivedCategory.homologyFunctor _ q ≅
      tensorRight ((DerivedCategory.homologyFunctor _ q).obj M) :=
  let N := (DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) q).obj M
  let S₀ := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  singleFunctorTensorRightTruncGEHomologyIso M q ≪≫
    Functor.isoWhiskerLeft S₀ (Functor.isoWhiskerRight ((tensoringRight _).mapIso
      (DerivedCategory.truncGEIsoSingleFunctorObjHomology M q ≪≫
        ((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by simp)).symm.app N))
      (DerivedCategory.homologyFunctor _ q)) ≪≫
    Functor.isoWhiskerLeft S₀ (Functor.isoWhiskerRight
      (derivedTensorRightShiftIso (A := A) (X := X) (S₀.obj N) (-q))
      (DerivedCategory.homologyFunctor _ q)) ≪≫
    Functor.isoWhiskerLeft (S₀ ⋙ tensorRight (S₀.obj N))
      ((DerivedCategory.homologyFunctor _ 0).shiftIso (-q) q 0 (by simp)) ≪≫
    singleFunctorTensorRightSingleHomologyZeroIso N

end Etale

end AlgebraicGeometry
