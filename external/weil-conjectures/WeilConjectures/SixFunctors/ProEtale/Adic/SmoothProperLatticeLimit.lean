/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarMittagLeffler

/-!
# Pro-étale higher direct images of limits of `ℓ`-adic towers

Let `K` be a field, `Y` of finite type over `K`, `f : X ⟶ Y` smooth and proper and `(Gₙ)` an
`ℓ`-adic tower of étale sheaves of `Λ`-modules on `X` as in
`WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLisse`. We identify the pro-étale
higher direct image of the limit, `Rʲf_*^{proét} (lim ν^* Gₙ)`, with the limit
`lim ν^* Rʲf_*^{ét} Gₙ`
(`AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarLimitIso`). For `Λ = ULift ℤ_ℓ` and `Y`
connected, its underlying abelian sheaf is that of the `ℤ_ℓ,Y`-module `lim Mₙ`, `Mₙ` being the
transport of `Rʲf_* Gₙ`, whose rationalisation is lisse
(`AlgebraicGeometry.ProEtale.exists_iso_limit_comparisonPadicIntModTower_isAdicLisseSheaf`).

The ingredients are:

* the comparison `Rf_*^{proét} ν^* G[0] ≅ ν^* Rf_*^{ét} G[0]` as a natural isomorphism in `G`
  (`AlgebraicGeometry.ProEtale.singleRightDerivedLowerStarComparisonUpperStarIso`);
* the Milnor sequence and the Mittag-Leffler property of the tower `(Rⁱf_* ν^* Gₙ)ₙ`
  (`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper`),
  together with the vanishing of `R⁻¹f_*` for `j = 0`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The comparison `Rf_*^{proét} ν^* G[0] ≅ ν^* Rf_*^{ét} G[0]`, natural in the étale sheaf `G`
(compare `AlgebraicGeometry.ProEtale.rightDerivedLowerStarSingleComparisonUpperStarIso`). -/
noncomputable def singleRightDerivedLowerStarComparisonUpperStarIso :
    ν^*(X)[A] ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R(ProEtale.lowerStar A f) ≅
      DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar A f) ⋙ D(ν^*(Y)[A]) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ν^*(X)[A].mapDerivedCategorySingleFunctor 0).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      ((rightDerivedLowerStarComparisonIso' f A).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Etale.lowerStar A f).rightDerivedFunctorPlusCompatibility _ ≪≫
        Functor.associator _ _ _)

/-- The comparison `Rᵠf_*^{proét} ν^* G ≅ ν^* Rᵠf_*^{ét} G`, natural in the étale sheaf `G`
(compare `AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarSingleComparisonUpperStarIso`).
-/
noncomputable def homologyRightDerivedLowerStarComparisonUpperStarIso (q : ℤ) :
    ν^*(X)[A] ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R(ProEtale.lowerStar A f) ⋙
        DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar A f) ⋙
        DerivedCategory.homologyFunctor _ q ⋙ ν^*(Y)[A] :=
  (Functor.isoWhiskerRight (singleRightDerivedLowerStarComparisonUpperStarIso A f)
      (DerivedCategory.homologyFunctor _ q)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar A f))
      (ν^*(Y)[A].mapDerivedCategoryHomologyFunctorIso q).symm

end Comparison

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **`Rʲf_*` commutes with the limit of an `ℓ`-adic tower along a smooth proper morphism**, in
every degree `j ≥ 0`: the case `j ≥ 1` is
`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper`, and
for `j = 0` the Milnor sequence applies with `R⁻¹f_* = 0`. -/
theorem isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper'
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (I : ℕ → Ideal Λ)
    [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE n.le_succ).op))
    {c : Cone (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ])} (hc : IsLimit c) (j : ℕ)
    {d : Cone (((((G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
      HomologicalComplex.single _ (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q) ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)) ⋙
          DerivedCategory.homologyFunctor _ (j : ℤ))}
    (hd : IsLimit d) :
    IsIso (hd.lift ((DerivedCategory.homologyFunctor _ (j : ℤ)).mapCone
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCone (DerivedCategory.Q.mapCone
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapCone c))))) := by
  cases j with
  | succ i =>
    exact isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper aY f G I F eG hG hc i
      _ (by push_cast; rfl) hd
  | zero =>
    let S := HomologicalComplex.single (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
      (ComplexShape.up ℤ) 0
    have : (ν^*(X)[ModuleCat.{u + 1} Λ]).IsLeftAdjoint :=
      (comparisonAdjunction _ X).isLeftAdjoint
    have (n : ℕ) : Epi ((G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]).map (homOfLE n.le_succ).op) :=
      have := hG n
      (ν^*(X)[ModuleCat.{u + 1} Λ]).map_epi (G.map (homOfLE n.le_succ).op)
    refine isIso_lift_homology_rightDerivedLowerStar_of_forall_mittagLeffler f
      (T := (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙ S) (c := S.mapCone c)
      (fun n i ↦ epi_single_map_f _ 0 i) (isLimitOfPreserves S hc) (-1) _ (by simp)
      (fun W _ _ n ↦ ⟨n, le_rfl, fun k hk ↦ ?_⟩) hd
    rintro _ ⟨x, rfl⟩
    have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)
      ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj (G.obj (op n)))
    have hz := (sheafToPresheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).map_isZero
      (DerivedCategory.isZero_of_isGE ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj (G.obj (op n))))) 0 (-1) (by omega))
    obtain rfl : x = 0 := (ModuleCat.isZero_iff_subsingleton.1 (hz.obj (op W))).elim x 0
    rw [map_zero]
    exact zero_mem _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **`Rʲf_*^{proét} (lim ν^* Gₙ) ≅ lim ν^* Rʲf_*^{ét} Gₙ`** for a tower `(Gₙ)` of finite locally
constant étale sheaves with epimorphic transitions along a smooth proper morphism, combining
`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper'`
with the comparison
`AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarComparisonUpperStarIso`. -/
noncomputable def homologyRightDerivedLowerStarLimitIso
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (I : ℕ → Ideal Λ)
    [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE n.le_succ).op)) (j : ℕ) :
    (DerivedCategory.homologyFunctor _ (j : ℤ)).obj
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (limit (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ])))) ≅
      limit (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ DerivedCategory.homologyFunctor _ (j : ℤ) ⋙
          ν^*(Y)[ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper' aY f G I F eG hG
    (limit.isLimit _) j (limit.isLimit _)
  asIso ((limit.isLimit _).lift ((DerivedCategory.homologyFunctor _ (j : ℤ)).mapCone
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCone (DerivedCategory.Q.mapCone
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapCone
          (limit.cone (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]))))))) ≪≫
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft G
    (homologyRightDerivedLowerStarComparisonUpperStarIso (ModuleCat.{u + 1} Λ) f (j : ℤ)))

variable (l : ℕ) [Fact l.Prime]

/-- **The pro-étale higher direct image of the limit of an `ℓ`-adic tower is the lattice
`lim Mₙ`, and is lisse after rationalisation.** In the situation of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar`,
the underlying abelian sheaf of `Rʲf_*^{proét} (lim ν^* Gₙ)` is that of the `ℤ_ℓ,Y`-module
`lim Mₙ`, where `Mₙ` is the transport of `Rʲf_*^{ét} Gₙ`, and `ℚ̄_ℓ ⊗ lim Mₙ` is lisse. -/
theorem exists_iso_limit_comparisonPadicIntModTower_isAdicLisseSheaf
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [ConnectedSpace Y] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    Nonempty ((sheafCompose (ProEt.topology Y)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab.{u + 1})).obj
        ((DerivedCategory.homologyFunctor _ (j : ℤ)).obj
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (limit (G ⋙ ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])]))))) ≅
      (limit (comparisonPadicIntModTower Y l
        (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          R(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙
            DerivedCategory.homologyFunctor _ j)
        (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j))).X) ∧
    IsAdicLisseSheaf ((adicSheafExtendScalars Y l).obj (limit (comparisonPadicIntModTower Y l
      (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙
          DerivedCategory.homologyFunctor _ j)
      (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j)))) :=
  ⟨⟨(sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab.{u + 1})).mapIso
      (homologyRightDerivedLowerStarLimitIso aY f G I F eG (fun n ↦ A.epi_map n.le_succ) j) ≪≫
    preservesLimitIso (sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab.{u + 1})) _ ≪≫
    (limit.isLimit (comparisonPadicIntModTower Y l
        (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          R(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙
            DerivedCategory.homologyFunctor _ j)
        (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j) ⋙
          Mod.forget _)).conePointUniqueUpToIso
      (isLimitOfPreserves (Mod.forget _) (limit.isLimit _))⟩,
    isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar l aY f G A I F
      eG j⟩

end AlgebraicGeometry.ProEtale
