/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts

/-!
# Towers of pro-étale sheaves with epimorphic transitions have no derived limit terms

Let `T` be a tower of complexes of sheaves of `Λ`-modules on the small pro-étale site whose
transition maps are degreewise epimorphisms. Then the limit `lim Tₙ`, computed degreewise, is
the derived limit `R lim Tₙ` in the derived category
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_mapCone_Q_of_epi`, blueprint
`proposition-milnor-sequence--3`, Stacks 0947, 091J): in each degree,
`0 ⟶ lim Tₙ ⟶ ∏ Tₙ ──1 - t──▶ ∏ Tₙ ⟶ 0` is exact, the surjectivity of `1 - t` being checked on
sections over the weakly contractible objects, which cover the site and over which epimorphisms
of sheaves are surjective; and countable products are exact on the pro-étale site (repleteness).

The general statement (`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi_one_sub`) holds in any
abelian category with exact countable products and K-injective resolutions, for towers of
complexes on which `1 - t` is degreewise an epimorphism. Combined with
`CategoryTheory.Pretriangulated.IsHomotopyLimit.map`, derived pushforwards then commute with the
limit (`AlgebraicGeometry.ProEtale.isHomotopyLimit_rightDerivedLowerStar_mapCone_Q_of_epi`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C]

/-- The image in the derived category of a limit cone `c` of a tower `T` of complexes is a
homotopy limit cone, provided that, in each degree, `1 - t` is an epimorphism on a product of the
tower, where `t` has components `∏ Tₙ ⟶ Tₙ₊₁ ⟶ Tₙ`: in each degree
`0 ⟶ lim Tₙ ⟶ ∏ Tₙ ──1 - t──▶ ∏ Tₙ ⟶ 0` is exact, and the triangle attached to this short exact
sequence of complexes is the Milnor triangle. -/
theorem isHomotopyLimit_mapCone_Q_of_epi_one_sub {T : ℕᵒᵖ ⥤ CochainComplex C ℤ}
    (hT : ∀ (i : ℤ) {P : Fan fun n : ℕ ↦ (T.obj (op n)).X i} (_ : IsLimit P) (t : P.pt ⟶ P.pt),
      (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ (T.map (homOfLE n.le_succ).op).f i) →
        Epi (𝟙 P.pt - t))
    {c : Cone T} (hc : IsLimit c) :
    IsHomotopyLimit (Q.mapCone c) := by
  let K (n : ℕ) : CochainComplex C ℤ := T.obj (op n)
  let P : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hP : IsLimit P := productIsProduct K
  let t : P.pt ⟶ P.pt := Pi.lift fun n ↦ Pi.π K (n + 1) ≫ T.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ P.proj n = P.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  let S := ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hP t ht hc
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
      rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      exact hT i (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hP) (t.f i)
        (fun n ↦ (HomologicalComplex.comp_f _ _ i).symm.trans
          ((congrArg (fun φ ↦ φ.f i) (ht n)).trans (HomologicalComplex.comp_f _ _ i)))
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  let hQ := isLimitFanQ K
  refine ⟨_, hQ, triangleOfSESδ hS, isomorphic_distinguished _ (triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hQ _ _ fun n ↦ ?_
    simp only [Functor.mapCone_pt, Functor.comp_obj, Fan.mk_pt, Functor.mapCone_π_app,
      Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, fan_mk_proj, triangleOfSES_mor₁,
      Category.id_comp]
    exact (Fan.IsLimit.fac hQ (fun n ↦ Q.map (c.π.app (op n))) n).trans (congrArg Q.map
      (Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n).symm |>.trans (Q.map_comp _ _))
  · refine Fan.IsLimit.hom_ext hQ _ _ fun n ↦ ?_
    simp only [Functor.mapCone_pt, Functor.comp_obj, Fan.mk_pt, Functor.mapCone_π_app,
      towerShift, fan_mk_proj, Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.comp_map,
      triangleOfSES, Triangle.mk_mor₂, ← Functor.map_comp, Iso.refl_hom, Category.comp_id,
      Preadditive.sub_comp, Functor.map_sub, CategoryTheory.Functor.map_id,
      Preadditive.comp_sub, Category.id_comp, sub_right_inj, S, P]
    exact (Fan.IsLimit.fac hQ _ n).trans (congrArg Q.map (ht n).symm)
  · simp [triangleOfSES]

end DerivedCategory

namespace AlgebraicGeometry.ProEtale

variable {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- **Towers with epimorphic transitions have no derived limit terms** on the pro-étale site
(blueprint `proposition-milnor-sequence--3`, Stacks 0947, 091J): for a tower of complexes of sheaves
of `Λ`-modules on `S_proét` with degreewise epimorphic transitions, the degreewise limit is the
derived limit, i.e. its image in the derived category is a homotopy limit cone. -/
theorem isHomotopyLimit_mapCone_Q_of_epi
    {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ)) ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) :
    IsHomotopyLimit (DerivedCategory.Q.mapCone c) :=
  DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi_one_sub (fun i _ hP t ht ↦
    GrothendieckTopology.epi_one_sub_of_forall_exists.{u + 1, u}
      (fun W : S.ProEt ↦ IsAffine W.left ∧
        (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1} W)
      (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V) (fun _ hW ↦ hW.2)
      (F := T ⋙ HomologicalComplex.eval _ _ i) hP t ht (fun n ↦ hT n i)) hc

end AlgebraicGeometry.ProEtale
