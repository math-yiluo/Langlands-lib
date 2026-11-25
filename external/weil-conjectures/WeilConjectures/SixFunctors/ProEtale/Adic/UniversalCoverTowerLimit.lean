/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapAdd
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverConstant
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose

/-!
# Limits of towers of finite locally constant sheaves on the universal cover

- `AlgebraicGeometry.ProEtale.constantSheafTowerCompForget₂IsoAdd`: the abelian tower underlying
  a tower of constant pro-étale sheaves of modules `n ↦ (Mₙ)_X` is `n ↦ C(-, Qₙ)`, for discrete
  groups `Qₙ ≅ Mₙ` compatible with the transitions; hence its limit is `C(-, lim Qₙ)`
  (`AlgebraicGeometry.ProEtale.exists_isLimit_continuousMapAddSheaf_of_iso`).
- `AlgebraicGeometry.Scheme.UniversalCovers.exists_isLimit_towerComparisonUpperStar`: for a tower
  `H` of finite locally constant étale sheaves on `Y`, the abelian tower underlying `p^* ν^* Hₙ`
  on the universal cover `Ỹ_y` has limit `C(-, lim_n (Hₙ)_y)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Bridge

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [Ring Λ] {Qs : ℕ → Type}
  [∀ n, TopologicalSpace (Qs n)] [∀ n, AddCommGroup (Qs n)] [∀ n, IsTopologicalAddGroup (Qs n)]
  [∀ n, DiscreteTopology (Qs n)] (τ : ∀ n, Qs (n + 1) →+ Qs n)
  (M : ℕᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
  (e : ∀ n, M.obj (op n) ≃+ ULift.{u + 1} (Qs n))
  (he : ∀ n x, e n (M.map (homOfLE (n.le_add_right 1)).op x) = ULift.up (τ n (e (n + 1) x).down))

include he in
/-- **The abelian tower underlying a tower of constant sheaves of modules is the tower of
continuous maps**, for discrete groups `Qₙ ≅ Mₙ` compatible with the transitions. -/
noncomputable def constantSheafTowerCompForget₂IsoAdd :
    M ⋙ constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
        sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      continuousMapAddSheafTower X τ (fun _ ↦ continuous_of_discreteTopology) := by
  have : (ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let ι := constantSheafCompSheafComposeIso (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let φ (n : ℕ) := ι.app (M.obj (op n)) ≪≫
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).mapIso (e n).toAddCommGrpIso ≪≫
    constantSheafIsoContinuousMapAddSheaf X (Qs n)
  let α : M ⋙ constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙ sheafCompose
      (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⟶
      continuousMapAddSheafTower X τ (fun _ ↦ continuous_of_discreteTopology) :=
    NatTrans.ofOpSequence (fun n ↦ (φ n).hom) fun n ↦ by
      rw [Functor.comp_map, Functor.comp_map]
      erw [continuousMapAddSheafTower_map_succ]
      have h1 := ι.hom.naturality (M.map (homOfLE (n.le_add_right 1)).op)
      have h3 : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (M.map (homOfLE (n.le_add_right 1)).op) ≫ (e n).toAddCommGrpIso.hom =
          (e (n + 1)).toAddCommGrpIso.hom ≫ uliftAddMonoidHom.{u} (τ n) := by
        ext x
        exact congrArg ULift.down (he n x)
      have h2 := constantSheaf_map_comp_constantSheafIsoContinuousMapAddSheaf_hom X (τ n)
      simp only [φ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      erw [reassoc_of% h1]
      erw [← Functor.map_comp_assoc, h3, Functor.map_comp_assoc, h2]
      simp only [Category.assoc]
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    rw [NatTrans.ofOpSequence_app]
    infer_instance
  have := NatIso.isIso_of_isIso_app α
  exact asIso α

include he in
/-- A tower of abelian sheaves isomorphic to the abelian tower underlying `n ↦ (Mₙ)_X` has
limit `C(-, lim Qₙ)`. -/
theorem exists_isLimit_continuousMapAddSheaf_of_iso
    {G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (iG : G ≅ M ⋙ constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
      sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :
    ∃ c : Cone G, c.pt = continuousMapAddSheaf X (towerLimitAddSubgroup τ) ∧
      Nonempty (IsLimit c) :=
  ⟨(Cone.postcompose (iG ≪≫ constantSheafTowerCompForget₂IsoAdd X τ M e he).inv).obj
      (continuousMapAddSheafCone X τ (fun _ ↦ continuous_of_discreteTopology)), rfl,
    ⟨(IsLimit.postcomposeInvEquiv _ _).symm (isLimitContinuousMapAddSheafCone X τ _)⟩⟩

end Bridge

/-- **The limit of a tower of finite locally constant sheaves on the universal cover.** Let `H` be
a tower of finite locally constant étale sheaves of `Λ`-modules on `Y` (`Λ` finite) and
`p : Ỹ_y ⟶ Y` the universal profinite étale cover. If the stalks `(Hₙ)_y` are identified with
discrete groups `Qₙ`, compatibly with the transitions, then the abelian tower underlying
`p^* ν^* Hₙ` has limit `C(-, lim Qₙ)`: the tower is constant with values the stalks on `Ỹ_y`
(`AlgebraicGeometry.Scheme.UniversalCovers.towerComparisonUpperStarIsoConstantSheaf`). -/
theorem _root_.AlgebraicGeometry.Scheme.UniversalCovers.exists_isLimit_towerComparisonUpperStar
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsFiniteLocallyConstantSheaf (H.obj (op n)))
    {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, AddCommGroup (Qs n)]
    [∀ n, IsTopologicalAddGroup (Qs n)] [∀ n, DiscreteTopology (Qs n)]
    (τ : ∀ n, Qs (n + 1) →+ Qs n)
    (e : ∀ n, ((pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (H.obj (op n)) ≃+
      ULift.{u + 1} (Qs n))
    (he : ∀ n x, e n ((pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber.map
      (H.map (homOfLE (n.le_add_right 1)).op) x) = ULift.up (τ n (e (n + 1) x).down)) :
    ∃ c : Cone (H ⋙ comparisonUpperStar _ Y ⋙ ProEtale.upperStar _ (U.proj y) ⋙
        sheafCompose (ProEt.topology (U.cover y))
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})),
      c.pt = continuousMapAddSheaf (U.cover y) (towerLimitAddSubgroup τ) ∧
        Nonempty (IsLimit c) :=
  exists_isLimit_continuousMapAddSheaf_of_iso (U.cover y) τ
    (H ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber) e he
    (Functor.isoWhiskerRight (U.towerComparisonUpperStarIsoConstantSheaf y Λ H hH)
      (sheafCompose (ProEt.topology (U.cover y))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))

end AlgebraicGeometry.ProEtale
