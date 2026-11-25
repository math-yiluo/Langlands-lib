/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantTowerLimit
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose

/-!
# Limits of towers of constant sheaves of modules

Let `n ↦ (Mₙ)_X` be a tower of constant pro-étale sheaves of `Λ`-modules
(`AlgebraicGeometry.ProEtale.constantModuleSheafTower`) with `Mₙ ≅ Qₙ` additively for discrete
rings `Qₙ`, compatibly with the transitions.

- `AlgebraicGeometry.ProEtale.constantModuleSheafTowerCompForget₂Iso`: the underlying abelian
  tower is `n ↦ C(-, Qₙ)`;
- `AlgebraicGeometry.ProEtale.isLimitConstantModuleSheafTowerCompForget₂`,
  `AlgebraicGeometry.ProEtale.exists_isLimit_continuousMapAbSheaf_of_iso`: its limit is
  `C(-, lim Qₙ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [Ring Λ] {Qs : ℕ → Type}
  [∀ n, TopologicalSpace (Qs n)] [∀ n, CommRing (Qs n)] [∀ n, IsTopologicalRing (Qs n)]
  [∀ n, DiscreteTopology (Qs n)] (τ : ∀ n, Qs (n + 1) →+* Qs n)
  (M : ℕ → ModuleCat.{u + 1} Λ) (std : ∀ n, M (n + 1) ⟶ M n)
  (e : ∀ n, M n ≃+ ULift.{u + 1} (Qs n))
  (he : ∀ n x, e n (std n x) = ULift.up (τ n (e (n + 1) x).down))

/-- The tower of constant pro-étale sheaves of modules `n ↦ (Mₙ)_X` with transitions `stdₙ`. -/
noncomputable abbrev constantModuleSheafTower :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  Functor.ofOpSequence (X := fun n ↦ (constantSheaf (ProEt.topology X) _).obj (M n))
    fun n ↦ (constantSheaf (ProEt.topology X) _).map (std n)

include he in
/-- **The abelian sheaves underlying a tower of constant sheaves of modules are the sheaves of
continuous maps**: if `Mₙ ≅ Qₙ` additively, compatibly with the transitions, the tower
`n ↦ (Mₙ)_X` of constant pro-étale sheaves of `Λ`-modules has underlying abelian tower
`n ↦ C(-, Qₙ)`. -/
noncomputable def constantModuleSheafTowerCompForget₂Iso :
    constantModuleSheafTower X M std ⋙
        sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      continuousMapAbSheafTower X τ (fun _ ↦ continuous_of_discreteTopology) := by
  have : (ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let ι := constantSheafCompSheafComposeIso (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let φ (n : ℕ) := ι.app (M n) ≪≫
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).mapIso (e n).toAddCommGrpIso ≪≫
    constantSheafIsoContinuousMapRingSheaf X (Qs n)
  let α : constantModuleSheafTower X M std ⋙ sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⟶
      continuousMapAbSheafTower X τ (fun _ ↦ continuous_of_discreteTopology) :=
    NatTrans.ofOpSequence (fun n ↦ (φ n).hom) fun n ↦ by
      rw [Functor.comp_map]
      erw [Functor.ofOpSequence_map_homOfLE_succ, continuousMapAbSheafTower_map_succ]
      have h1 := ι.hom.naturality (std n)
      have h3 : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (std n) ≫
          (e n).toAddCommGrpIso.hom = (e (n + 1)).toAddCommGrpIso.hom ≫ uliftAddHom.{u} (τ n) := by
        ext x
        exact congrArg ULift.down (he n x)
      have h2 := constantSheaf_map_comp_constantSheafIsoContinuousMapRingSheaf_hom X (τ n)
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
/-- `lim (Mₙ)_X ≅ C(-, lim Qₙ)` on underlying abelian sheaves: the cone with point
`C(-, lim Qₙ)` over the abelian tower underlying the constant tower `n ↦ (Mₙ)_X` is a limit
cone (`AlgebraicGeometry.ProEtale.isLimitContinuousMapAbSheafConeTowerLimitRing`). -/
noncomputable def isLimitConstantModuleSheafTowerCompForget₂ :
    IsLimit ((Cone.postcompose (constantModuleSheafTowerCompForget₂Iso X τ M std e he).inv).obj
      (continuousMapAbSheafCone X τ (fun _ ↦ continuous_of_discreteTopology)
        (towerLimitRingπ τ) (continuous_towerLimitRingπ τ) (towerLimitRingπ_comp τ))) :=
  (IsLimit.postcomposeInvEquiv _ _).symm (isLimitContinuousMapAbSheafConeTowerLimitRing τ X)

include he in
/-- A tower of abelian sheaves isomorphic to the abelian tower underlying `n ↦ (Mₙ)_X` has
limit `C(-, lim Qₙ)`. -/
theorem exists_isLimit_continuousMapAbSheaf_of_iso
    {G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (iG : G ≅ constantModuleSheafTower X M std ⋙
      sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :
    ∃ c : Cone G, c.pt = continuousMapAbSheaf X (towerLimitRing τ) ∧ Nonempty (IsLimit c) :=
  ⟨(Cone.postcompose (iG ≪≫ constantModuleSheafTowerCompForget₂Iso X τ M std e he).inv).obj
      (continuousMapAbSheafCone X τ (fun _ ↦ continuous_of_discreteTopology)
        (towerLimitRingπ τ) (continuous_towerLimitRingπ τ) (towerLimitRingπ_comp τ)), rfl,
    ⟨(IsLimit.postcomposeInvEquiv _ _).symm
      (isLimitContinuousMapAbSheafConeTowerLimitRing τ X)⟩⟩

end AlgebraicGeometry.ProEtale
