/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeFrameSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTowerExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntLatticeLisse

/-!
# The lattice of an integral cocycle

Let `f : V ⟶ X` be a single-morphism pro-étale cover and `γ` a continuous integral cocycle on
`V ×_X V` (`AlgebraicGeometry.IsIntegralCocycle`). The limit, in `ℤ_ℓ,X`-modules, of the
transport `ν^* Gₖ` of the étale tower of `γ` is the *lattice* of `γ`
(`AlgebraicGeometry.integralCocycleLattice`). Its pullback to `V` is free:
`f^* M ≅ ℤ_ℓ,V^N` (`AlgebraicGeometry.upperStarIntegralCocycleLatticeIso`), the tower being
constant over `V` (`AlgebraicGeometry.frameTowerIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open Scheme ProEtale

variable {l : ℕ} [Fact l.Prime] {X V : Scheme.{u}} {f : V ⟶ X} [WeaklyEtale f] [Surjective f]
  [QuasiCompact f] [QuasiSeparated f] {N : ℕ} {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

variable (l) in
/-- The `ℓ`-adic tower of an integral cocycle is killed levelwise by `ℓᵏ`. -/
lemma zsmul_id_integralCocycleTower_obj (hγ : IsIntegralCocycle f γ) (k : ℕ) :
    ((l ^ k : ℕ) : ℤ) • 𝟙 ((integralCocycleTower γ).obj (op k)) = 0 :=
  zsmul_id_eq_zero_of_adicTowerStructure X l (integralCocycleTowerAdicTowerStructure hγ) k

variable (l) in
/-- **The lattice of an integral cocycle**: the limit, in `ℤ_ℓ,X`-modules, of the transported
étale tower of twisted sections. -/
noncomputable abbrev integralCocycleLattice (hγ : IsIntegralCocycle f γ) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) :=
  limit (comparisonPadicIntModTower X l (integralCocycleTower γ)
    (zsmul_id_integralCocycleTower_obj l hγ))

/-- The underlying abelian sheaf of the lattice is the limit of the pro-étale tower. -/
noncomputable def integralCocycleLatticeXIso (hγ : IsIntegralCocycle f γ) :
    (integralCocycleLattice l hγ).X ≅
      limit (proEtIntegralCocycleTower γ ⋙
        sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab)) :=
  preservesLimitIso (Mod.forget _) _ ≪≫
    HasLimit.isoOfNatIso ((Functor.associator (integralCocycleTower γ)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X)
      (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab))).symm ≪≫
      Functor.isoWhiskerRight (comparisonUpperStarIntegralCocycleTowerIso hγ) _ :
        comparisonPadicIntModTower X l (integralCocycleTower γ)
          (zsmul_id_integralCocycleTower_obj l hγ) ⋙ Mod.forget _ ≅ _)

omit [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The restriction along the localization functor preserves limits, which are computed
sectionwise. -/
instance (J : Type) [SmallCategory J] :
    PreservesLimitsOfShape J (localizationRestriction Ab.{u + 1} f (inferInstanceAs
      (WeaklyEtale f))) := by
  have : PreservesLimitsOfShape J
      (localizationRestriction Ab.{u + 1} f (inferInstanceAs (WeaklyEtale f)) ⋙
        sheafToPresheaf _ _) :=
    preservesLimitsOfShape_of_natIso (F := sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (MorphismProperty.Over.map ⊤
        (inferInstanceAs (WeaklyEtale f))).op) (Iso.refl _)
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- The restriction to `V` of the lattice is free, as an abelian sheaf. -/
noncomputable def localizationRestrictionIntegralCocycleLatticeXIso
    (hγ : IsIntegralCocycle f γ) :
    (localizationRestriction Ab.{u + 1} f inferInstance).obj (integralCocycleLattice l hγ).X ≅
      ⨁ fun _ : Fin N ↦ padicIntAbSheaf V l :=
  (localizationRestriction Ab.{u + 1} f inferInstance).mapIso
      (integralCocycleLatticeXIso hγ) ≪≫
    preservesLimitIso (localizationRestriction Ab.{u + 1} f inferInstance) _ ≪≫
    frameLimitIso hγ

/-- **The coordinates of the restriction of the lattice**: modulo `ℓᵏ`, the `j`-th coordinate is
the `j`-th coordinate of the twisted sections of the tower at level `k`. -/
lemma localizationRestrictionIntegralCocycleLatticeXIso_hom_π (hγ : IsIntegralCocycle f γ)
    (k : ℕ) (j : Fin N) :
    (localizationRestrictionIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j ≫
        padicIntAbSheafToZModPow V l k =
      (localizationRestriction Ab.{u + 1} f inferInstance).map
        ((integralCocycleLatticeXIso hγ).hom ≫ limit.π _ (op k)) ≫ frameEvalHom k j := by
  have h₁ : (limitZmodPowAbSheafDiagramPowIso V l N).hom ≫ biproduct.π _ j ≫
      padicIntAbSheafToZModPow V l k = limit.π _ (op k) ≫ biproduct.π _ j := by
    have := (limit.isLimit _).conePointUniqueUpToIso_hom_comp
      ((isLimitPadicIntAbSheafCone V l).biproductPow (Fin N)) (op k)
    rw [← biproduct.map_π (fun _ ↦ padicIntAbSheafToZModPow V l k) j, ← Category.assoc]
    exact this ▸ rfl
  simp only [localizationRestrictionIntegralCocycleLatticeXIso, frameLimitIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, h₁, Functor.map_comp]
  have h₂ : (frameTowerIso hγ).hom.app (op k) ≫ biproduct.π _ j = frameEvalHom k j :=
    frameTowerObjIso_hom_π hγ k j
  erw [limMap_π_assoc, h₂, preservesLimitIso_hom_π_assoc]

/-- **The pullback of the lattice to `V` is free**, as an abelian sheaf. -/
noncomputable def upperStarIntegralCocycleLatticeXIso (hγ : IsIntegralCocycle f γ) :
    (f)^*[Ab.{u + 1}].obj (integralCocycleLattice l hγ).X ≅
      ⨁ fun _ : Fin N ↦ padicIntAbSheaf V l :=
  (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).app _ ≪≫
    localizationRestrictionIntegralCocycleLatticeXIso hγ

/-- **The pullback of the lattice to `V` is free**, as a `ℤ_ℓ,V`-module. -/
noncomputable def upperStarIntegralCocycleLatticeIso (hγ : IsIntegralCocycle f γ) :
    (padicIntModUpperStar l f).obj (integralCocycleLattice l hγ) ≅
      ⨁ fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l) :=
  modIsoBiproductRegularOfIso l _ (upperStarIntegralCocycleLatticeXIso hγ)

end AlgebraicGeometry
