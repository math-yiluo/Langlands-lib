/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FreeCokernelPowTower
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicIntCokernelPowTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.TateTwist.RootsOfUnityTrivialization

/-!
# The Tate module is trivial over a base with a compatible system of roots of unity

Let `g : U ⟶ X` be a weakly étale morphism and suppose that `U` lives over a field `K` containing
a compatible system `(ζₙ)` of primitive `ℓⁿ`-th roots of unity (`ζₙ₊₁ ^ ℓ = ζₙ`), `ℓ` a prime.
Then the pullback along `g` of the Tate module `ℤ_ℓ(1) = lim_n ℤ_ℓ,X ⊗ μ_{ℓⁿ}` is trivial, as a
module over `g^* ℤ_ℓ,X` (`AlgebraicGeometry.ProEtale.upperStarMapModTateModuleIsoUnit`):

* the pullback commutes with the limit, with free modules and with `μ_{ℓⁿ}`
  (`Functor.mapModFreeFunctorIso`, `ProEtale.upperStarRootsOfUnitySheafIso`), so `g^* ℤ_ℓ(1)` is
  the limit of the free modules `g^* ℤ_ℓ,X ⊗ μ_{ℓⁿ,U}`;
* over `U`, `ζₙ` identifies `μ_{ℓⁿ,U}` with `ℤ/ℓⁿ = coker(ℓⁿ : ℤ ⟶ ℤ)`, compatibly with the
  transition maps (`ProEtale.isColimitUnitToRootsOfUnitySheaf`), so the inverse system is
  `n ↦ g^* ℤ_ℓ,X / ℓⁿ` (`AlgebraicGeometry.ProEtale.upperStarTateModuleSystemIso`);
* `g^* ℤ_ℓ,X ≅ ℤ_ℓ,U` is `ℓ`-adically complete (`ProEtale.isLimitCokernelPowTowerCone`), so the
  limit is `g^* ℤ_ℓ,X` (`Mod.isLimitFreeCokernelPowTowerCone`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X U : Scheme.{u}} (g : U ⟶ X) {K : Type u} [Field K] (f : U ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] {ζ : ℕ → K} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))

instance (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- The identification `ℤ/ℓⁿ ≅ μ_{ℓⁿ}`, `a ↦ ζₙ^a`, of sheaves on `U_proét`. -/
noncomputable def cokernelPowIsoRootsOfUnitySheaf (n : ℕ) :
    cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1}))) ≅
      rootsOfUnitySheaf U (ℓ ^ n) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (isColimitUnitToRootsOfUnitySheaf f (hζ n))

@[reassoc (attr := simp)]
lemma cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom (n : ℕ) :
    cokernel.π _ ≫ (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).hom =
      unitToRootsOfUnitySheaf f (hζ n).pow_eq_one :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (isColimitUnitToRootsOfUnitySheaf f (hζ n)) WalkingParallelPair.one

@[reassoc]
lemma unitToRootsOfUnitySheaf_comp_eqToHom {N N' : ℕ} (h : N = N') {z : K} (hz : z ^ N = 1)
    (hz' : z ^ N' = 1) :
    unitToRootsOfUnitySheaf f hz ≫ eqToHom (congrArg (rootsOfUnitySheaf U) h) =
      unitToRootsOfUnitySheaf f hz' := by
  subst h
  simp

lemma upperStar_map_eqToHom_rootsOfUnitySheafIso [WeaklyEtale g] {N N' : ℕ} (h : N = N') :
    (g)^*[Ab.{u + 1}].map (eqToHom (congrArg (rootsOfUnitySheaf X) h)) ≫
        (upperStarRootsOfUnitySheafIso g N').hom =
      (upperStarRootsOfUnitySheafIso g N).hom ≫ eqToHom (congrArg (rootsOfUnitySheaf U) h) := by
  subst h
  simp

variable (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

include hζ' in
/-- The identifications `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` are compatible with the transition maps. -/
@[reassoc]
lemma cokernelPowTransition_comp_cokernelPowIsoRootsOfUnitySheaf_hom (n : ℕ) :
    cokernelPowTransition _ ℓ n ≫ (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).hom =
      (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ (n + 1)).hom ≫
        eqToHom (congrArg (rootsOfUnitySheaf U) (pow_succ' ℓ n)) ≫
          rootsOfUnitySheafPow U (ℓ ^ n) ℓ := by
  rw [← cancel_epi (cokernel.π _), cokernel_π_cokernelPowTransition_assoc,
    cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom,
    cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom_assoc,
    unitToRootsOfUnitySheaf_comp_eqToHom_assoc f (pow_succ' ℓ n) _
      (by rw [← pow_succ']; exact (hζ (n + 1)).pow_eq_one),
    unitToRootsOfUnitySheaf_comp_rootsOfUnitySheafPow f _ _ (hζ' n)]

variable [WeaklyEtale g]

/-- The components `g^*(ℤ_ℓ,X ⊗ μ_{ℓⁿ}) ≅ g^* ℤ_ℓ,X ⊗ ℤ/ℓⁿ` of the trivialization of the Tate
module tower. -/
noncomputable def upperStarTateModuleLevelIso (n : ℕ) :
    ((g)^*[Ab.{u + 1}].mapMod _).obj (tateModuleLevel X ℓ n) ≅
      (Mod.freeFunctor ((g)^*[Ab.{u + 1}].obj
        (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))).obj
        (cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})))) :=
  ((g)^*[Ab.{u + 1}].mapModFreeFunctorIso _).app (rootsOfUnitySheaf X (ℓ ^ n)) ≪≫
    (Mod.freeFunctor _).mapIso (upperStarRootsOfUnitySheafIso g (ℓ ^ n) ≪≫
      (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).symm)

include hζ' in
lemma upperStarTateModuleLevelIso_naturality (n : ℕ) :
    ((g)^*[Ab.{u + 1}].mapMod _).map (tateModuleTransition X ℓ n) ≫
        (upperStarTateModuleLevelIso g f ℓ hζ n).hom =
      (upperStarTateModuleLevelIso g f ℓ hζ (n + 1)).hom ≫
        (Mod.freeFunctor _).map (cokernelPowTransition _ ℓ n) := by
  have h := ((g)^*[Ab.{u + 1}].mapModFreeFunctorIso
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)).hom.naturality
      (eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
        rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
  dsimp only [Functor.comp_map] at h
  simp only [upperStarTateModuleLevelIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [tateModuleTransition, reassoc_of% h, cancel_epi]
  simp only [← Functor.map_comp]
  refine congrArg (Mod.freeFunctor ((g)^*[Ab.{u + 1}].obj
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))).map ?_
  have h2 := upperStar_map_rootsOfUnitySheafPow_comp g (ℓ ^ n) ℓ
  rw [Functor.map_comp, Category.assoc, reassoc_of% h2,
    reassoc_of% upperStar_map_eqToHom_rootsOfUnitySheafIso, Category.assoc,
    cancel_epi, Iso.eq_inv_comp,
    ← cokernelPowTransition_comp_cokernelPowIsoRootsOfUnitySheaf_hom_assoc f ℓ hζ hζ' n,
    Iso.hom_inv_id, Category.comp_id]
  exact pow_succ' ℓ n

/-- The comparison from the pullback of the Tate module tower to the tower
`n ↦ g^* ℤ_ℓ,X / ℓⁿ`. -/
noncomputable def upperStarTateModuleSystemHom :
    tateModuleSystem X ℓ ⋙ (g)^*[Ab.{u + 1}].mapMod _ ⟶
      cokernelPowTower (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})) ℓ ⋙
        Mod.freeFunctor ((g)^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) :=
  NatTrans.ofOpSequence (fun n ↦ (upperStarTateModuleLevelIso g f ℓ hζ n).hom) (fun n ↦ by
    simpa [tateModuleSystem] using upperStarTateModuleLevelIso_naturality g f ℓ hζ hζ' n)

instance : IsIso (upperStarTateModuleSystemHom g f ℓ hζ hζ') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact inferInstanceAs (IsIso (upperStarTateModuleLevelIso g f ℓ hζ n.unop).hom)

/-- **The pullback of the Tate module tower is the tower `n ↦ g^* ℤ_ℓ,X / ℓⁿ`.** -/
noncomputable def upperStarTateModuleSystemIso :
    tateModuleSystem X ℓ ⋙ (g)^*[Ab.{u + 1}].mapMod _ ≅
      cokernelPowTower (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})) ℓ ⋙
        Mod.freeFunctor ((g)^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) :=
  asIso (upperStarTateModuleSystemHom g f ℓ hζ hζ')

/-- **The Tate module is trivial over a base with a compatible system of primitive `ℓⁿ`-th roots
of unity**: `g^* ℤ_ℓ(1) ≅ g^* ℤ_ℓ,X` as `g^* ℤ_ℓ,X`-modules. -/
noncomputable def upperStarMapModTateModuleIsoUnit :
    ((g)^*[Ab.{u + 1}].mapMod _).obj (tateModule X ℓ) ≅ 𝟙_ _ :=
  preservesLimitIso _ _ ≪≫ HasLimit.isoOfNatIso (upperStarTateModuleSystemIso g f ℓ hζ hζ') ≪≫
    (limit.isLimit _).conePointUniqueUpToIso
      (Mod.isLimitFreeCokernelPowTowerCone ((g)^*[Ab.{u + 1}].obj
        (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) ℓ
        (isLimitCokernelPowTowerConeOfIso
        (B := (g)^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))
        ((upperStarFromPointComp g).app (Profinite.continuousMapRingObj ℤ_[ℓ])).symm
        (isLimitCokernelPowTowerCone ℓ U)))

end AlgebraicGeometry.ProEtale
