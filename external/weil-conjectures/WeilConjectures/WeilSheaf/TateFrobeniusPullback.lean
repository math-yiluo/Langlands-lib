/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusTrivialization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# The trivialization of the Tate module under pullback: ingredients

Towards the naturality of the trivialization `g^* ℤ_ℓ(1) ≅ g^* ℤ_ℓ,X` of the Tate module
(`AlgebraicGeometry.ProEtale.upperStarMapModTateModuleIsoUnit`) under a further weakly étale
pullback `g₁ : U' ⟶ U`, this file provides:

* the monoidality of the composition isomorphisms of pullbacks of abelian pro-étale sheaves
  (`AlgebraicGeometry.ProEtale.isMonoidal_upperStarComp_ab_hom`), as for sheaves of
  `ℚ̄_ℓ`-modules, and the factorization isomorphism `g^* ⋙ g₁^* ≅ g'^*` along `g₁ ≫ g = g'`
  (`AlgebraicGeometry.ProEtale.upperStarFactorIso`);
* the compatibility of the level identifications `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` with the pullback along a
  morphism `g₁` over the same field
  (`AlgebraicGeometry.ProEtale.upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_of_comp_eq`);
* the projection formula of the trivialization: its composite with the `n`-th leg of the tower
  of free modules `n ↦ g^* ℤ_ℓ,X ⊗ ℤ/ℓⁿ` is the `n`-th level identification
  (`AlgebraicGeometry.ProEtale.upperStarMapModTateModuleIsoUnit_hom_comp_π`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### Monoidality of the composition isomorphisms of pullbacks of abelian sheaves -/

section Monoidal

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `h₂^* ⋙ h₁^* ≅ (h₁ ≫ h₂)^*` of pullbacks of abelian sheaves is
monoidal: it is the conjugate of the monoidal composition isomorphism of pushforwards. -/
instance isMonoidal_upperStarComp_ab_inv :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} h₁ h₂).inv := by
  have h₁' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (h₁ ≫ h₂))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} h₂).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} h₁))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} h₁ h₂).inv

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks of abelian sheaves is
monoidal. -/
instance isMonoidal_upperStarComp_ab_hom :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} h₁ h₂).hom :=
  have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} h₁ h₂).symm.hom :=
    isMonoidal_upperStarComp_ab_inv h₁ h₂
  inferInstanceAs (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} h₁ h₂).symm.inv)

/-- The isomorphism `g^* ≅ g'^*` of pullbacks of abelian sheaves along equal morphisms is
monoidal. -/
instance isMonoidal_upperStarCongr_ab_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    NatTrans.IsMonoidal (upperStarCongr Ab.{u + 1} h).hom := by
  subst h
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))

variable {U' U X : Scheme.{u}} (g₁ : U' ⟶ U) (g : U ⟶ X) {g' : U' ⟶ X} (h : g₁ ≫ g = g')

/-- The factorization isomorphism `g^* ⋙ g₁^* ≅ g'^*` of pullbacks of abelian sheaves along
`g₁ ≫ g = g'`. -/
noncomputable def upperStarFactorIso :
    (g)^*[Ab.{u + 1}] ⋙ (g₁)^*[Ab.{u + 1}] ≅ (g')^*[Ab.{u + 1}] :=
  (upperStarComp Ab.{u + 1} g₁ g).symm ≪≫ upperStarCongr Ab.{u + 1} h

/-- The factorization isomorphism of pullbacks is monoidal. -/
instance isMonoidal_upperStarFactorIso_hom :
    NatTrans.IsMonoidal (upperStarFactorIso g₁ g h).hom := by
  dsimp only [upperStarFactorIso]
  rw [Iso.trans_hom, Iso.symm_hom]
  infer_instance

end Monoidal

/-! ### The level identifications under pullback over the same field -/

section SameField

variable {K : Type u} [Field K] {U' U : Scheme.{u}} (g₁ : U' ⟶ U) (f : U ⟶ Spec (.of K))
  (f' : U' ⟶ Spec (.of K)) (hf : g₁ ≫ f = f') (ℓ : ℕ) [Fact ℓ.Prime] {ζ : ℕ → K}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))

include hf in
/-- The identifications `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` by the roots `ζₙ` are compatible with the pullback along
a morphism `g₁ : U' ⟶ U` over `K`: `g₁^*(ℤ/ℓⁿ ≅ μ_{ℓⁿ})` followed by `g₁^* μ_{ℓⁿ} ⟶ μ_{ℓⁿ}` is
`g₁^*(ℤ/ℓⁿ) ≅ ℤ/ℓⁿ` followed by `ℤ/ℓⁿ ≅ μ_{ℓⁿ}`. -/
lemma upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_of_comp_eq (n : ℕ) :
    (g₁)^*[Ab.{u + 1}].map (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).hom ≫
        upperStarRootsOfUnitySheafHom g₁ (ℓ ^ n) =
      (upperStarCokernelPowIso g₁ (ℓ ^ n)).hom ≫
        (cokernelPowIsoRootsOfUnitySheaf f' ℓ hζ n).hom := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  refine Cofork.IsColimit.hom_ext (isColimitCoforkMapOfIsColimit' (g₁)^*[Ab.{u + 1}]
    (cokernel.condition (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1}))))
    (cokernelIsCokernel _)) ?_
  try simp only [Cofork.π_ofπ]
  rw [← Functor.map_comp_assoc, cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom,
    upperStar_map_cokernel_π_comp_upperStarCokernelPowIso_hom_assoc,
    cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom, upperStarRootsOfUnitySheafHom,
    ← Functor.map_comp_assoc,
    reassoc_of% (upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison g₁ f f'
      hf (hζ n).pow_eq_one),
    Iso.hom_inv_id, Category.comp_id]

end SameField

/-! ### The projection formula of the trivialization -/

section Projection

variable {X U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] {K : Type u} [Field K]
  (f : U ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] {ζ : ℕ → K}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- **The projection formula of the trivialization**: the trivialization `g^* ℤ_ℓ(1) ≅ g^* ℤ_ℓ,X`
followed by the `n`-th leg `g^* ℤ_ℓ,X ⟶ g^* ℤ_ℓ,X ⊗ ℤ/ℓⁿ` of the tower of free modules is the
`n`-th projection of the Tate module followed by the `n`-th level identification
`g^*(ℤ_ℓ,X ⊗ μ_{ℓⁿ}) ≅ g^* ℤ_ℓ,X ⊗ ℤ/ℓⁿ`. -/
lemma upperStarMapModTateModuleIsoUnit_hom_comp_π (n : ℕ) :
    (upperStarMapModTateModuleIsoUnit g f ℓ hζ hζ').hom ≫
        (Mod.freeCokernelPowTowerCone ((g)^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) ℓ).π.app (op n) =
      ((g)^*[Ab.{u + 1}].mapMod _).map (limit.π (tateModuleSystem X ℓ) (op n)) ≫
        (upperStarTateModuleLevelIso g f ℓ hζ n).hom := by
  simp only [upperStarMapModTateModuleIsoUnit, Iso.trans_hom, Category.assoc,
    IsLimit.conePointUniqueUpToIso_hom_comp, limit.cone_π, HasLimit.isoOfNatIso_hom_π,
    preservesLimitIso_hom_π_assoc, upperStarTateModuleSystemIso,
    asIso_hom]
  try rfl

end Projection

end AlgebraicGeometry.ProEtale
