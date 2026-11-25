/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusTower

/-!
# The trivialization of the Tate module along the semilinear structure

Let `k` be a finite field with `q` elements, `k̄` its algebraic closure, `γ` its geometric
Frobenius, `σ = Spec γ`, and `g : U ⟶ X` a weakly étale morphism with `U` over `k̄` through `f`.
The Tate module `ℤ_ℓ(1)` pulled back along `g` is trivialized by a compatible system `ζₙ` of
primitive
`ℓⁿ`-th roots of unity of `k̄` (`AlgebraicGeometry.ProEtale.upperStarMapModTateModuleIsoUnit`).
The trivialization depends on the `k̄`-structure `f` of `U`: along the semilinear structure
`f ≫ σ`, the level identifications `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` are multiplied by `cₙ = χ_ℓ(γ) mod ℓⁿ`
(`AlgebraicGeometry.ProEtale.cokernelPowIsoRootsOfUnitySheaf_comp_specGeometricFrobenius_hom`),
hence their inverses by `q`, since `cₙ q = 1`
(`AlgebraicGeometry.ProEtale.cokernelPowIsoRootsOfUnitySheaf_comp_specGeometricFrobenius_inv`).
Hence **the trivialization along `f ≫ σ` is `q` times the trivialization along `f`**
(`AlgebraicGeometry.ProEtale.upperStarMapModTateModuleIsoUnit_comp_specGeometricFrobenius_hom`):
the geometric Frobenius acts on the trivialized Tate module through the integer `q`, the inverse
of the cyclotomic character `χ_ℓ(γ) = q⁻¹`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The free module functor on sheaves on `X_proét` is additive. -/
instance freeFunctor_additive {X : Scheme.{u}} (R : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] : (Mod.freeFunctor R).Additive where
  map_add := by
    intro A B f g
    apply Mod.hom_ext
    exact MonoidalPreadditive.whiskerLeft_add f g

section FiniteField

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- `cₙ q ≡ 1 mod ℓⁿ`, as integers. -/
lemma pow_dvd_geometricFrobeniusModularCharacterVal_mul_natCard_sub_one (n : ℕ) :
    ((ℓ ^ n : ℕ) : ℤ) ∣ geometricFrobeniusModularCharacterVal k ℓ n * (Nat.card k : ℤ) - 1 := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, Int.cast_one,
    geometricFrobeniusModularCharacterVal, Int.cast_natCast, Int.cast_natCast,
    ZMod.natCast_zmod_val, geometricFrobeniusModularCharacter_mul_natCard, sub_self]

variable {U : Scheme.{u}} (f : U ⟶ Spec (.of (AlgebraicClosure k)))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))

/-- Along the semilinear structure `f ≫ σ`, the identification `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` is `cₙ` times the
one along `f`. -/
lemma cokernelPowIsoRootsOfUnitySheaf_comp_specGeometricFrobenius_hom (n : ℕ) :
    (cokernelPowIsoRootsOfUnitySheaf (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ n).hom =
      geometricFrobeniusModularCharacterVal k ℓ n •
        (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).hom := by
  rw [← cancel_epi (cokernel.π _), cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom,
    Preadditive.comp_zsmul, cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom]
  exact unitToRootsOfUnitySheaf_comp_specGeometricFrobenius f n (hζ n).pow_eq_one

/-- Along the semilinear structure `f ≫ σ`, the inverse identification `μ_{ℓⁿ} ≅ ℤ/ℓⁿ` is `q`
times the one along `f`, since `cₙ q = 1` in `ℤ/ℓⁿ`. -/
lemma cokernelPowIsoRootsOfUnitySheaf_comp_specGeometricFrobenius_inv (n : ℕ) :
    (cokernelPowIsoRootsOfUnitySheaf (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ n).inv =
      (Nat.card k : ℤ) • (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).inv := by
  have h : (cokernelPowIsoRootsOfUnitySheaf (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ n).hom ≫
      ((Nat.card k : ℤ) • (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).inv) = 𝟙 _ := by
    rw [cokernelPowIsoRootsOfUnitySheaf_comp_specGeometricFrobenius_hom, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, smul_smul, Iso.hom_inv_id]
    obtain ⟨m, hm⟩ := pow_dvd_geometricFrobeniusModularCharacterVal_mul_natCard_sub_one
      (k := k) (ℓ := ℓ) n
    rw [← sub_add_cancel (geometricFrobeniusModularCharacterVal k ℓ n * (Nat.card k : ℤ)) 1, hm,
      add_smul, one_smul, mul_comm, mul_smul, zsmul_id_cokernel_zsmul_id, smul_zero, zero_add]
  rw [← Category.comp_id (cokernelPowIsoRootsOfUnitySheaf (f ≫ (specGeometricFrobenius k).asIso.hom)
    ℓ hζ n).inv, ← h, Iso.inv_hom_id_assoc]

variable {X : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g]

/-- Along the semilinear structure `f ≫ σ`, the level trivializations of the pulled-back Tate
module tower are `q` times the ones along `f`. -/
lemma upperStarTateModuleLevelIso_comp_specGeometricFrobenius_hom (n : ℕ) :
    (upperStarTateModuleLevelIso g (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ n).hom =
      (Nat.card k : ℤ) • (upperStarTateModuleLevelIso g f ℓ hζ n).hom := by
  simp only [upperStarTateModuleLevelIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, cokernelPowIsoRootsOfUnitySheaf_comp_specGeometricFrobenius_inv,
    Preadditive.comp_zsmul, Functor.map_zsmul]

variable (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- Along the semilinear structure `f ≫ σ`, the trivialization of the pulled-back Tate module
tower is `q` times the one along `f`. -/
lemma upperStarTateModuleSystemHom_comp_specGeometricFrobenius :
    upperStarTateModuleSystemHom g (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ hζ' =
      (Nat.card k : ℤ) • upperStarTateModuleSystemHom g f ℓ hζ hζ' := by
  ext n
  rw [NatTrans.app_zsmul]
  exact upperStarTateModuleLevelIso_comp_specGeometricFrobenius_hom f hζ g n.unop

/-- **The trivialization of the Tate module along the semilinear structure**: for `g : U ⟶ X`
weakly étale with `U` over `k̄` through `f`, the trivialization `g^* ℤ_ℓ(1) ≅ g^* ℤ_ℓ,X` by the
roots of unity `ζₙ` along the structure `f ≫ σ` is `q` times the trivialization along `f`. -/
theorem upperStarMapModTateModuleIsoUnit_comp_specGeometricFrobenius_hom :
    (upperStarMapModTateModuleIsoUnit g (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ hζ').hom =
      (Nat.card k : ℤ) • (upperStarMapModTateModuleIsoUnit g f ℓ hζ hζ').hom := by
  have hI : (HasLimit.isoOfNatIso (upperStarTateModuleSystemIso g
        (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ hζ')).hom =
      (Nat.card k : ℤ) •
        (HasLimit.isoOfNatIso (upperStarTateModuleSystemIso g f ℓ hζ hζ')).hom := by
    apply limit.hom_ext
    intro j
    rw [HasLimit.isoOfNatIso_hom_π, Preadditive.zsmul_comp, HasLimit.isoOfNatIso_hom_π]
    simp only [upperStarTateModuleSystemIso, asIso_hom,
      upperStarTateModuleSystemHom_comp_specGeometricFrobenius f hζ g hζ', NatTrans.app_zsmul,
      Preadditive.comp_zsmul]
  simp only [upperStarMapModTateModuleIsoUnit, Iso.trans_hom]
  rw [hI, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

end FiniteField

end AlgebraicGeometry.ProEtale
