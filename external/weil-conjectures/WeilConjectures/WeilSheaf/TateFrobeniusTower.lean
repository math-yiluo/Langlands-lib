/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusCokernel
public import WeilConjectures.TateTwist.TateModuleUpperStar

/-!
# The geometric Frobenius on the trivialized tower of roots of unity

The Tate module `ℤ_ℓ(1)` is the limit of the tower `n ↦ μ_{ℓⁿ}` of sheaves of roots of unity
with the `ℓ`-th power maps (`AlgebraicGeometry.ProEtale.rootsOfUnityTower`). Over a field `K`
with a compatible system `ζₙ` of primitive `ℓⁿ`-th roots of unity, this tower is the tower
`n ↦ ℤ/ℓⁿ` of reductions of the unit `ℤ`
(`AlgebraicGeometry.ProEtale.cokernelPowTowerIsoRootsOfUnityTower`, from the level
identifications `AlgebraicGeometry.ProEtale.cokernelPowIsoRootsOfUnitySheaf`). The pullback
along a morphism `g` identifies the towers of roots of unity
(`AlgebraicGeometry.ProEtale.upperStarRootsOfUnityTowerHom`) and the towers of reductions
(`AlgebraicGeometry.ProEtale.upperStarCokernelPowTowerIso`).

On the geometric fibre `X̄` of a scheme over a finite field `k`, the pullback along the geometric
Galois Frobenius `g = 𝟙 × σ` reads, on the trivialized tower `n ↦ ℤ/ℓⁿ`, as the compatible
system of scalars `cₙ = χ_ℓ(γ) mod ℓⁿ`, the reductions of the `ℓ`-adic cyclotomic character of
the geometric Frobenius `γ` of `k̄`
(`AlgebraicGeometry.ProEtale.cokernelPowTowerIsoRootsOfUnityTower_geometricGaloisFrobenius`).
A compatible system of integers acts on the tower of reductions through
`AlgebraicGeometry.ProEtale.cokernelPowTowerScalar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-! ### Scalars on the tower of reductions -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (A : C)

/-- The cokernel of `N : A ⟶ A` is killed by `N`. -/
lemma zsmul_id_cokernel_zsmul_id (N : ℕ) :
    ((N : ℤ) • 𝟙 (cokernel ((N : ℤ) • 𝟙 A))) = 0 := by
  rw [← cancel_epi (cokernel.π ((N : ℤ) • 𝟙 A)), Preadditive.comp_zsmul, Category.comp_id,
    comp_zero, ← Category.id_comp (cokernel.π ((N : ℤ) • 𝟙 A)), ← Preadditive.zsmul_comp,
    cokernel.condition]

/-- `ℓⁿ` kills the reduction `A/ℓⁿ⁺¹ ⟶ A/ℓⁿ`. -/
lemma zsmul_cokernelPowTransition (ℓ n : ℕ) :
    (((ℓ ^ n : ℕ) : ℤ) • cokernelPowTransition A ℓ n) = 0 := by
  rw [← Category.comp_id (cokernelPowTransition A ℓ n), ← Preadditive.comp_zsmul,
    zsmul_id_cokernel_zsmul_id, comp_zero]

/-- The scalars `cₙ` of a compatible system, `cₙ ≡ cₙ₊₁ mod ℓⁿ`, commute with the reductions
`A/ℓⁿ⁺¹ ⟶ A/ℓⁿ`. -/
lemma cokernelPowTransition_comp_zsmul_id (ℓ : ℕ) (c : ℕ → ℤ)
    (hc : ∀ n, ((ℓ ^ n : ℕ) : ℤ) ∣ c n - c (n + 1)) (n : ℕ) :
    cokernelPowTransition A ℓ n ≫ (c n • 𝟙 (cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A))) =
      (c (n + 1) • 𝟙 (cokernel (((ℓ ^ (n + 1) : ℕ) : ℤ) • 𝟙 A))) ≫ cokernelPowTransition A ℓ n := by
  obtain ⟨m, hm⟩ := hc n
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id, Category.id_comp,
    ← sub_eq_zero, ← sub_smul, hm, mul_comm, mul_smul, zsmul_cokernelPowTransition, smul_zero]

/-- A compatible system of integers `cₙ`, `cₙ ≡ cₙ₊₁ mod ℓⁿ`, acts on the tower `n ↦ A/ℓⁿ` of
reductions: by `cₙ` on `A/ℓⁿ`. -/
noncomputable def cokernelPowTowerScalar (ℓ : ℕ) (c : ℕ → ℤ)
    (hc : ∀ n, ((ℓ ^ n : ℕ) : ℤ) ∣ c n - c (n + 1)) :
    cokernelPowTower A ℓ ⟶ cokernelPowTower A ℓ :=
  NatTrans.ofOpSequence (fun n ↦ c n • 𝟙 (cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A))) (fun n ↦ by
    rw [cokernelPowTower_map_succ]
    exact cokernelPowTransition_comp_zsmul_id A ℓ c hc n)

@[simp]
lemma cokernelPowTowerScalar_app (ℓ : ℕ) (c : ℕ → ℤ)
    (hc : ∀ n, ((ℓ ^ n : ℕ) : ℤ) ∣ c n - c (n + 1)) (n : ℕᵒᵖ) :
    (cokernelPowTowerScalar A ℓ c hc).app n =
      c n.unop • 𝟙 (cokernel (((ℓ ^ n.unop : ℕ) : ℤ) • 𝟙 A)) :=
  rfl

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The towers -/

section Towers

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- The tower `n ↦ μ_{ℓⁿ}` of sheaves of roots of unity on `X_proét`, with the `ℓ`-th power maps
`μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`; the Tate module tower `AlgebraicGeometry.ProEtale.tateModuleSystem` is
the tower of free `ℤ_ℓ,X`-modules on it. -/
noncomputable def rootsOfUnityTower : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X (ℓ ^ n) ℓ)

lemma rootsOfUnityTower_obj (n : ℕ) :
    (rootsOfUnityTower X ℓ).obj (op n) = rootsOfUnitySheaf X (ℓ ^ n) :=
  rfl

@[simp]
lemma rootsOfUnityTower_map_succ (n : ℕ) :
    (rootsOfUnityTower X ℓ).map (homOfLE (n.le_add_right 1)).op =
      eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
        rootsOfUnitySheafPow X (ℓ ^ n) ℓ :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end Towers

section Trivialization

variable {K : Type u} [Field K] {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime]
  {ζ : ℕ → K} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- The comparison from the tower of reductions `n ↦ ℤ/ℓⁿ` to the tower of roots of unity
`n ↦ μ_{ℓⁿ}`, `a ↦ ζₙ^a`. -/
noncomputable def cokernelPowTowerToRootsOfUnityTower :
    cokernelPowTower (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})) ℓ ⟶ rootsOfUnityTower U ℓ :=
  NatTrans.ofOpSequence (fun n ↦ (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).hom) (fun n ↦ by
    rw [cokernelPowTower_map_succ, rootsOfUnityTower_map_succ]
    exact cokernelPowTransition_comp_cokernelPowIsoRootsOfUnitySheaf_hom f ℓ hζ hζ' n)

instance : IsIso (cokernelPowTowerToRootsOfUnityTower f ℓ hζ hζ') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact inferInstanceAs (IsIso (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n.unop).hom)

/-- **The tower of roots of unity is trivial over a base with a compatible system of primitive
`ℓⁿ`-th roots of unity**: `n ↦ ℤ/ℓⁿ` is `n ↦ μ_{ℓⁿ}` through `a ↦ ζₙ^a`. -/
noncomputable def cokernelPowTowerIsoRootsOfUnityTower :
    cokernelPowTower (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})) ℓ ≅ rootsOfUnityTower U ℓ :=
  asIso (cokernelPowTowerToRootsOfUnityTower f ℓ hζ hζ')

@[simp]
lemma cokernelPowTowerIsoRootsOfUnityTower_hom_app (n : ℕᵒᵖ) :
    (cokernelPowTowerIsoRootsOfUnityTower f ℓ hζ hζ').hom.app n =
      (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n.unop).hom :=
  rfl

end Trivialization

/-! ### Pullbacks of the towers -/

section Pullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (ℓ : ℕ)

/-- The comparison from the pullback of the tower of reductions `n ↦ ℤ/ℓⁿ` to the tower of
reductions, through `η : g^* ℤ ≅ ℤ`. -/
noncomputable def upperStarCokernelPowTowerHom :
    cokernelPowTower (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1})) ℓ ⋙ (g)^*[Ab.{u + 1}] ⟶
      cokernelPowTower (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1})) ℓ :=
  NatTrans.ofOpSequence (fun n ↦ (upperStarCokernelPowIso g (ℓ ^ n)).hom) (fun n ↦ by
    rw [Functor.comp_map, cokernelPowTower_map_succ, cokernelPowTower_map_succ]
    exact upperStarCokernelPowIso_naturality g ℓ n)

instance : IsIso (upperStarCokernelPowTowerHom g ℓ) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact inferInstanceAs (IsIso (upperStarCokernelPowIso g (ℓ ^ n.unop)).hom)

/-- The pullback of the tower of reductions `n ↦ ℤ/ℓⁿ` is the tower of reductions, through
`η : g^* ℤ ≅ ℤ`. -/
noncomputable def upperStarCokernelPowTowerIso :
    cokernelPowTower (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1})) ℓ ⋙ (g)^*[Ab.{u + 1}] ≅
      cokernelPowTower (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1})) ℓ :=
  asIso (upperStarCokernelPowTowerHom g ℓ)

@[simp]
lemma upperStarCokernelPowTowerIso_hom_app (n : ℕᵒᵖ) :
    (upperStarCokernelPowTowerIso g ℓ).hom.app n =
      (upperStarCokernelPowIso g (ℓ ^ n.unop)).hom :=
  rfl

variable {k : Type u} [Field k] (f : Y ⟶ Spec (.of k)) [NeZero (ℓ : k)]

/-- The comparison from the pullback of the tower of roots of unity to the tower of roots of
unity. -/
noncomputable def upperStarRootsOfUnityTowerHom :
    rootsOfUnityTower Y ℓ ⋙ (g)^*[Ab.{u + 1}] ⟶ rootsOfUnityTower X ℓ :=
  NatTrans.ofOpSequence (fun n ↦ upperStarRootsOfUnitySheafHom g (ℓ ^ n)) (fun n ↦ by
    rw [Functor.comp_map, rootsOfUnityTower_map_succ, rootsOfUnityTower_map_succ]
    exact upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g n)

@[simp]
lemma upperStarRootsOfUnityTowerHom_app (n : ℕᵒᵖ) :
    (upperStarRootsOfUnityTowerHom g ℓ).app n = upperStarRootsOfUnitySheafHom g (ℓ ^ n.unop) :=
  rfl

variable {k : Type u} [Field k] (f : Y ⟶ Spec (.of k)) [NeZero (ℓ : k)]

include f in
/-- The pullback of the tower of roots of unity is the tower of roots of unity, for `Y` over a
field in which `ℓ` is invertible. -/
lemma isIso_upperStarRootsOfUnityTowerHom : IsIso (upperStarRootsOfUnityTowerHom g ℓ) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have := NeZero.natCast_pow (R := k) ℓ n.unop
  exact isIso_upperStarRootsOfUnitySheafHom g f (ℓ ^ n.unop)

end Pullback

/-! ### The geometric Frobenius -/

section FiniteField

variable (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- The values `cₙ ∈ ℤ/ℓⁿ` of the modular cyclotomic characters of the geometric Frobenius are
compatible: `cₙ₊₁ ≡ cₙ mod ℓⁿ`, both being reductions of the `ℓ`-adic cyclotomic character. -/
lemma geometricFrobeniusModularCharacter_succ_cast (n : ℕ) :
    (((geometricFrobeniusModularCharacter k ℓ (n + 1) : (ZMod (ℓ ^ (n + 1)))ˣ) :
        ZMod (ℓ ^ (n + 1))).cast : ZMod (ℓ ^ n)) =
      ((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)) := by
  have := WeilSheaf.purity_neZero_natCast_algebraicClosure k ℓ
  let := Fintype.ofFinite k
  unfold geometricFrobeniusModularCharacter
  rw [← cyclotomicCharacter.toZModPow, ← cyclotomicCharacter.toZModPow]
  exact PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) _

/-- The integers `cₙ = (χ_ℓ(γ) mod ℓⁿ).val` of the geometric Frobenius. -/
noncomputable def geometricFrobeniusModularCharacterVal (n : ℕ) : ℤ :=
  ((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val

/-- The integers `cₙ` form a compatible system: `ℓⁿ ∣ cₙ - cₙ₊₁`. -/
lemma pow_dvd_geometricFrobeniusModularCharacterVal_sub (n : ℕ) :
    ((ℓ ^ n : ℕ) : ℤ) ∣ geometricFrobeniusModularCharacterVal k ℓ n -
      geometricFrobeniusModularCharacterVal k ℓ (n + 1) := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, geometricFrobeniusModularCharacterVal,
    geometricFrobeniusModularCharacterVal, Int.cast_natCast, Int.cast_natCast,
    ZMod.natCast_zmod_val, ZMod.natCast_val, geometricFrobeniusModularCharacter_succ_cast,
    sub_self]

variable {k ℓ} {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k)) {ζ : ℕ → AlgebraicClosure k}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- **The geometric Galois Frobenius on the trivialized tower of roots of unity**: on the
geometric fibre `X̄`, the pullback along `g = 𝟙 × σ` of the trivialization `n ↦ (ℤ/ℓⁿ ≅ μ_{ℓⁿ})`
followed by the identification `g^* μ_{ℓⁿ} ≅ μ_{ℓⁿ}` is the identification `g^*(ℤ/ℓⁿ) ≅ ℤ/ℓⁿ`
followed by the scalars `cₙ = χ_ℓ(γ) mod ℓⁿ` and the trivialization. -/
theorem cokernelPowTowerIsoRootsOfUnityTower_geometricGaloisFrobenius :
    Functor.whiskerRight (cokernelPowTowerIsoRootsOfUnityTower
        a.geometricFiberToAlgebraicClosure ℓ hζ hζ').hom
        (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}] ≫
        upperStarRootsOfUnityTowerHom a.geometricGaloisFrobenius.asIso.hom ℓ =
      (upperStarCokernelPowTowerIso a.geometricGaloisFrobenius.asIso.hom ℓ).hom ≫
        cokernelPowTowerScalar _ ℓ (geometricFrobeniusModularCharacterVal k ℓ)
          (pow_dvd_geometricFrobeniusModularCharacterVal_sub k ℓ) ≫
        (cokernelPowTowerIsoRootsOfUnityTower a.geometricFiberToAlgebraicClosure ℓ hζ hζ').hom := by
  refine NatTrans.ext (funext fun n ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    cokernelPowTowerIsoRootsOfUnityTower_hom_app, upperStarRootsOfUnityTowerHom_app,
    upperStarCokernelPowTowerIso_hom_app, cokernelPowTowerScalar_app, Preadditive.zsmul_comp]
  exact upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_geometricGaloisFrobenius a hζ n.unop

end FiniteField

end AlgebraicGeometry.ProEtale
