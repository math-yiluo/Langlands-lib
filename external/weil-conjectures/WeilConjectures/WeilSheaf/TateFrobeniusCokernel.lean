/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusLevel
public import WeilConjectures.TateTwist.TateModuleTrivialization

/-!
# The geometric Frobenius on the trivialized `μ_{ℓⁿ}`, in cokernel form

`WeilConjectures.WeilSheaf.TateFrobeniusLevel` computes the pullback of roots of unity along the
geometric Galois Frobenius `g = 𝟙 × σ` of a geometric fibre `X̄` on the generator `a ↦ ζ ^ a` of
`μ_{ℓⁿ}`. This file restates it on the identification `ℤ/ℓⁿ ≅ μ_{ℓⁿ}`
(`AlgebraicGeometry.ProEtale.cokernelPowIsoRootsOfUnitySheaf`) used to trivialize the Tate module:

* for any morphism `g : X ⟶ Y`, the pullback `g^*(ℤ/N)` of the cokernel of `N : ℤ ⟶ ℤ` is the
  cokernel of `N : ℤ ⟶ ℤ` on `X`, through the unit comparison `η : g^* ℤ ≅ ℤ`
  (`AlgebraicGeometry.ProEtale.upperStarCokernelPowIso`), compatibly with the reductions
  `ℤ/ℓⁿ⁺¹ ⟶ ℤ/ℓⁿ` (`AlgebraicGeometry.ProEtale.upperStarCokernelPowIso_naturality`);
* on the geometric fibre, `g^*(ℤ/ℓⁿ ≅ μ_{ℓⁿ})` followed by the comparison `g^* μ_{ℓⁿ} ⟶ μ_{ℓⁿ}`
  is `g^*(ℤ/ℓⁿ) ≅ ℤ/ℓⁿ` followed by `c` times `ℤ/ℓⁿ ≅ μ_{ℓⁿ}`, for `c = χ_ℓ(γ) mod ℓⁿ`
  (`upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_geometricGaloisFrobenius`).

For a weakly étale `g`, the comparison `g^* μ_N ⟶ μ_N` of
`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafHom` is the isomorphism
`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIso` computed on the slice site
(`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

section Cokernel

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (N : ℕ)

/-- The pullback of `N : ℤ ⟶ ℤ` is `N : ℤ ⟶ ℤ`, through the unit comparison `η : g^* ℤ ⟶ ℤ`. -/
lemma upperStar_map_zsmul_id_comp_η :
    (g)^*[Ab.{u + 1}].map ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}))) ≫
        η (g)^*[Ab.{u + 1}] =
      η (g)^*[Ab.{u + 1}] ≫ ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}))) := by
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]

/-- The pullback `g^*(ℤ/N)` of the cokernel of `N : ℤ ⟶ ℤ` on `Y` is the cokernel of
`N : ℤ ⟶ ℤ` on `X`: `g^*` preserves cokernels, and `η : g^* ℤ ≅ ℤ`. -/
noncomputable def upperStarCokernelPowIso :
    (g)^*[Ab.{u + 1}].obj (cokernel ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1})))) ≅
      cokernel ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}))) :=
  (isColimitCoforkMapOfIsColimit' (g)^*[Ab.{u + 1}]
    (cokernel.condition ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}))))
    (cokernelIsCokernel _)).coconePointUniqueUpToIso
    (isColimitCokernelCoforkOfIsoHomComp (asIso (η (g)^*[Ab.{u + 1}]))
      (upperStar_map_zsmul_id_comp_η g N) (cokernel.condition _) (cokernelIsCokernel _))

/-- The identification `g^*(ℤ/N) ≅ ℤ/N` is `η` on the projections `ℤ ⟶ ℤ/N`. -/
@[reassoc]
lemma upperStar_map_cokernel_π_comp_upperStarCokernelPowIso_hom :
    (g)^*[Ab.{u + 1}].map (cokernel.π ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1})))) ≫
        (upperStarCokernelPowIso g N).hom =
      η (g)^*[Ab.{u + 1}] ≫ cokernel.π ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}))) :=
  (isColimitCoforkMapOfIsColimit' (g)^*[Ab.{u + 1}]
    (cokernel.condition ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}))))
    (cokernelIsCokernel _)).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- The identifications `g^*(ℤ/ℓⁿ) ≅ ℤ/ℓⁿ` are compatible with the reductions
`ℤ/ℓⁿ⁺¹ ⟶ ℤ/ℓⁿ`. -/
lemma upperStarCokernelPowIso_naturality (ℓ n : ℕ) :
    (g)^*[Ab.{u + 1}].map (cokernelPowTransition (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1})) ℓ n) ≫
        (upperStarCokernelPowIso g (ℓ ^ n)).hom =
      (upperStarCokernelPowIso g (ℓ ^ (n + 1))).hom ≫
        cokernelPowTransition (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1})) ℓ n := by
  refine Cofork.IsColimit.hom_ext (isColimitCoforkMapOfIsColimit' (g)^*[Ab.{u + 1}]
    (cokernel.condition (((ℓ ^ (n + 1) : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}))))
    (cokernelIsCokernel _)) ?_
  try simp only [Cofork.π_ofπ]
  rw [← Functor.map_comp_assoc, cokernel_π_cokernelPowTransition,
    upperStar_map_cokernel_π_comp_upperStarCokernelPowIso_hom,
    upperStar_map_cokernel_π_comp_upperStarCokernelPowIso_hom_assoc,
    cokernel_π_cokernelPowTransition]

end Cokernel

/-! ### Weakly étale morphisms -/

section WeaklyEtale

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [hg : WeaklyEtale g] (N : ℕ)

/-- For a weakly étale `g`, the comparison map `g^* μ_N ⟶ μ_N` is the identity of
`U ↦ μ_N(Γ(U, 𝒪_U))` read on the slice site. -/
lemma upperStarRootsOfUnityComparison_eq_of_weaklyEtale :
    upperStarRootsOfUnityComparison g N =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} g hg).hom.app _ ≫
        (localizationRestrictionRootsOfUnityIso g N).hom := by
  have h : upperStarRootsOfUnityComparison g N =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} g hg).hom.app _ ≫
        ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g hg).homEquiv _ _).symm
          (rootsOfUnityToLowerStar g N) := by
    rw [upperStarRootsOfUnityComparison, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      upperStarIsoLocalizationRestriction,
      ← Adjunction.leftAdjointUniq_hom_app_counit _
        (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g hg),
      NatTrans.naturality_assoc]
  rw [h, localizationRestrictionLowerStarAdjunction_homEquiv_symm_rootsOfUnityToLowerStar]

/-- For a weakly étale `g`, the isomorphism `g^* μ_N ≅ μ_N` computed on the slice site is the
comparison map `g^* μ_N ⟶ μ_N`. -/
lemma upperStarRootsOfUnitySheafIso_hom :
    (upperStarRootsOfUnitySheafIso g N).hom = upperStarRootsOfUnitySheafHom g N := by
  rw [upperStarRootsOfUnitySheafIso, upperStarRootsOfUnitySheafHom,
    upperStarRootsOfUnityComparison_eq_of_weaklyEtale]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]

end WeaklyEtale

/-! ### The geometric Frobenius -/

section FiniteField

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k)) {ζ : ℕ → AlgebraicClosure k}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))

/-- **The geometric Galois Frobenius on the trivialized `μ_{ℓⁿ}`, in cokernel form**: on the
geometric fibre `X̄` with its trivializations `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` by the compatible system `ζₙ`, the
pullback along `g = 𝟙 × σ` of `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` followed by the comparison `g^* μ_{ℓⁿ} ⟶ μ_{ℓⁿ}` is
`g^*(ℤ/ℓⁿ) ≅ ℤ/ℓⁿ` followed by `c` times `ℤ/ℓⁿ ≅ μ_{ℓⁿ}`, where `c ∈ ℤ/ℓⁿ` is the value of the
modular cyclotomic character of the geometric Frobenius (`c q = 1`). -/
theorem upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_geometricGaloisFrobenius (n : ℕ) :
    (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map
        (cokernelPowIsoRootsOfUnitySheaf a.geometricFiberToAlgebraicClosure ℓ hζ n).hom ≫
        upperStarRootsOfUnitySheafHom a.geometricGaloisFrobenius.asIso.hom (ℓ ^ n) =
      (upperStarCokernelPowIso a.geometricGaloisFrobenius.asIso.hom (ℓ ^ n)).hom ≫
        ((((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val : ℤ) •
          (cokernelPowIsoRootsOfUnitySheaf a.geometricFiberToAlgebraicClosure ℓ hζ n).hom) := by
  refine Cofork.IsColimit.hom_ext (isColimitCoforkMapOfIsColimit'
    (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}]
    (cokernel.condition (((ℓ ^ n : ℕ) : ℤ) •
      𝟙 (𝟙_ (Sheaf (ProEt.topology a.geometricFiber) Ab.{u + 1}))))
    (cokernelIsCokernel _)) ?_
  try simp only [Cofork.π_ofπ]
  rw [← Functor.map_comp_assoc, cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom,
    upperStar_map_cokernel_π_comp_upperStarCokernelPowIso_hom_assoc, Preadditive.comp_zsmul,
    cokernel_π_cokernelPowIsoRootsOfUnitySheaf_hom, upperStarRootsOfUnitySheafHom,
    ← Functor.map_comp_assoc,
    reassoc_of% (upperStar_map_unitToRootsOfUnitySheaf_geometricGaloisFrobenius a n
      (hζ n).pow_eq_one),
    Iso.hom_inv_id, Category.comp_id]

end FiniteField

end AlgebraicGeometry.ProEtale
