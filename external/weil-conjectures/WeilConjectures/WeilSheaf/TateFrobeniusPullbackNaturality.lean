/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusPullback

/-!
# The trivialization of the Tate module is natural under pullback

Let `g : U ⟶ X` and `g₁ : U' ⟶ U` be weakly étale, `g' = g₁ ≫ g`, and let `U` be over a field
`K` through `f`, `U'` through `f' = g₁ ≫ f`, with a compatible system `ζₙ` of primitive `ℓⁿ`-th
roots of unity of `K`. The trivializations `g^* ℤ_ℓ(1) ≅ g^* ℤ_ℓ,X` and `g'^* ℤ_ℓ(1) ≅ g'^* ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.upperStarMapModTateModuleIsoUnit`) are compatible with the pullback
along `g₁`, through the factorization isomorphism `g^* ⋙ g₁^* ≅ g'^*` on underlying sheaves
(`AlgebraicGeometry.ProEtale.upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom`). This is
checked after the legs `g'^* ℤ_ℓ,X ⟶ g'^* ℤ_ℓ,X ⊗ ℤ/ℓⁿ` of the `ℓ`-adic completeness limit, where
it reduces to the compatibility of the level identifications `ℤ/ℓⁿ ≅ μ_{ℓⁿ}` with pullback
(`AlgebraicGeometry.ProEtale.upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_of_comp_eq`), the
cocycle of the comparisons `g^* μ_N ⟶ μ_N`, and the monoidality of the factorization isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section Cocycle

variable {U' U X : Scheme.{u}} (g₁ : U' ⟶ U) (g : U ⟶ X) {g' : U' ⟶ X} (h : g₁ ≫ g = g')

/-- The comparison `g'^* μ_N ⟶ μ_N` along `g₁ ≫ g = g'`. -/
lemma upperStarCongr_hom_app_comp_upperStarRootsOfUnitySheafHom (N : ℕ) :
    (upperStarCongr Ab.{u + 1} h).hom.app (rootsOfUnitySheaf X N) ≫
        upperStarRootsOfUnitySheafHom g' N =
      upperStarRootsOfUnitySheafHom (g₁ ≫ g) N := by
  subst h
  simp [upperStarCongr]

/-- **The cocycle of the comparisons `g^* μ_N ⟶ μ_N`**: `g₁^*(g^* μ_N ⟶ μ_N)` followed by
`g₁^* μ_N ⟶ μ_N` is the composition isomorphism followed by `(g₁ ≫ g)^* μ_N ⟶ μ_N`. -/
lemma upperStar_map_upperStarRootsOfUnitySheafHom_comp (N : ℕ) :
    (g₁)^*[Ab.{u + 1}].map (upperStarRootsOfUnitySheafHom g N) ≫
        upperStarRootsOfUnitySheafHom g₁ N =
      (upperStarComp Ab.{u + 1} g₁ g).inv.app (rootsOfUnitySheaf X N) ≫
        upperStarRootsOfUnitySheafHom (g₁ ≫ g) N := by
  simp only [upperStarRootsOfUnitySheafHom, Functor.map_comp, Category.assoc]
  rw [← upperStarRootsOfUnityComparison_comp g₁ g N, ← Functor.map_comp_assoc (g₁)^*[Ab.{u + 1}]
    (rootsOfUnitySheafIso U N).inv, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, ← NatTrans.naturality_assoc]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  try rfl

/-- The comparison `g^* μ_N ⟶ μ_N` along `g₁ ≫ g = g'`, through the factorization isomorphism
`g^* ⋙ g₁^* ≅ g'^*`. -/
@[reassoc]
lemma upperStar_map_upperStarRootsOfUnitySheafHom_comp' (N : ℕ) :
    (g₁)^*[Ab.{u + 1}].map (upperStarRootsOfUnitySheafHom g N) ≫
        upperStarRootsOfUnitySheafHom g₁ N =
      (upperStarFactorIso g₁ g h).hom.app (rootsOfUnitySheaf X N) ≫
        upperStarRootsOfUnitySheafHom g' N := by
  rw [upperStar_map_upperStarRootsOfUnitySheafHom_comp, upperStarFactorIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    upperStarCongr_hom_app_comp_upperStarRootsOfUnitySheafHom]

end Cocycle

section Leg

variable {U' U X : Scheme.{u}} (g₁ : U' ⟶ U) (g : U ⟶ X) {g' : U' ⟶ X} (h : g₁ ≫ g = g')

/-- The oplax right unitality of the pullback, solved for `δ`. -/
@[reassoc]
lemma upperStar_map_rightUnitor_inv_comp_δ (A : Sheaf (ProEt.topology U) Ab.{u + 1}) :
    (g₁)^*[Ab.{u + 1}].map (ρ_ A).inv ≫ δ (g₁)^*[Ab.{u + 1}] A (𝟙_ _) =
      (ρ_ ((g₁)^*[Ab.{u + 1}].obj A)).inv ≫
        (g₁)^*[Ab.{u + 1}].obj A ◁ inv (η (g₁)^*[Ab.{u + 1}]) := by
  rw [← cancel_mono ((g₁)^*[Ab.{u + 1}].obj A ◁ η (g₁)^*[Ab.{u + 1}]), Category.assoc,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp, IsIso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    ← Functor.OplaxMonoidal.oplax_right_unitality]

/-- **The legs of the tower of free modules under pullback**: for `A` on `U`, the factorization
`g₁^* A ⟶ A'` followed by the leg `A' ⟶ A' ⊗ ℤ/N` is the pullback of the leg `A ⟶ A ⊗ ℤ/N`
followed by `δ` and the factorization tensored with `g₁^*(ℤ/N) ≅ ℤ/N`. -/
lemma comp_rightUnitor_inv_comp_whiskerLeft_cokernel_π {A : Sheaf (ProEt.topology U) Ab.{u + 1}}
    {A' : Sheaf (ProEt.topology U') Ab.{u + 1}} (φ : (g₁)^*[Ab.{u + 1}].obj A ⟶ A') (N : ℕ) :
    φ ≫ (ρ_ A').inv ≫ A' ◁ cokernel.π ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U') Ab.{u + 1}))) =
      (g₁)^*[Ab.{u + 1}].map ((ρ_ A).inv ≫
          A ◁ cokernel.π ((N : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})))) ≫
        δ (g₁)^*[Ab.{u + 1}] A _ ≫ (φ ⊗ₘ (upperStarCokernelPowIso g₁ N).hom) := by
  rw [Functor.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc,
    upperStar_map_rightUnitor_inv_comp_δ_assoc, tensorHom_def',
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Category.assoc, upperStar_map_cokernel_π_comp_upperStarCokernelPowIso_hom,
    IsIso.inv_hom_id_assoc, whisker_exchange, rightUnitor_inv_naturality_assoc]

end Leg

section Factor

variable {U' U X : Scheme.{u}} (g₁ : U' ⟶ U) (g : U ⟶ X) {g' : U' ⟶ X} (h : g₁ ≫ g = g')

/-- The factorization isomorphism is compatible with `δ`. -/
@[reassoc]
lemma upperStarFactorIso_hom_app_tensor_comp_δ (A B : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (upperStarFactorIso g₁ g h).hom.app (A ⊗ B) ≫ δ (g')^*[Ab.{u + 1}] A B =
      ((g₁)^*[Ab.{u + 1}].map (δ (g)^*[Ab.{u + 1}] A B) ≫
        δ (g₁)^*[Ab.{u + 1}] ((g)^*[Ab.{u + 1}].obj A) ((g)^*[Ab.{u + 1}].obj B)) ≫
        ((upperStarFactorIso g₁ g h).hom.app A ⊗ₘ (upperStarFactorIso g₁ g h).hom.app B) := by
  have hτ := NatTrans.IsMonoidal.tensor (τ := (upperStarFactorIso g₁ g h).hom) A B
  rw [← cancel_epi (μ ((g)^*[Ab.{u + 1}] ⋙ (g₁)^*[Ab.{u + 1}]) A B), ← Category.assoc, hτ,
    Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  simp only [Functor.LaxMonoidal.comp_μ, Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, CategoryTheory.Functor.map_id,
    Category.id_comp, Functor.Monoidal.μ_δ_assoc]

end Factor

/-! ### The trivialization on underlying sheaves -/

section Underlying

variable {X U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] {K : Type u} [Field K]
  (f : U ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] {ζ : ℕ → K}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- The projection formula of the trivialization, on underlying sheaves. -/
lemma upperStarMapModTateModuleIsoUnit_hom_hom_comp (n : ℕ) :
    (upperStarMapModTateModuleIsoUnit g f ℓ hζ hζ').hom.hom ≫
        ((ρ_ ((g)^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))).inv ≫
          (g)^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ◁
            cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U) Ab.{u + 1})))) =
      (g)^*[Ab.{u + 1}].map (limit.π (tateModuleSystem X ℓ) (op n)).hom ≫
        δ (g)^*[Ab.{u + 1}] (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)
          (rootsOfUnitySheaf X (ℓ ^ n)) ≫
        (g)^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ◁
          (upperStarRootsOfUnitySheafHom g (ℓ ^ n) ≫
            (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).inv) := by
  have h := congrArg Mod.Hom.hom (upperStarMapModTateModuleIsoUnit_hom_comp_π g f ℓ hζ hζ' n)
  simpa [Mod.comp_hom', upperStarTateModuleLevelIso, upperStarRootsOfUnitySheafIso_hom] using h

end Underlying

/-! ### Naturality under pullback -/

section Naturality

variable {U' U X : Scheme.{u}} (g₁ : U' ⟶ U) [WeaklyEtale g₁] (g : U ⟶ X) [WeaklyEtale g]
  {g' : U' ⟶ X} [WeaklyEtale g'] (h : g₁ ≫ g = g') {K : Type u} [Field K]
  (f : U ⟶ Spec (.of K)) {f' : U' ⟶ Spec (.of K)} (hf : g₁ ≫ f = f') (ℓ : ℕ) [Fact ℓ.Prime]
  {ζ : ℕ → K} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

omit [WeaklyEtale g₁] in
include hf in
/-- The inverse level identifications under pullback over the same field. -/
lemma upperStar_map_cokernelPowIsoRootsOfUnitySheaf_inv_comp (n : ℕ) :
    (g₁)^*[Ab.{u + 1}].map (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).inv ≫
        (upperStarCokernelPowIso g₁ (ℓ ^ n)).hom =
      upperStarRootsOfUnitySheafHom g₁ (ℓ ^ n) ≫
        (cokernelPowIsoRootsOfUnitySheaf f' ℓ hζ n).inv := by
  rw [← cancel_epi ((g₁)^*[Ab.{u + 1}].map (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).hom),
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Category.assoc, upperStar_map_cokernelPowIsoRootsOfUnitySheaf_hom_of_comp_eq g₁ f f' hf ℓ
      hζ n, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [WeaklyEtale g₁] in
include h hf in
/-- The naturality of the trivialization under pullback, at level `n`: both sides of
`AlgebraicGeometry.ProEtale.upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom` agree after
the leg `g'^* ℤ_ℓ,X ⟶ g'^* ℤ_ℓ,X ⊗ ℤ/ℓⁿ`. -/
lemma upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom_comp_leg (n : ℕ) :
    (g₁)^*[Ab.{u + 1}].map (upperStarMapModTateModuleIsoUnit g f ℓ hζ hζ').hom.hom ≫
        (upperStarFactorIso g₁ g h).hom.app
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ≫
        (ρ_ ((g')^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))).inv ≫
        (g')^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ◁
          cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U') Ab.{u + 1}))) =
      (upperStarFactorIso g₁ g h).hom.app (tateModule X ℓ).X ≫
        (upperStarMapModTateModuleIsoUnit g' f' ℓ hζ hζ').hom.hom ≫
        (ρ_ ((g')^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))).inv ≫
        (g')^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ◁
          cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ (Sheaf (ProEt.topology U') Ab.{u + 1}))) := by
  rw [comp_rightUnitor_inv_comp_whiskerLeft_cokernel_π g₁ ((upperStarFactorIso g₁ g h).hom.app
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) (ℓ ^ n),
    ← Functor.map_comp_assoc, upperStarMapModTateModuleIsoUnit_hom_hom_comp,
    upperStarMapModTateModuleIsoUnit_hom_hom_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc, tensorHom_def',
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.map_comp (g₁)^*[Ab.{u + 1}] (upperStarRootsOfUnitySheafHom g (ℓ ^ n))
      (cokernelPowIsoRootsOfUnitySheaf f ℓ hζ n).inv,
    Category.assoc, upperStar_map_cokernelPowIsoRootsOfUnitySheaf_inv_comp g₁ f hf ℓ hζ n,
    upperStar_map_upperStarRootsOfUnitySheafHom_comp'_assoc g₁ g h,
    MonoidalCategory.whiskerLeft_comp _
      ((upperStarFactorIso g₁ g h).hom.app (rootsOfUnitySheaf X (ℓ ^ n))),
    Category.assoc, whisker_exchange, ← tensorHom_def'_assoc,
    ← upperStarFactorIso_hom_app_tensor_comp_δ_assoc,
    ← Functor.comp_map (g)^*[Ab.{u + 1}] (g₁)^*[Ab.{u + 1}]]
  erw [(upperStarFactorIso g₁ g h).hom.naturality_assoc
    (limit.π (tateModuleSystem X ℓ) (op n)).hom]
  try rfl

omit [WeaklyEtale g₁] in
include h hf in
/-- **The trivialization of the Tate module is natural under weakly étale pullback**: on underlying
sheaves, `g₁^*` of the trivialization `g^* ℤ_ℓ(1) ≅ g^* ℤ_ℓ,X` followed by the factorization
`g₁^* g^* ℤ_ℓ,X ≅ g'^* ℤ_ℓ,X` is the factorization `g₁^* g^* ℤ_ℓ(1) ≅ g'^* ℤ_ℓ(1)` followed by the
trivialization `g'^* ℤ_ℓ(1) ≅ g'^* ℤ_ℓ,X`. -/
theorem upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom :
    (g₁)^*[Ab.{u + 1}].map (upperStarMapModTateModuleIsoUnit g f ℓ hζ hζ').hom.hom ≫
        (upperStarFactorIso g₁ g h).hom.app
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) =
      (upperStarFactorIso g₁ g h).hom.app (tateModule X ℓ).X ≫
        (upperStarMapModTateModuleIsoUnit g' f' ℓ hζ hζ').hom.hom := by
  have hS' : IsLimit (cokernelPowTowerCone ((g')^*[Ab.{u + 1}].obj
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) ℓ) :=
    isLimitCokernelPowTowerConeOfIso ((upperStarFromPointComp g').app _).symm
      (isLimitCokernelPowTowerCone ℓ U')
  refine IsLimit.hom_ext (isLimitOfIsColimitCokernelCofork
    ((Mod.forget _).mapCone (Mod.freeCokernelPowTowerCone ((g')^*[Ab.{u + 1}].obj
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) ℓ)) _
    (Mod.isColimitCokernelCoforkFreeCokernelPowTowerCone _ ℓ) hS') fun n ↦ ?_
  induction n with | op n => ?_
  simp only [Functor.mapCone_π_app, Mod.forget_map, Mod.freeCokernelPowTowerCone_π_app_hom,
    Category.assoc]
  exact upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom_comp_leg g₁ g h f hf ℓ hζ hζ' n

end Naturality

end AlgebraicGeometry.ProEtale
