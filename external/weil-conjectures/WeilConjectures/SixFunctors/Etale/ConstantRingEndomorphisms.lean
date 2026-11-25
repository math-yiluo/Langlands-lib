/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
public import WeilConjectures.CategoryTheory.Sites.ModuleCohomologyExt

/-!
# Endomorphisms of the constant sheaf `Λ` for a quotient ring `Λ` of `ℤ`

Let `Λ` be a quotient ring of `ℤ` (e.g. `ℤ/ℓᵐ`). On a connected scheme every endomorphism of
the constant étale sheaf `Λ_X` is an integer multiple of the identity
(`AlgebraicGeometry.Etale.exists_eq_zsmul_id_constantRing`), and morphisms of étale sheaves of
`Λ`-modules are the morphisms of the underlying abelian sheaves
(`AlgebraicGeometry.Etale.exists_sheafForget₂_map_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (hΛ : Function.Surjective (Int.cast : ℤ → Λ))
include hΛ

/-- If `Λ` is a quotient of `ℤ` and `X` is connected, every endomorphism of the constant étale
sheaf `Λ_X` is an integer multiple of the identity. -/
theorem exists_eq_zsmul_id_constantRing (X : Scheme.{u}) [ConnectedSpace X]
    (f : Sheaf.constantRing X.smallEtaleTopology Λ ⟶ Sheaf.constantRing X.smallEtaleTopology Λ) :
    ∃ k : ℤ, f = k • 𝟙 _ := by
  let E := unitIsoSingleFunctorConstantSheaf Λ X
  obtain ⟨r, hr⟩ := (bijective_smul_id_unit Λ X).2
    (E.hom ≫ (DerivedCategory.singleFunctor _ 0).map f ≫ E.inv)
  obtain ⟨k, rfl⟩ := hΛ r
  refine ⟨k, (DerivedCategory.singleFunctor _ 0).map_injective ?_⟩
  have hf : (DerivedCategory.singleFunctor _ 0).map f = E.inv ≫ ((k : Λ) • 𝟙 _) ≫ E.hom := by
    simp only at hr
    rw [hr]
    simp
  rw [hf, Int.cast_smul_eq_zsmul, Functor.map_zsmul, CategoryTheory.Functor.map_id,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Iso.inv_hom_id]

/-- If `Λ` is a quotient of `ℤ`, every morphism of the underlying abelian sheaves of two étale
sheaves of `Λ`-modules is `Λ`-linear. -/
theorem exists_sheafForget₂_map_eq {X : Scheme.{u}}
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : (sheafForget₂ Λ X).obj M ⟶ (sheafForget₂ Λ X).obj N) :
    ∃ f : M ⟶ N, (sheafForget₂ Λ X).map f = h := by
  let φ (U : X.Etaleᵒᵖ) : M.obj.obj U →ₗ[Λ] N.obj.obj U :=
    { toFun x := (h.hom.app U).hom x
      map_add' := map_add (h.hom.app U).hom
      map_smul' r x := by
        obtain ⟨k, rfl⟩ := hΛ r
        simp only [Int.cast_smul_eq_zsmul, RingHom.id_apply]
        exact map_zsmul (h.hom.app U).hom k x }
  let τ : M.obj ⟶ N.obj :=
    { app U := ModuleCat.ofHom (φ U)
      naturality U V ψ := by
        ext x
        exact ConcreteCategory.congr_hom (h.hom.naturality ψ) x }
  refine ⟨⟨τ⟩, ?_⟩
  apply Sheaf.hom_ext
  ext U x
  rfl

end AlgebraicGeometry.Etale
