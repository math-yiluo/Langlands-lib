/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarWeilLaw
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientFactor
public import WeilConjectures.WeilSheaf.SmoothPurityScalarCoefficientTransport
import WeilConjectures.Tactic.ExactModProofs

/-! # Changing coefficients in a scalar Frobenius relation -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

section Transport

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- **The Weil structures of pulled-back module objects are compatible with the extension of
scalars** along a change of coefficients `a : Λ ⟶ Λ'`: through the (Pull) isomorphisms
`Ext (p^* M) ≅ p^* (Ext M)` and `Ext (Fr^* N) ≅ Fr^* (Ext N)`, the extension of scalars of the
Weil structure `Fr^* p^* M ≅ p^* M` is the Weil structure of `p^* (Ext M)`. -/
lemma purity_extendScalars_map_geometricFiberProjUpperStarFrobeniusIso_hom_app_comp_pullIso_hom_app
    (M : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    (Mod.extendScalars (coefficientMap a f.geometricFiber)).map
          ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M) ≫
        (pullIso a f.geometricFiberProj).hom.app M =
      (pullIso a f.geometricGaloisFrobenius.asIso.hom).hom.app ((f.geometricFiberProj)^*⟦Λ⟧.obj M) ≫
        (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧.map
            ((pullIso a f.geometricFiberProj).hom.app M) ≫
          (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
            ((Mod.extendScalars (coefficientMap a X₀)).obj M) := by
  have h := purity_extendScalars_map_factor_hom_comp_pullIso a f.geometricFiberProj
    f.geometricGaloisFrobenius.asIso.hom f.geometricGaloisFrobenius_hom_comp_geometricFiberProj M
  simp only [purityModuleFactorIso, geometricFiberProjUpperStarFrobeniusIso] at h ⊢
  exact_mod_proofs h

/-- The Weil structure of `p^* (Ext M)`, expressed through the Weil structure of `p^* M` and
the (Pull) isomorphisms. -/
lemma purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_extendScalars_obj
    (M : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
        ((Mod.extendScalars (coefficientMap a X₀)).obj M) =
      (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧.map
          ((pullIso a f.geometricFiberProj).inv.app M) ≫
        (pullIso a f.geometricGaloisFrobenius.asIso.hom).inv.app
            ((f.geometricFiberProj)^*⟦Λ⟧.obj M) ≫
          (Mod.extendScalars (coefficientMap a f.geometricFiber)).map
            ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M) ≫
          (pullIso a f.geometricFiberProj).hom.app M := by
  rw [purity_extendScalars_map_geometricFiberProjUpperStarFrobeniusIso_hom_app_comp_pullIso_hom_app,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Transport

section ScalarRelation

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))


variable (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (e : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
    ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj N)
  (c : ℤ)

/-- Changing coefficients preserves the scalar relation of an underlying trivialization. -/
theorem purityChangeCoefficientPullbackIso_weil
    (he : (f.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map e.hom.hom ≫
        (purityAbelianFrobeniusFactorIso f).hom.app N.X =
      c • ((purityAbelianFrobeniusFactorIso f).hom.app M.X ≫ e.hom.hom)) :
    c • ((geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
          ((Mod.extendScalars (coefficientMap a X)).obj M) ≫
        (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M N e).hom) =
      (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧.map
          (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M N e).hom ≫
        (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
          ((Mod.extendScalars (coefficientMap a X)).obj N) := by
  exact purity_scalarFunctor_coefficient (f.geometricFiberProj)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X))
    (Mod.extendScalars (coefficientMap a f.geometricFiber)) (f.geometricFiberProj)^*⟦Λ'⟧
    (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ⟧ (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧
    (pullIso a f.geometricGaloisFrobenius.asIso.hom) (pullIso a f.geometricFiberProj)
    (geometricFiberProjUpperStarFrobeniusIso Λ f)
    (geometricFiberProjUpperStarFrobeniusIso Λ' f) M N
    (fun K ↦
      purity_extendScalars_map_geometricFiberProjUpperStarFrobeniusIso_hom_app_comp_pullIso_hom_app
        a f K)
    (purityExtendPullbackIso Λ f.geometricFiberProj M N e) c
    (purityExtendPullbackIso_weil Λ f M N e c he)

/-- Unfold the trivialization at the isomorphism level. -/
lemma purityChangeCoefficientTrivialization_eq
    (e₁ : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _)) :
    purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁ =
      purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M (𝟙_ _) e₁ ≪≫
        (f.geometricFiberProj)^*⟦Λ'⟧.mapIso (purityCoefficientUnitIso Λ a X) := rfl

/-- The normalized trivialization obeys the same scalar Frobenius law. -/
theorem purityChangeCoefficientTrivialization_weil
    (e₁ : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _))
    (he : (f.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map e₁.hom.hom ≫
        (purityAbelianFrobeniusFactorIso f).hom.app (condensedRingObj Λ X) =
      c • ((purityAbelianFrobeniusFactorIso f).hom.app M.X ≫ e₁.hom.hom)) :
    c • ((geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
          ((Mod.extendScalars (coefficientMap a X)).obj M) ≫
        (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁).hom) =
      (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧.map
          (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁).hom ≫
        (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app (𝟙_ _) := by
  have h := purity_scalarDatum_postcomposeIso (f.geometricFiberProj)^*⟦Λ'⟧
    (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧
    (geometricFiberProjUpperStarFrobeniusIso Λ' f)
    (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M (𝟙_ _) e₁)
    (purityCoefficientUnitIso Λ a X)
    (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁)
    (purityChangeCoefficientTrivialization_eq a f M e₁) c
    (purityChangeCoefficientPullbackIso_weil a f M (𝟙_ _) e₁ c he)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
  cast_proofs h

end ScalarRelation

end AlgebraicGeometry.ProEtale.CondensedRing
