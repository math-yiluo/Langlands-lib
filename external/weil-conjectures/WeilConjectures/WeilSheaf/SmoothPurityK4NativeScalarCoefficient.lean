/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityChangeCoefficientWeilLaw
public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarTransport
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientFactor
public import WeilConjectures.WeilSheaf.SmoothPurityScalarCoefficientTransport
import WeilConjectures.Tactic.ExactModProofs

/-! # Changing coefficients in a scalar Frobenius relation -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.K4Native

open CondensedRing Scheme

/-- The Frobenius descent component with its source normalized in the interface. -/
noncomputable def scalarFrobeniusIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.upperStar Λ f.geometricGaloisFrobenius.asIso.hom).obj
        ((CondensedRing.upperStar Λ f.geometricFiberProj).obj M) ≅
      (CondensedRing.upperStar Λ f.geometricFiberProj).obj M :=
  CategoryTheory.K4Native.scalarComponent
    (CondensedRing.upperStar Λ f.geometricFiberProj)
    (CondensedRing.upperStar Λ f.geometricGaloisFrobenius.asIso.hom)
    (geometricFiberProjUpperStarFrobeniusIso Λ f) M

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
    c • ((scalarFrobeniusIso Λ' f
          ((Mod.extendScalars (coefficientMap a X)).obj M)).hom ≫
        (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M N e).hom) =
      (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧.map
          (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M N e).hom ≫
        (scalarFrobeniusIso Λ' f
          ((Mod.extendScalars (coefficientMap a X)).obj N)).hom := by
  exact CategoryTheory.K4Native.scalarFunctor_coefficient (f.geometricFiberProj)^*⟦Λ⟧
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

/-- The normalized trivialization obeys the same scalar Frobenius law. -/
theorem purityChangeCoefficientTrivialization_weil
    (e₁ : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _))
    (he : (f.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map e₁.hom.hom ≫
        (purityAbelianFrobeniusFactorIso f).hom.app (condensedRingObj Λ X) =
      c • ((purityAbelianFrobeniusFactorIso f).hom.app M.X ≫ e₁.hom.hom)) :
    c • ((scalarFrobeniusIso Λ' f
          ((Mod.extendScalars (coefficientMap a X)).obj M)).hom ≫
        (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁).hom) =
      (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧.map
          (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁).hom ≫
        (scalarFrobeniusIso Λ' f (𝟙_ _)).hom := by
  have h := CategoryTheory.K4Native.scalarDatum_postcomposeIso (f.geometricFiberProj)^*⟦Λ'⟧
    (f.geometricGaloisFrobenius.asIso.hom)^*⟦Λ'⟧
    (geometricFiberProjUpperStarFrobeniusIso Λ' f)
    (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M (𝟙_ _) e₁)
    (purityCoefficientUnitIso Λ a X)
    (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁)
    (purityChangeCoefficientTrivialization_eq a f M e₁) c
    (purityChangeCoefficientPullbackIso_weil a f M (𝟙_ _) e₁ c he)
  dsimp +instances only [scalarFrobeniusIso, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end ScalarRelation

end AlgebraicGeometry.ProEtale.K4Native
