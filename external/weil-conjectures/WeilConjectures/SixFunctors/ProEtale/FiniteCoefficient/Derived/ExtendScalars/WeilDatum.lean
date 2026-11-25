/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilDatum

/-!
# Scalar extension of Weil data and of local Frobenii

Let `R → S` be a homomorphism of commutative rings and `Ψ = - ⊗ᴸ_R S` derived scalar extension
of pro-étale sheaves (blueprint `prose-03-02`). A Weil datum `φ : Lg^* K ⟶ K` over
`R` induces the Weil datum
```
φ_S : Lg^* Ψ K ≅ Ψ Lg^* K --Ψ φ--> Ψ K
```
over `S` (`AlgebraicGeometry.ProEtale.extendScalarsWeilDatum`), through the commutation
`Ψ Lg^* ≅ Lg^* Ψ` of `AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`. This
construction commutes with the operations of `WeilConjectures.SixFunctors.ProEtale.
FiniteCoefficient.Derived.WeilDatum`: iterates, pullbacks and local Frobenii. In particular the
identification `Lx^* Ψ K ≅ Ψ Lx^* K` of the geometric stalks intertwines the local Frobenius of
`(Ψ K, φ_S)` with the scalar extension of the local Frobenius of `(K, φ)` (part of blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`).

## Main statements

- `AlgebraicGeometry.ProEtale.extendScalarsWeilDatum_weilDatumIterate`: `(φ_S)_m = (φ_m)_S`.
- `AlgebraicGeometry.ProEtale.upperStarWeilDatum_extendScalarsWeilDatum_comp`: the
  identification `Lx^* Ψ K ≅ Ψ Lx^* K` is a morphism of Weil data.
- `AlgebraicGeometry.ProEtale.stalkFrobenius_extendScalarsWeilDatum_comp`: it intertwines the
  local Frobenii.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]

variable {R S} in
/-- The scalar extension `φ_S : Lg^* Ψ K ≅ Ψ Lg^* K --Ψ φ--> Ψ K` of a Weil datum
`φ : Lg^* K ⟶ K`, where `Ψ = - ⊗ᴸ_R S`. -/
noncomputable def extendScalarsWeilDatum {X : Scheme.{u}} {g : X ⟶ X}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (φ : L((g)^*[ModuleCat.{u + 1} R]).obj K ⟶ K) :
    L((g)^*[ModuleCat.{u + 1} S]).obj (L(sheafExtendScalars (algebraMap R S) X).obj K) ⟶
      L(sheafExtendScalars (algebraMap R S) X).obj K :=
  (leftDerivedUpperStarExtendScalarsIso R S g).hom.app K ≫
    L(sheafExtendScalars (algebraMap R S) X).map φ

variable {X : Scheme.{u}} {g : X ⟶ X}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}

/-- Scalar extension commutes with iterating Weil data: `(φ_S)_m = (φ_m)_S`. -/
theorem extendScalarsWeilDatum_weilDatumIterate
    (φ : L((g)^*[ModuleCat.{u + 1} R]).obj K ⟶ K) (m : ℕ) :
    extendScalarsWeilDatum (weilDatumIterate φ m) =
      weilDatumIterate (extendScalarsWeilDatum (S := S) φ) m := by
  induction m with
  | zero =>
    exact leftDerivedUpperStarExtendScalarsIso_hom_app_id R S K
  | succ m ih =>
    rw [weilDatumIterate_succ, weilDatumIterate_succ, ← ih]
    simp only [extendScalarsWeilDatum, Functor.map_comp]
    rw [leftDerivedUpperStarExtendScalarsIso_hom_app_congr_assoc,
      leftDerivedUpperStarExtendScalarsIso_hom_app_comp_assoc]
    have hn := (leftDerivedUpperStarExtendScalarsIso R S g).hom.naturality
      (weilDatumIterate φ m)
    dsimp at hn
    rw [← reassoc_of% hn]
    simp

variable {P : Scheme.{u}} {e : P ⟶ P} {x : P ⟶ X}

/-- Scalar extension commutes with the pullback of Weil data: the identification
`Lx^* Ψ K ≅ Ψ Lx^* K` is a morphism from the Weil datum induced on `Lx^* Ψ K` by `φ_S` to the
scalar extension of the Weil datum induced on `Lx^* K` by `φ`. -/
theorem upperStarWeilDatum_extendScalarsWeilDatum_comp (h : e ≫ x = x ≫ g)
    (φ : L((g)^*[ModuleCat.{u + 1} R]).obj K ⟶ K) :
    upperStarWeilDatum h (extendScalarsWeilDatum (S := S) φ) ≫
        (leftDerivedUpperStarExtendScalarsIso R S x).hom.app K =
      L((e)^*[ModuleCat.{u + 1} S]).map ((leftDerivedUpperStarExtendScalarsIso R S x).hom.app K) ≫
        extendScalarsWeilDatum (upperStarWeilDatum h φ) := by
  have hc := leftDerivedUpperStarExtendScalarsIso_hom_app_comp R S x e K
  have hc' := leftDerivedUpperStarExtendScalarsIso_hom_app_comp R S g x K
  have hn := (leftDerivedUpperStarExtendScalarsIso R S x).hom.naturality φ
  dsimp at hn
  have hΨ : L(sheafExtendScalars (algebraMap R S) P).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) e x).hom.app K) ≫
      L(sheafExtendScalars (algebraMap R S) P).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) e x).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} S) e x).hom.app _)]
  simp only [upperStarWeilDatum, extendScalarsWeilDatum, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hc, reassoc_of% hΨ, leftDerivedUpperStarExtendScalarsIso_hom_app_congr_assoc,
    reassoc_of% hc', ← hn]

/-- Scalar extension commutes with the local Frobenius: at a point `x` fixed by `g`, the
identification `Lx^* Ψ K ≅ Ψ Lx^* K` of the stalk complexes carries the local Frobenius of
`(Ψ K, φ_S)` to the scalar extension of the local Frobenius of `(K, φ)`. -/
theorem stalkFrobenius_extendScalarsWeilDatum_comp (hx : x ≫ g = x)
    (φ : L((g)^*[ModuleCat.{u + 1} R]).obj K ⟶ K) :
    stalkFrobenius hx (extendScalarsWeilDatum (S := S) φ) ≫
        (leftDerivedUpperStarExtendScalarsIso R S x).hom.app K =
      (leftDerivedUpperStarExtendScalarsIso R S x).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) P).map (stalkFrobenius hx φ) := by
  have hi := leftDerivedUpperStarExtendScalarsIso_hom_app_id R S
    (L((x)^*[ModuleCat.{u + 1} R]).obj K)
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} S) P).inv.naturality
    ((leftDerivedUpperStarExtendScalarsIso R S x).hom.app K)
  dsimp at hn
  have hi' : (leftDerivedUpperStarId (ModuleCat.{u + 1} S) P).inv.app
        (L(sheafExtendScalars (algebraMap R S) P).obj (L((x)^*[ModuleCat.{u + 1} R]).obj K)) ≫
      (leftDerivedUpperStarExtendScalarsIso R S (𝟙 P)).hom.app
        (L((x)^*[ModuleCat.{u + 1} R]).obj K) =
      L(sheafExtendScalars (algebraMap R S) P).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) P).inv.app
          (L((x)^*[ModuleCat.{u + 1} R]).obj K)) := by
    rw [← cancel_mono (L(sheafExtendScalars (algebraMap R S) P).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) P).hom.app
        (L((x)^*[ModuleCat.{u + 1} R]).obj K))), Category.assoc, hi, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    exact (CategoryTheory.Functor.map_id L(sheafExtendScalars (algebraMap R S) P) _).symm
  rw [stalkFrobenius, Category.assoc, upperStarWeilDatum_extendScalarsWeilDatum_comp,
    ← reassoc_of% hn, stalkFrobenius, Functor.map_comp, extendScalarsWeilDatum,
    reassoc_of% hi']

end AlgebraicGeometry.ProEtale
