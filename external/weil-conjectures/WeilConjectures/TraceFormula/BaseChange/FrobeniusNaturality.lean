/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChange.WeilObject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FrobeniusNaturality

/-!
# Naturality of the `#k ^ N`-power Frobenius trivialization

Let `k` be a finite field, `f : X ⟶ Y` a morphism of schemes over `k` and `F_X`, `F_Y` the
`#k ^ N`-power Frobenii, so that `f ≫ F_Y = F_X ≫ f`. The trivializations `κ_X : F_X^* ≅ 𝟭`,
`κ_Y : F_Y^* ≅ 𝟭` of the pullbacks of `ℚ̲̄_ℓ`-modules
(`ProEtale.CondensedRing.upperStarFrobeniusIso`) are compatible with `f^*`:
```
(f ≫ F_Y)^* M ≅ f^* F_Y^* M --f^* κ_Y--> f^* M
     ‖                                     ‖
(F_X ≫ f)^* M ≅ F_X^* f^* M --κ_X------> f^* M
```
and so are their derived versions (`ProEtale.CondensedRing.leftDerivedUpperStarFrobeniusIso`).

## Main results

- `ProEtale.CondensedRing.upperStarComp_hom_app_comp_map_upperStarFrobeniusIso_hom_app`: the
  underived compatibility.
- `leftDerivedUpperStarComp_hom_app_comp_map_leftDerivedUpperStarFrobeniusIso_hom_app`:
  the derived compatibility.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- the rewrites of `eqToHom` in the categories of module objects are slow to elaborate
/-- Compatibility of trivializations of pullbacks with `g^*` is invariant under transporting the
trivializations along equalities `F_X = F_X'`, `F_T = F_T'` of the endomorphisms. -/
lemma upperStarComp_hom_app_comp_map_upperStarEqToIso_trans_hom_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T X : Scheme.{u}} (g : T ⟶ X) {FX FX' : X ⟶ X} {FT FT' : T ⟶ T} (eX : FX = FX')
    (eT : FT = FT') (h : g ≫ FX = FT ≫ g) (h' : g ≫ FX' = FT' ≫ g) (κX : (FX')^*⟦Λ⟧ ≅ 𝟭 _)
    (κT : (FT')^*⟦Λ⟧ ≅ 𝟭 _)
    (hκ : ∀ M, (upperStarComp Λ g FX').hom.app M ≫ (g)^*⟦Λ⟧.map (κX.hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) h') ≫ (upperStarComp Λ FT' g).hom.app M ≫
        κT.hom.app ((g)^*⟦Λ⟧.obj M))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ g FX).hom.app M ≫
        (g)^*⟦Λ⟧.map ((upperStarEqToIso Λ eX ≪≫ κX).hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) h) ≫ (upperStarComp Λ FT g).hom.app M ≫
        (upperStarEqToIso Λ eT ≪≫ κT).hom.app ((g)^*⟦Λ⟧.obj M) := by
  rw [upperStarEqToIso_trans_hom_app, upperStarEqToIso_trans_hom_app]
  subst eX
  subst eT
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]
  exact hκ M

variable {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Over (Spec (.of k))}

/-- A morphism `f` of schemes over `k` commutes with the `#k ^ N`-power Frobenii:
`f ≫ F_Y^N = F_X^N ≫ f`. -/
lemma left_comp_frobeniusIterate_overFrobenius_left (f : X ⟶ Y) (N : ℕ) :
    f.left ≫ (frobeniusIterate (overFrobenius Y) N).left =
      (frobeniusIterate (overFrobenius X) N).left ≫ f.left := by
  rw [← Over.comp_left, ← Over.comp_left,
    frobeniusIterate_comp_of_comp (comp_overFrobenius f).symm N]

/-- **Naturality of the `#k ^ N`-power Frobenius trivialization**: for a morphism `f : X ⟶ Y`
of schemes over the finite field `k`, the two identifications `(f ≫ F_Y)^* M ≅ f^* M` through
`κ_Y` and through `κ_X` agree. -/
theorem upperStarComp_hom_app_comp_map_upperStarFrobeniusIso_hom_app (f : X ⟶ Y) (N : ℕ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left
        (frobeniusIterate (overFrobenius Y) N).left).hom.app M ≫
        (f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarFrobeniusIso ℓ Y N).hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (left_comp_frobeniusIterate_overFrobenius_left f N)) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ)
          (frobeniusIterate (overFrobenius X) N).left f.left).hom.app M ≫
          (upperStarFrobeniusIso ℓ X N).hom.app
            ((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) := by
  rw [upperStarFrobeniusIso_eq, upperStarFrobeniusIso_eq]
  exact upperStarComp_hom_app_comp_map_upperStarEqToIso_trans_hom_app
    (Profinite.padicAlgClRingObj ℓ) f.left
    (frobeniusIterate_overFrobenius_left Y N) (frobeniusIterate_overFrobenius_left X N)
    (left_comp_frobeniusIterate_overFrobenius_left f N)
    (comp_iterateFrobenius (FiniteField.ringChar_prime (k := k)) f.left
      (natCast_ringChar_left_eq_zero Y) (natCast_ringChar_left_eq_zero X)
      (FiniteField.frobeniusExponent k * N))
    (upperStarIterateFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      (FiniteField.ringChar_prime (k := k)) (natCast_ringChar_left_eq_zero Y)
      (FiniteField.frobeniusExponent k * N))
    (upperStarIterateFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      (FiniteField.ringChar_prime (k := k)) (natCast_ringChar_left_eq_zero X)
      (FiniteField.frobeniusExponent k * N))
    (upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app
      (Profinite.padicAlgClRingObj ℓ) (FiniteField.ringChar_prime (k := k))
      (natCast_ringChar_left_eq_zero Y) (natCast_ringChar_left_eq_zero X)
      (FiniteField.frobeniusExponent k * N) f.left) M

-- the instances of the general lemma are found for each of the categories of module objects
/-- **Naturality of the derived `#k ^ N`-power Frobenius trivialization**: for a morphism
`f : X ⟶ Y` of schemes over the finite field `k`, the two identifications
`L(f ≫ F_Y)^* M ≅ Lf^* M` through `Lκ_Y` and through `Lκ_X` agree. -/
theorem leftDerivedUpperStarComp_hom_app_comp_map_leftDerivedUpperStarFrobeniusIso_hom_app
    (f : X ⟶ Y) (N : ℕ)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))) :
    (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj.{u} ℓ) f.left
        (frobeniusIterate (overFrobenius Y) N).left).hom.app M ≫
        L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((leftDerivedUpperStarFrobeniusIso ℓ Y N).hom.app M) =
      eqToHom (congrArg (fun s ↦ L((s)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M)
          (left_comp_frobeniusIterate_overFrobenius_left f N)) ≫
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj.{u} ℓ)
          (frobeniusIterate (overFrobenius X) N).left f.left).hom.app M ≫
          (leftDerivedUpperStarFrobeniusIso ℓ X N).hom.app
            (L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M) :=
  leftDerivedUpperStarComp_hom_app_comp_map_leftDerivedFunctorIdIso
    (Profinite.padicAlgClRingObj ℓ) f.left (left_comp_frobeniusIterate_overFrobenius_left f N)
    (upperStarFrobeniusIso ℓ Y N) (upperStarFrobeniusIso ℓ X N)
    (upperStarComp_hom_app_comp_map_upperStarFrobeniusIso_hom_app ℓ f N) M

end AlgebraicGeometry.ProEtale.CondensedRing
