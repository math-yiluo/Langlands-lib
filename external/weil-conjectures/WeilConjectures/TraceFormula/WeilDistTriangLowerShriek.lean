/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.WeilDistTriang
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Connecting
public import WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek

/-!

# The lower shriek of Weil objects preserves distinguished triangles

Let `f : X ⟶ Y` be a morphism with automorphisms `e_X`, `e_Y` and `e_X ≫ f = f ≫ e_Y`. The lower
shriek of Weil objects `Rf_!^Weil` (`ProEtale.CondensedRing.weilLowerShriek`) sends
distinguished triangles of Weil objects to distinguished triangles of Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y)

variable {eX eY} in
/-- The connecting morphism transported through the ambient lower shriek `R(f)_!` and its
comparison isomorphism is the one transported through the lift of `Rf_!` of
`ProEtale.CondensedRing.shiftLift_boundedConstructibleLowerShriek`. -/
lemma connectingOfIso_boundedConstructibleLowerShriek (f : X ⟶ Y)
    {a c : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj c ⟶
      (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          X.left)).ι.obj a)) :
    haveI := HasCompactification.of_over f
    connectingOfIso (boundedConstructibleLowerShriek ℓ f)
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
        (R(f.left)_!⟦Profinite.padicAlgClRingObj ℓ⟧)
        (boundedConstructibleLowerShriekCompatibility ℓ f) δ =
      Functor.ShiftLift.connecting
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
        (boundedConstructibleLowerShriek ℓ f) δ := by
  have := HasCompactification.of_over f
  unfold connectingOfIso Functor.ShiftLift.connecting
  -- the components agree definitionally; comparing them one by one avoids unfolding the functors
  exact congrArg₂ (· ≫ ·) (congrArg (fun t ↦ NatTrans.app t c) rfl)
    (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·)
      (congrArg (fun t ↦ NatTrans.app t _) rfl)
      (congrArg (fun t ↦ (shiftFunctor _ (1 : ℤ)).map (NatTrans.app t a)) rfl)))

/-- The structure morphism of the lower shriek of a Weil object is the compact-support base
change followed by the lower shriek of the structure morphism. -/
lemma weilLowerShriek_obj_str_hom {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    (K : WeilBoundedConstructible ℓ eX.hom) :
    ((weilLowerShriek ℓ eX eY hf).obj K).str.hom =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (weilFrobeniusSquare eX eY hf)).app
        K.carrier ≫ (boundedConstructibleLowerShriek ℓ f).map
          K.str.hom := by
  rw [weilLowerShriek_obj_str]
  rfl

/-- The image under `Rf_!` of a connecting morphism `δ` commuting with the Frobenius structures
of Weil objects `A` and `C` commutes with the Frobenius structures of `Rf_! A` and `Rf_! C`: the
compact-support base change commutes with the connecting morphisms
(`ProEtale.CondensedRing.commConnecting_boundedConstructibleLowerShriekBaseChange_padicAlgCl`). -/
lemma weilLowerShriek_str_comp_connecting {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    {A C : WeilBoundedConstructible ℓ eX.hom}
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
      C.carrier ⟶ (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          A.carrier))
    (hφ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
        C.str.hom ≫ δ = Functor.ShiftLift.connecting
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom) δ ≫
        (shiftFunctor _ (1 : ℤ)).map
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
            A.str.hom)) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι.map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (weilFrobeniusSquare eX eY hf)).app
          C.carrier ≫
          (boundedConstructibleLowerShriek ℓ f).map C.str.hom) ≫
        Functor.ShiftLift.connecting
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
          (boundedConstructibleLowerShriek ℓ f) δ =
      Functor.ShiftLift.connecting
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eY.hom)
          (Functor.ShiftLift.connecting
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
            (boundedConstructibleLowerShriek ℓ f) δ) ≫
        (shiftFunctor _ (1 : ℤ)).map
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι.map
            ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
              (weilFrobeniusSquare eX eY hf)).app A.carrier ≫
              (boundedConstructibleLowerShriek ℓ f).map
                A.str.hom)) := by
  have hBC := (commConnecting_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (weilFrobeniusSquare eX eY hf)).comm δ
  rw [Functor.ShiftLift.connecting_comp, Functor.ShiftLift.connecting_comp] at hBC
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.ShiftLift.connecting_map_comp, hφ, Functor.ShiftLift.connecting_comp_shift_map,
    ← Category.assoc]
  exact (hBC =≫ _).trans (Category.assoc _ _ _)

/-- **The lower shriek of Weil objects preserves distinguished triangles**: `Rf_!` is a
triangulated functor (`R(f)_!` on the ambient derived categories commutes with the shifts and is
triangulated), and the compact-support base change isomorphism giving the Frobenius structure of
`Rf_!^Weil` commutes with the connecting morphisms
(`ProEtale.CondensedRing.commConnecting_boundedConstructibleLowerShriekBaseChange_padicAlgCl`),
so the image of the connecting morphism commutes with the Frobenius structures. -/
theorem WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map {f : X ⟶ Y}
    (hf : eX.hom ≫ f = f ≫ eY.hom) {A B C : WeilBoundedConstructible ℓ eX.hom} {a : A ⟶ B}
    {b : B ⟶ C} (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    WeilBoundedConstructible.IsDistTriang ℓ ((weilLowerShriek ℓ eX eY hf).map a)
      ((weilLowerShriek ℓ eX eY hf).map b) := by
  obtain ⟨δ, hT, hφ⟩ := h
  have := HasCompactification.of_over f
  refine ⟨connectingOfIso (boundedConstructibleLowerShriek ℓ f)
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    (R(f.left)_!⟦Profinite.padicAlgClRingObj ℓ⟧)
    (boundedConstructibleLowerShriekCompatibility ℓ f) δ,
    distinguished_of_iso (boundedConstructibleLowerShriek ℓ f)
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
      (R(f.left)_!⟦Profinite.padicAlgClRingObj ℓ⟧)
      (boundedConstructibleLowerShriekCompatibility ℓ f) hT, ?_⟩
  rw [weilLowerShriek_obj_str_hom, weilLowerShriek_obj_str_hom,
    connectingOfIso_boundedConstructibleLowerShriek]
  exact weilLowerShriek_str_comp_connecting ℓ eX eY hf δ hφ

end AlgebraicGeometry.ProEtale.CondensedRing
