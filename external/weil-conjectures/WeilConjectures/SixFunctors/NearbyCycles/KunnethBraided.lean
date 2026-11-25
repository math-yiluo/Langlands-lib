/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided

/-!

# The Künneth map of nearby cycles is symmetric

The lax tensor map `μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` of the derived pushforward commutes with
the braidings (`ProEtale.CondensedRing.lowerStarTensorMap'_braiding`), since the monoidal
structure of the derived pullback does
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_braiding`).
Hence so does the lax tensor map of nearby cycles
(`ProEtale.CondensedRing.NearbyCyclesModel.tensorMap_braiding`), and the Künneth map of nearby
cycles is symmetric: exchanging the two factors of a product exchanges the Künneth maps up to the
braidings (`ProEtale.CondensedRing.NearbyCyclesModel.braiding_comp_kunnethMap`).

The braiding of the derived categories is `DerivedCategory.braidedCategory'`, used as a local
instance.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [local instance] DerivedCategory.braidedCategory'

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The comultiplication of the derived pullback commutes with the braidings. -/
@[reassoc]
lemma δ_leftDerivedUpperStar_braiding {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map (β_ K M).hom ≫ Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) M K =
      Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) K M ≫
        (β_ (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj M)).hom :=
  leftDerivedUpperStarTensor_braiding Λ f K M

/-- The multiplication of the derived pullback commutes with the braidings. -/
@[reassoc]
lemma μ_leftDerivedUpperStar_braiding {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    Functor.LaxMonoidal.μ L((f)^*⟦Λ⟧) K M ≫ L((f)^*⟦Λ⟧).map (β_ K M).hom =
      (β_ (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj M)).hom ≫
        Functor.LaxMonoidal.μ L((f)^*⟦Λ⟧) M K := by
  rw [← cancel_epi (Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) K M), Functor.Monoidal.δ_μ_assoc,
    ← δ_leftDerivedUpperStar_braiding_assoc, Functor.Monoidal.δ_μ, Category.comp_id]

/-- **The lax tensor map of the derived pushforward commutes with the braidings.** -/
@[reassoc]
lemma lowerStarTensorMap'_braiding {U T : Scheme.{u}} (j : U ⟶ T)
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    (β_ (R((j)_*⟦Λ⟧).obj A) (R((j)_*⟦Λ⟧).obj B)).hom ≫ lowerStarTensorMap' Λ j B A =
      lowerStarTensorMap' Λ j A B ≫ R((j)_*⟦Λ⟧).map (β_ A B).hom := by
  apply ((derivedUpperStarLowerStarAdjunction Λ j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    lowerStarTensorMap'_comp_counit, Adjunction.counit_naturality]
  rw [δ_leftDerivedUpperStar_braiding_assoc, ← BraidedCategory.braiding_naturality,
    reassoc_of% (lowerStarTensorMap'_comp_counit Λ j A B)]
  rfl

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

private lemma tensorMap_braiding_aux {C D T S : Type*} [Category C] [Category D] [Category T]
    [Category S] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory T]
    [MonoidalCategory S] [BraidedCategory C] [BraidedCategory D] [BraidedCategory T]
    [BraidedCategory S] {E : C ⥤ D} {R : D ⥤ T} {I : T ⥤ S} [E.LaxMonoidal] [I.LaxMonoidal]
    (μR : ∀ U V, R.obj U ⊗ R.obj V ⟶ R.obj (U ⊗ V))
    (hE : ∀ A B, Functor.LaxMonoidal.μ E A B ≫ E.map (β_ A B).hom =
      (β_ (E.obj A) (E.obj B)).hom ≫ Functor.LaxMonoidal.μ E B A)
    (hR : ∀ U V, (β_ (R.obj U) (R.obj V)).hom ≫ μR V U =
      μR U V ≫ R.map (β_ U V).hom)
    (hI : ∀ U V, Functor.LaxMonoidal.μ I U V ≫ I.map (β_ U V).hom =
      (β_ (I.obj U) (I.obj V)).hom ≫ Functor.LaxMonoidal.μ I V U)
    (A B : C) :
    (β_ ((E ⋙ R ⋙ I).obj A) ((E ⋙ R ⋙ I).obj B)).hom ≫
        Functor.LaxMonoidal.μ I _ _ ≫ I.map (μR _ _ ≫ R.map (Functor.LaxMonoidal.μ E B A)) =
      (Functor.LaxMonoidal.μ I _ _ ≫ I.map (μR _ _ ≫ R.map (Functor.LaxMonoidal.μ E A B))) ≫
        (E ⋙ R ⋙ I).map (β_ A B).hom := by
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [← reassoc_of% (hI _ _), ← I.map_comp, Category.assoc, ← I.map_comp]
  congr 1
  rw [reassoc_of% (hR _ _), ← R.map_comp, Category.assoc, ← R.map_comp, hE]

/-- **The lax tensor map of nearby cycles commutes with the braidings.** -/
@[reassoc]
lemma tensorMap_braiding
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (β_ ((M.nearbyCycles Λ).obj A) ((M.nearbyCycles Λ).obj B)).hom ≫ M.tensorMap Λ B A =
      M.tensorMap Λ A B ≫ (M.nearbyCycles Λ).map (β_ A B).hom :=
  tensorMap_braiding_aux (E := L((M.ε)^*⟦Λ⟧)) (I := L((M.i)^*⟦Λ⟧))
    (lowerStarTensorMap' Λ M.j) (μ_leftDerivedUpperStar_braiding Λ M.ε)
    (lowerStarTensorMap'_braiding Λ M.j) (μ_leftDerivedUpperStar_braiding Λ M.i) A B

variable {Y Y' Z Z' : Scheme.{u}} {M} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- **The Künneth map of nearby cycles is symmetric**: exchanging the two factors of a product
exchanges the Künneth maps up to the braidings. -/
@[reassoc]
lemma braiding_comp_kunnethMap (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (β_ _ _).hom ≫ kunnethMap Λ φ₂ φ₁ B A =
      kunnethMap Λ φ₁ φ₂ A B ≫ (P.nearbyCycles Λ).map (β_ _ _).hom := by
  simp only [kunnethMap, Category.assoc, ← tensorMap_braiding]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rfl

/-- Exchanging the two factors of a product, the Künneth maps are simultaneously invertible,
after any functor. -/
lemma isIso_map_kunnethMap_iff_swap {D : Type*} [Category D]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj Λ Z')) ⥤ D)
    (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso (F.map (kunnethMap Λ φ₂ φ₁ B A)) ↔ IsIso (F.map (kunnethMap Λ φ₁ φ₂ A B)) := by
  have h := congrArg F.map (braiding_comp_kunnethMap Λ φ₁ φ₂ A B)
  rw [F.map_comp, F.map_comp] at h
  constructor
  · intro _
    have : IsIso (F.map (kunnethMap Λ φ₁ φ₂ A B) ≫
        F.map ((P.nearbyCycles Λ).map (β_ _ _).hom)) := h ▸ inferInstance
    exact IsIso.of_isIso_comp_right _ (F.map ((P.nearbyCycles Λ).map (β_ _ _).hom))
  · intro _
    have : IsIso (F.map (β_ _ _).hom ≫ F.map (kunnethMap Λ φ₂ φ₁ B A)) := h.symm ▸ inferInstance
    exact IsIso.of_isIso_comp_left (F.map (β_ _ _).hom) _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
