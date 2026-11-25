/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization

/-! # Tor vanishing over a localized base ring

Source: Stacks Project, Tag 0B67, the base-ring localization part of (1) to (2).
(blueprint: lem-pc-tor-vanishing-localized-base).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Tor vanishing after scalar restriction implies Tor vanishing over the localization.
Source: Stacks Project, Tag 0B67, `lemma-tor-amplitude-localization`, the
base-ring localization step in (1) to (2), expanded here for modules.

Proof: let P be an A-projective resolution of the restriction of L. Extend scalars
along A to A'. Localization is flat, so A' tensor_A P remains an exact resolution
by projective A'-modules. The augmentation targets A' tensor_A L, canonically
isomorphic to L: every element of the localization submonoid already acts invertibly
on an A'-module, so the counit is invertible. Tensor associativity identifies
(A' tensor_A P) tensor_A' M with P tensor_A M. This is an identification of chain
complexes after restriction to A and therefore of their homology. The latter
homology is the Tor' object in the hypothesis and is zero. Restriction of scalars
reflects zero objects, giving the required zero Tor' object over A'.
This includes j = 0, S = {1}, and the zero localization; no finite generation
hypothesis is used, and both L and M have their original A'-module structures.
(blueprint: lem-pc-tor-vanishing-localized-base). -/
theorem isZero_tor_of_restrictScalars_localization
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    (S : Submonoid A) [IsLocalization S A']
    (L M : ModuleCat.{u} A') (j : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars (algebraMap A A')).obj L)).obj
        ((restrictScalars (algebraMap A A')).obj M))) :
    IsZero (((Tor' (ModuleCat.{u} A') j).obj L).obj M) := by
  -- Restricting scalar extension is tensoring with the flat localized ring.
  let R := restrictScalars (algebraMap A A')
  let E := extendScalars (algebraMap A A')
  let : E.Additive := by
    constructor
    intro X Y f g
    apply ExtendScalars.hom_ext
    intro x
    simp [E, TensorProduct.tmul_add]
  let : E.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj (algebraMap A A'))
  let : Module.Flat A A' := IsLocalization.flat A' S
  let : Module.Flat A (R.obj (of A' A')) := Module.Flat.of_linearEquiv
    ({ __ := AddEquiv.refl A', map_smul' := fun a x ↦ by
        exact (Algebra.smul_def a (show A' from x)).symm } : R.obj (of A' A') ≃ₗ[A] A')
  let : PreservesFiniteLimits (E ⋙ R) :=
    inferInstanceAs (PreservesFiniteLimits
      (MonoidalCategory.tensorLeft (R.obj (of A' A'))))
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E R
  -- The localization counit identifies the extended restricted module with L.
  let e : E.obj (R.obj L) ≅ L := by
    have hloc := ‹IsLocalization S A'›
    letI alg : Algebra A A' := (algebraMap A A').toAlgebra
    let : IsLocalization S A' := ⟨hloc.toIsLocalizationMap⟩
    let : IsScalarTower A A' (R.obj L) := IsScalarTower.of_compHom A A' L
    exact (IsLocalization.moduleLid S A' (R.obj L)).toModuleIso
  -- Tensor associativity is natural before taking homology.
  let eT : E ⋙ MonoidalCategory.tensorRight M ⋙ R ≅
      MonoidalCategory.tensorRight (R.obj M) := by
    letI alg : Algebra A A' := (algebraMap A A').toAlgebra
    let : IsScalarTower A A' (R.obj M) := IsScalarTower.of_compHom A A' M
    refine NatIso.ofComponents (fun X ↦ ?_) ?_
    · letI : Module A (TensorProduct A' (E.obj X) M) :=
        Module.compHom _ (algebraMap A A')
      let : IsScalarTower A A' (TensorProduct A' (E.obj X) M) :=
        IsScalarTower.of_compHom A A' _
      exact ((TensorProduct.comm A' (E.obj X) M ≪≫ₗ
        TensorProduct.AlgebraTensorModule.cancelBaseChange A A' A' (R.obj M) X).restrictScalars A
        ≪≫ₗ TensorProduct.comm A (R.obj M) X).toModuleIso
    · intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x m =>
        induction x using TensorProduct.inductionOn with
        | tmul a x => rfl
        | add x y hx hy => simp_all [TensorProduct.add_tmul]
      | add x y hx hy => simp_all
  -- Compute both derived tensor functors on P and its scalar extension Q.
  let P := projectiveResolution (R.obj L)
  let Q := E.mapProjectiveResolution P
  let T := MonoidalCategory.tensorRight M
  let G := MonoidalCategory.tensorRight (R.obj M)
  let C := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let eC : (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ R))
      (ComplexShape.down ℕ)).app Q.complex ≪≫
    (Functor.mapHomologicalComplexCompIso eT (ComplexShape.down ℕ)).app P.complex
  let eH : ((R.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology j ≅
      R.obj (C.homology j) := (C.sc j).mapHomologyIso R
  have hz : IsZero (R.obj ((T.leftDerived j).obj (E.obj (R.obj L)))) := by
    apply IsZero.of_iso h
    exact R.mapIso (Q.isoLeftDerivedObj T j) ≪≫ eH.symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) j).mapIso eC ≪≫
      (P.isoLeftDerivedObj G j).symm
  -- A faithful additive functor reflects a zero identity, hence a zero object.
  have hz' : IsZero ((T.leftDerived j).obj (E.obj (R.obj L))) := by
    rw [IsZero.iff_id_eq_zero]
    apply R.map_injective
    simpa using hz.eq_of_src (R.map (𝟙 _)) 0
  exact IsZero.of_iso hz' ((T.leftDerived j).mapIso e).symm

end ModuleCat
