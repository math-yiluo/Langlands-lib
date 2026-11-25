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
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Restricting a Tor bound along a flat base map
Source: Stacks Project, Tag 069C, proof of (3) implies (1), flat base localization.
(blueprint: lem-pc-tor-vanishing-restriction-flat-base).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Flat scalar restriction transfers a fixed Tor vanishing test from scalar extension.
Source: Stacks Project, Tag 069C, proof of (3) implies (1).
Proof: Resolve N by projective A-modules and extend the resolution to B. Flatness makes
this an exact projective resolution of B tensor_A N. Tensor associativity identifies its
B-tensor with L, restricted to A, with the original resolution tensored over A with L.
Restriction is exact, so it commutes with homology. Symmetry of Tor lets these resolutions
of the second argument compute the first-variable Tor convention used here. Thus zero Tor
for (L, B tensor_A N) gives zero Tor for (L restricted to A, N). The argument works also
in degree zero, for N = 0, and for the zero algebra B; no faithfulness is needed.
(blueprint: lem-pc-tor-vanishing-restriction-flat-base). -/
theorem isZero_tor_restrictScalars_of_flat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (L : ModuleCat.{u} B) (N : ModuleCat.{u} A) (j : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} B) j).obj L).obj
      ((extendScalars (algebraMap A B)).obj N))) :
    IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars (algebraMap A B)).obj L)).obj N) := by
  let R := restrictScalars (algebraMap A B)
  let E := extendScalars (algebraMap A B)
  let : E.Additive := by
    constructor
    intro X Y f g
    apply ExtendScalars.hom_ext
    intro x
    simp [E, TensorProduct.tmul_add]
  let : E.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj (algebraMap A B))
  let : Module.Flat A (R.obj (of B B)) := Module.Flat.of_linearEquiv
    ({ __ := AddEquiv.refl B, map_smul' := fun a x ↦ by
        exact (Algebra.smul_def a (show B from x)).symm } : R.obj (of B B) ≃ₗ[A] B)
  let : PreservesFiniteLimits (E ⋙ R) :=
    inferInstanceAs (PreservesFiniteLimits
      (MonoidalCategory.tensorLeft (R.obj (of B B))))
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E R
  let eT : E ⋙ MonoidalCategory.tensorRight L ⋙ R ≅
      MonoidalCategory.tensorRight (R.obj L) := by
    letI alg : Algebra A B := (algebraMap A B).toAlgebra
    let : IsScalarTower A B (R.obj L) := IsScalarTower.of_compHom A B L
    refine NatIso.ofComponents (fun X ↦ ?_) ?_
    · letI : Module A (TensorProduct B (E.obj X) L) :=
        Module.compHom _ (algebraMap A B)
      let : IsScalarTower A B (TensorProduct B (E.obj X) L) :=
        IsScalarTower.of_compHom A B _
      exact ((TensorProduct.comm B (E.obj X) L ≪≫ₗ
        TensorProduct.AlgebraTensorModule.cancelBaseChange A B B (R.obj L) X).restrictScalars A
        ≪≫ₗ TensorProduct.comm A (R.obj L) X).toModuleIso
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
  let P := projectiveResolution N
  let Q := E.mapProjectiveResolution P
  let T := MonoidalCategory.tensorRight L
  let G := MonoidalCategory.tensorRight (R.obj L)
  let C := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let eC : (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ R))
      (ComplexShape.down ℕ)).app Q.complex ≪≫
    (Functor.mapHomologicalComplexCompIso eT (ComplexShape.down ℕ)).app P.complex
  let eH : ((R.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology j ≅
      R.obj (C.homology j) := (C.sc j).mapHomologyIso R
  obtain ⟨σB⟩ := nonempty_tor'_flip_iso B j
  have hz : IsZero ((T.leftDerived j).obj (E.obj N)) :=
    h.of_iso ((σB.app L).app (E.obj N)).symm
  have hzA : IsZero ((G.leftDerived j).obj N) := by
    apply IsZero.of_iso (R.map_isZero hz)
    exact (P.isoLeftDerivedObj G j) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) j).mapIso
        eC.symm ≪≫ eH ≪≫ (R.mapIso (Q.isoLeftDerivedObj T j)).symm
  obtain ⟨σA⟩ := nonempty_tor'_flip_iso A j
  exact hzA.of_iso ((σA.app (R.obj L)).app N)

end ModuleCat
