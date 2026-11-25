/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.CategoryTheory.Slice
/-! # The projection/counit calculation with pointwise scalar comparison inverses -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

/-- The evaluated squares used in the projection/counit calculation. Only the
three specified compact-support comparison components are inverted. The
exceptional-unit map is constrained by its own counit equation; no theta
compatibility is a field.
Source: finite-reduction proof Steps 3--4
(blueprint: lem-pur-projection-counit-pointwise-data). -/
structure ProjectionCounitData where
  C : Type (u + 1)
  D : Type (u + 1)
  E : Type (u + 1)
  F : Type (u + 1)
  [catC : Category.{u} C]
  [catD : Category.{u} D]
  [catE : Category.{u} E]
  [catF : Category.{u} F]
  [monC : MonoidalCategory C]
  [monD : MonoidalCategory D]
  [monE : MonoidalCategory E]
  [monF : MonoidalCategory F]
  [braidC : BraidedCategory C]
  [braidE : BraidedCategory E]
  FA : C ⥤ D
  FB : E ⥤ F
  QX : C ⥤ E
  QY : D ⥤ F
  U : C
  W : C
  V : E
  Z : E
  K : D
  eA : FA.obj W ⟶ 𝟙_ D
  eB : FB.obj Z ⟶ 𝟙_ F
  w : QX.obj W ⟶ Z
  qC : FB.obj (QX.obj (U ⊗ W)) ⟶ QY.obj (FA.obj (U ⊗ W))
  qSwap : FB.obj (QX.obj (W ⊗ U)) ⟶ QY.obj (FA.obj (W ⊗ U))
  qW : FB.obj (QX.obj W) ⟶ QY.obj (FA.obj W)
  uY : QY.obj (𝟙_ D) ≅ 𝟙_ F
  cK : QX.obj U ≅ V
  mu : QX.obj (U ⊗ W) ≅ QX.obj U ⊗ QX.obj W
  muSwap : QX.obj (W ⊗ U) ≅ QX.obj W ⊗ QX.obj U
  muY : QY.obj (FA.obj W ⊗ K) ≅ QY.obj (FA.obj W) ⊗ QY.obj K
  muYUnit : QY.obj ((𝟙_ D) ⊗ K) ≅ QY.obj (𝟙_ D) ⊗ QY.obj K
  pfA : FA.obj (W ⊗ U) ≅ FA.obj W ⊗ K
  pfW : FB.obj (QX.obj W ⊗ V) ≅ FB.obj (QX.obj W) ⊗ QY.obj K
  pfB : FB.obj (Z ⊗ V) ≅ FB.obj Z ⊗ QY.obj K
  symmetry_naturality :
    FB.map (QX.map (β_ U W).hom) ≫ qSwap =
      qC ≫ QY.map (FA.map (β_ U W).hom)
  projection_reduction :
    qSwap ≫ QY.map pfA.hom ≫ muY.hom =
      FB.map (muSwap.hom ≫ (𝟙 (QX.obj W) ⊗ₘ cK.hom)) ≫
        pfW.hom ≫ (qW ⊗ₘ 𝟙 (QY.obj K))
  projection_naturality :
    FB.map (w ⊗ₘ 𝟙 V) ≫ pfB.hom =
      pfW.hom ≫ (FB.map w ⊗ₘ 𝟙 (QY.obj K))
  unit_counit : qW ≫ QY.map eA ≫ uY.hom = FB.map w ≫ eB
  scalar_symmetry :
    QX.map (β_ U W).hom ≫ muSwap.hom =
      mu.hom ≫ (β_ (QX.obj U) (QX.obj W)).hom
  scalar_tensor_counit :
    QY.map (eA ⊗ₘ 𝟙 K) ≫ muYUnit.hom =
      muY.hom ≫ (QY.map eA ⊗ₘ 𝟙 (QY.obj K))
  scalar_unitor :
    QY.map (λ_ K).hom =
      muYUnit.hom ≫ (uY.hom ⊗ₘ 𝟙 (QY.obj K)) ≫ (λ_ (QY.obj K)).hom

instance (T : ProjectionCounitData.{u}) : Category T.C := T.catC
instance (T : ProjectionCounitData.{u}) : Category T.D := T.catD
instance (T : ProjectionCounitData.{u}) : Category T.E := T.catE
instance (T : ProjectionCounitData.{u}) : Category T.F := T.catF
instance (T : ProjectionCounitData.{u}) : MonoidalCategory T.C := T.monC
instance (T : ProjectionCounitData.{u}) : MonoidalCategory T.D := T.monD
instance (T : ProjectionCounitData.{u}) : MonoidalCategory T.E := T.monE
instance (T : ProjectionCounitData.{u}) : MonoidalCategory T.F := T.monF
instance (T : ProjectionCounitData.{u}) : BraidedCategory T.C := T.braidC
instance (T : ProjectionCounitData.{u}) : BraidedCategory T.E := T.braidE

namespace ProjectionCounitData
variable (T : ProjectionCounitData.{u})
/-- The A projection/counit composite. -/
def aA : T.FA.obj (T.U ⊗ T.W) ⟶ T.K :=
  T.FA.map (β_ T.U T.W).hom ≫ T.pfA.hom ≫
    (T.eA ⊗ₘ 𝟙 T.K) ≫ (λ_ T.K).hom
/-- The B projection/counit composite. -/
def aB : T.FB.obj (T.V ⊗ T.Z) ⟶ T.QY.obj T.K :=
  T.FB.map (β_ T.V T.Z).hom ≫ T.pfB.hom ≫
    (T.eB ⊗ₘ 𝟙 (T.QY.obj T.K)) ≫ (λ_ (T.QY.obj T.K)).hom
/-- The tensor-domain coefficient comparison. -/
def t : T.QX.obj (T.U ⊗ T.W) ⟶ T.V ⊗ T.Z :=
  T.mu.hom ≫ (T.cK.hom ⊗ₘ T.w)
end ProjectionCounitData

/-- Pointwise compact-support inverses suffice for the projection/counit calculation.
Source: finite-reduction proof Steps 3--4
(blueprint: lem-pur-projection-counit-pointwise-data).
Proof: naturality moves the initial symmetry past the scalar comparison. The
inverse projection square and scalar tensor/unit equations move the projection
and counit past reduction. Rewrite the reduced unit counit using its mate
identity, use projection naturality at the exceptional-unit map, and use
braiding naturality to move that map into the tensor source. -/
theorem projectionCounitReduction (T : ProjectionCounitData.{u}) :
    T.qC ≫ T.QY.map T.aA = T.FB.map T.t ≫ T.aB := by
  have htail :
      T.QY.map (T.eA ⊗ₘ 𝟙 T.K) ≫
          T.QY.map (λ_ T.K).hom =
        T.muY.hom ≫
          ((T.QY.map (T.eA) ≫ T.uY.hom) ⊗ₘ
            𝟙 (T.QY.obj T.K)) ≫ (λ_ (T.QY.obj T.K)).hom := by
    rw [T.scalar_unitor, ← Category.assoc, T.scalar_tensor_counit]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have hn := T.symmetry_naturality
  have hs :
      T.QX.map (β_ (T.U) (T.W)).hom ≫
          T.muSwap.hom ≫
          (𝟙 (T.QX.obj (T.W)) ⊗ₘ T.cK.hom) =
        T.mu.hom ≫
          (T.cK.hom ⊗ₘ 𝟙 (T.QX.obj (T.W))) ≫
          (β_ (T.V)
            (T.QX.obj (T.W))).hom := by
    rw [← Category.assoc, T.scalar_symmetry]
    rw [Category.assoc, BraidedCategory.braiding_naturality]
  dsimp [ProjectionCounitData.aA]
  simp only [Functor.map_comp]
  slice_lhs 4 5 => rw [htail]
  slice_lhs 1 2 => rw [← hn]
  simp only [Category.assoc]
  slice_lhs 2 4 => rw [T.projection_reduction]
  simp only [Category.assoc]
  slice_lhs 4 5 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rw [T.unit_counit]
  have hsplit := MonoidalCategory.tensorHom_comp_tensorHom
    (T.FB.map T.w) (𝟙 (T.QY.obj T.K))
    (T.eB) (𝟙 (T.QY.obj T.K))
  simp only [Category.id_comp] at hsplit
  rw [← hsplit]
  have hpf : T.FB.map (T.w ⊗ₘ 𝟙 (T.V)) ≫ T.pfB.hom =
      T.pfW.hom ≫ (T.FB.map T.w ⊗ₘ 𝟙 (T.QY.obj T.K)) := by
    exact T.projection_naturality
  slice_lhs 3 4 => rw [← hpf]
  have hdomain :
      (T.QX.map (β_ (T.U) (T.W)).hom ≫
        (T.muSwap.hom ≫ (𝟙 (T.QX.obj (T.W)) ⊗ₘ T.cK.hom))) ≫
          (T.w ⊗ₘ 𝟙 (T.V)) =
        T.t ≫ (β_ (T.V) (T.Z)).hom := by
    calc
      _ = (T.mu.hom ≫
          (T.cK.hom ⊗ₘ 𝟙 (T.QX.obj (T.W))) ≫
          (β_ (T.V)
            (T.QX.obj (T.W))).hom) ≫
          (T.w ⊗ₘ 𝟙 (T.V)) := by
            exact congrArg (fun z ↦ z ≫
              (T.w ⊗ₘ 𝟙 (T.V))) hs
      _ = _ := by
        simp only [Category.assoc]
        rw [← BraidedCategory.braiding_naturality]
        dsimp [ProjectionCounitData.t]
        simp only [Category.assoc]
        slice_lhs 2 3 =>
          rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
            Category.id_comp]
  have hmap := congrArg T.FB.map hdomain
  simp only [Functor.map_comp, Category.assoc] at hmap
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 1 4 => rw [hmap]
  dsimp [ProjectionCounitData.aB]
  simp only [Category.assoc]

/-- Inverting the three vertical/projection maps in a forward scalar projection
square gives the inverse projection square. Source: finite-reduction Step 3
(blueprint: lem-pur-projection-counit-pointwise-data). -/
theorem inverseProjectionScalarSquare
    {D E F : Type*} [Category D] [Category E] [Category F]
    [MonoidalCategory F]
    (Q : D ⥤ F) (G : E ⥤ F)
    {A B : D} {X Y : E} {W V K : F}
    (p : A ⟶ B) [IsIso p] (r : G.obj Y ⟶ V ⊗ K) [IsIso r]
    (q : Q.obj A ⟶ G.obj X) [IsIso q]
    (d : X ⟶ Y) (mu : Q.obj B ⟶ W ⊗ K)
    (v : W ⟶ V) [IsIso v]
    (h : mu ≫ (v ⊗ₘ 𝟙 K) ≫ inv r = Q.map (inv p) ≫ q ≫ G.map d) :
    inv q ≫ Q.map p ≫ mu = G.map d ≫ r ≫ (inv v ⊗ₘ 𝟙 K) := by
  apply (cancel_mono ((v ⊗ₘ 𝟙 K) ≫ inv r)).mp
  simp only [Category.assoc]
  rw [h]
  simp only [← Q.map_comp_assoc, IsIso.hom_inv_id, Q.map_id, Category.id_comp,
    IsIso.inv_hom_id_assoc]
  simp only [MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_whiskerRight_assoc, IsIso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp, IsIso.hom_inv_id,
    Category.comp_id]
