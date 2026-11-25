/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
import all WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemResolutionModels

/-! # Recovering a tensor comparison from its closed comparison

Source: Stacks 08J9; tensor--Hom adjunction and its naturality.
-/

@[expose] public section
set_option autoImplicit false

universe a b c d va vb vc vd
open CategoryTheory Opposite
namespace WeilConjectures

/-- A natural isomorphism preserving the evaluation-defined internal-Hom comparisons
also preserves the tensor comparisons.
Source: Stacks 08J9, tensor--Hom adjunction.
(blueprint: lem-coef-tensor-square-of-hom-square).

Proof: for inputs L,M transpose the identity of L tensor M. Apply the closed
comparison equality to M and L tensor M, and precompose by the image of this
transpose. Naturality of the given isomorphism and compatibility of base change
with transposition identify the two sides. Uncurrying gives the inverse tensor
square, since evaluation after the transposed identity is the identity. Cancel
the invertible tensor comparisons and the given isomorphism to obtain the forward
square. No faithfulness, essential surjectivity or nonzero hypothesis is used. -/
theorem coefficientTensorSquareOfHomSquare
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F G : A ⥤ B)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SA.tensor ⋙ G ≅ G.prod G ⋙ SB.tensor)
    (α : F ≅ G)
    (h : ∀ M N : A,
      coefficientBaseChangeHom SA SB F μ M N =
        α.hom.app (HA.obj (op M, N)) ≫ coefficientBaseChangeHom SA SB G ν M N ≫
          HB.map (Prod.mkHom (α.hom.app M).op (α.inv.app N)))
    (L M : A) :
    α.hom.app (SA.tensor.obj (L, M)) ≫ ν.hom.app (L, M) =
      μ.hom.app (L, M) ≫ SB.tensor.map (Prod.mkHom (α.hom.app L) (α.hom.app M)) := by
  let T := SA.tensor.obj (L, M)
  let c := SA.transpose L M T (𝟙 T)
  have hc :
      SB.transpose (F.obj L) (F.obj M) (F.obj T) (μ.inv.app (L, M)) =
        α.hom.app L ≫
          SB.transpose (G.obj L) (G.obj M) (G.obj T) (ν.inv.app (L, M)) ≫
          HB.map (Prod.mkHom (α.hom.app M).op (α.inv.app T)) := by
    calc
      _ = F.map c ≫ coefficientBaseChangeHom SA SB F μ M T := by
        have hh := baseChange_transpose SA SB F μ L M T (𝟙 T)
        have hid : μ.inv.app (L, M) ≫ F.map (𝟙 T) = μ.inv.app (L, M) := by
          rw [F.map_id]
          exact Category.comp_id _
        rw [hid] at hh
        exact hh.symm
      _ = F.map c ≫ α.hom.app (HA.obj (op M, T)) ≫
          coefficientBaseChangeHom SA SB G ν M T ≫
          HB.map (Prod.mkHom (α.hom.app M).op (α.inv.app T)) := by rw [h]
      _ = α.hom.app L ≫ (G.map c ≫ coefficientBaseChangeHom SA SB G ν M T) ≫
          HB.map (Prod.mkHom (α.hom.app M).op (α.inv.app T)) := by
        rw [← Category.assoc (F.map c), α.hom.naturality c]
        simp only [Category.assoc]
      _ = _ := by
        have hh := baseChange_transpose SA SB G ν L M T (𝟙 T)
        have hid : ν.inv.app (L, M) ≫ G.map (𝟙 T) = ν.inv.app (L, M) := by
          rw [G.map_id]
          exact Category.comp_id _
        rw [hid] at hh
        rw [hh]
  have hi := congrArg ((SB.transpose (F.obj L) (F.obj M) (F.obj T)).symm) hc
  rw [Equiv.symm_apply_apply, uncurry_precomp, uncurry_naturality,
    Equiv.symm_apply_apply] at hi
  have ht :
      SB.tensor.map (Prod.mkHom (α.hom.app L) (𝟙 (F.obj M))) ≫
          SB.tensor.map (Prod.mkHom (𝟙 (G.obj L)) (α.hom.app M)) =
        SB.tensor.map (Prod.mkHom (α.hom.app L) (α.hom.app M)) := by
    rw [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [← Category.assoc, ht] at hi
  apply (cancel_epi (μ.inv.app (L, M))).1
  apply (cancel_mono (ν.inv.app (L, M))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  rw [hi]
  simp [Category.assoc, T]

private theorem baseChange_composite
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HC : Cᵒᵖ × C ⥤ C}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (F : A ⥤ B) (G : B ⥤ C)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SC.tensor) (M N : A) :
    coefficientBaseChangeHom SA SC (F ⋙ G)
        (Functor.isoWhiskerRight μ G ≪≫ Functor.isoWhiskerLeft (F.prod F) ν) M N =
      G.map (coefficientBaseChangeHom SA SB F μ M N) ≫
        coefficientBaseChangeHom SB SC G ν (F.obj M) (F.obj N) := by
  let τ := Functor.isoWhiskerRight μ G ≪≫ Functor.isoWhiskerLeft (F.prod F) ν
  have hh := baseChange_evaluation SA SB SC F G (F ⋙ G) μ ν τ (Iso.refl _) (by
    intro X Y
    simp [τ]) M N
  simpa [τ] using hh.symm

/-- The closed square detects a square between two composite tensor comparisons.
Source: Stacks 08J9, transposition of the identity tensor map.
(blueprint: lem-coef-tensor-square-of-hom-square).
Proof: the evaluation-defined closed comparison of a composite is the composite
of the two closed comparisons. Substitute these formulas and apply
coefficientTensorSquareOfHomSquare. -/
theorem coefficientTensorSquareOfCompositeHomSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (α : F ⋙ V ≅ U ⋙ G)
    (h : ∀ M N : A,
      V.map (coefficientBaseChangeHom SA SB F μF M N) ≫
          coefficientBaseChangeHom SB SD V μV (F.obj M) (F.obj N) =
        α.hom.app (HA.obj (op M, N)) ≫
          G.map (coefficientBaseChangeHom SA SC U μU M N) ≫
          coefficientBaseChangeHom SC SD G μG (U.obj M) (U.obj N) ≫
          HD.map (Prod.mkHom (α.hom.app M).op (α.inv.app N)))
    (L M : A) :
    α.hom.app (SA.tensor.obj (L, M)) ≫ G.map (μU.hom.app (L, M)) ≫
        μG.hom.app (U.obj L, U.obj M) =
      V.map (μF.hom.app (L, M)) ≫ μV.hom.app (F.obj L, F.obj M) ≫
        SD.tensor.map (Prod.mkHom (α.hom.app L) (α.hom.app M)) := by
  let μ := Functor.isoWhiskerRight μF V ≪≫ Functor.isoWhiskerLeft (F.prod F) μV
  let ν := Functor.isoWhiskerRight μU G ≪≫ Functor.isoWhiskerLeft (U.prod U) μG
  have hh := coefficientTensorSquareOfHomSquare SA SD (F ⋙ V) (U ⋙ G) μ ν α (by
    intro M N
    rw [baseChange_composite, baseChange_composite]
    simpa only [Category.assoc] using h M N) L M
  simpa only [μ, ν, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.prod_obj, Category.assoc] using hh

end WeilConjectures
