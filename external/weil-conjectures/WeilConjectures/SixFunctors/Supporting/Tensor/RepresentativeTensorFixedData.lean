/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The fixed part of tensor representative data

Source: Stacks Tags 04VK and 07A4.
(blueprint: def-sf-representative-tensor-fixed-data).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures

/-- A tensor presentation on a class of representatives.
Source: Stacks Tag 04VK (blueprint: def-sf-representative-tensor-fixed-data). -/
structure TensorFixedRepresentativeData
    (K D : Type*) [Category K] [Category D] where
  q : K ⥤ D
  P : ObjectProperty K
  t : K × K ⥤ K
  T : D ⥤ D ⥤ D
  r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ uncurry.obj T

/-- Pullback data between two fixed tensor presentations.
Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-fixed-data). -/
structure TensorFixedPullbackData
    {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]
    (Y : TensorFixedRepresentativeData K D) (X : TensorFixedRepresentativeData H E) where
  A : K ⥤ H
  F : D ⥤ E
  f : Y.q ⋙ F ≅ A ⋙ X.q
  hA : ∀ P, Y.P P → X.P (A.obj P)
  mF : Y.t ⋙ A ⟶ (A.prod A) ⋙ X.t
  phiF : (postcompose₂.obj F).obj Y.T ⟶
    (((whiskeringLeft₂ E).obj F).obj F).obj X.T

/-- The representative equation for the fixed tensor comparison.
Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-fixed-data). -/
def TensorFixedPullbackData.law
    {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]
    {Y : TensorFixedRepresentativeData K D} {X : TensorFixedRepresentativeData H E}
    (S : TensorFixedPullbackData Y X) : Prop :=
  ∀ (P Q : K) (hp : Y.P P) (hq : Y.P Q),
    S.F.map (Y.r.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        (S.phiF.app (Y.q.obj P)).app (Y.q.obj Q) ≫
        (uncurry.obj X.T).map (Prod.mkHom (S.f.hom.app P) (S.f.hom.app Q)) =
      S.f.hom.app (Y.t.obj (P, Q)) ≫ X.q.map (S.mF.app (P, Q)) ≫
        X.r.hom.app (⟨S.A.obj P, S.hA P hp⟩, ⟨S.A.obj Q, S.hA Q hq⟩)

end WeilConjectures
