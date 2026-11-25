/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Currying

/-! # The ordinary tensor pullback square

Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-ordinary-pullback-law).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures

/-- The chain tensor square, independently of localization or chosen tensor models.
Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-ordinary-pullback-law).
The left composite first pulls back the fixed tensor and then realizes coefficients;
the right composite first realizes coefficients and then pulls back. This definition
only names their equality and constructs no objects from existence proofs. -/
def tensorOrdinaryPullbackLaw
    {K H K' H' : Type*} [Category K] [Category H] [Category K'] [Category H']
    (tY : K × K ⥤ K) (tX : H × H ⥤ H)
    (tY' : K' × K' ⥤ K') (tX' : H' × H' ⥤ H')
    (U : K ⥤ K') (V : H ⥤ H') (A : K ⥤ H) (B : K' ⥤ H')
    (c : U ⋙ B ≅ A ⋙ V)
    (mF : tY ⋙ A ⟶ (A.prod A) ⋙ tX)
    (bY : tY ⋙ U ⟶ (U.prod U) ⋙ tY')
    (bX : tX ⋙ V ⟶ (V.prod V) ⋙ tX')
    (mG : tY' ⋙ B ⟶ (B.prod B) ⋙ tX') : Prop :=
  ∀ P Q : K,
    V.map (mF.app (P, Q)) ≫ bX.app (A.obj P, A.obj Q) ≫
        tX'.map (Prod.mkHom (c.inv.app P) (c.inv.app Q)) =
      c.inv.app (tY.obj (P, Q)) ≫ B.map (bY.app (P, Q)) ≫
        mG.app (U.obj P, U.obj Q)

end WeilConjectures
