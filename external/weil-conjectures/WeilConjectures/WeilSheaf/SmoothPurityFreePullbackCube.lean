/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Comparing free-module pullback before and after coefficient extension -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {A B C D E F : Type*} [Category A] [Category B] [Category C]
  [Category D] [Category E] [Category F]
  {P : A ⥤ B} {RP : B ⥤ A} (p : P ⊣ RP)
  {FY : A ⥤ C} {RFY : C ⥤ A} (fy : FY ⊣ RFY)
  {FX : B ⥤ D} {RFX : D ⥤ B} (fx : FX ⊣ RFX)
  {Q : C ⥤ D} {RQ : D ⥤ C} (q : Q ⊣ RQ)
  {EY : C ⥤ E} {REY : E ⥤ C} (ey : EY ⊣ REY)
  {EX : D ⥤ F} {REX : F ⥤ D} (ex : EX ⊣ REX)
  {FY' : A ⥤ E} {RFY' : E ⥤ A} (fy' : FY' ⊣ RFY')
  {FX' : B ⥤ F} {RFX' : F ⥤ B} (fx' : FX' ⊣ RFX')
  {Q' : E ⥤ F} {RQ' : F ⥤ E} (q' : Q' ⊣ RQ')

/-- A commuting diagram of right adjoints implies the corresponding diagram of
the canonical comparisons of left adjoints. The application is the free-module,
coefficient-extension and geometric-pullback square. -/
theorem purity_free_pullback_cube
    (u : FY ⋙ Q ≅ P ⋙ FX) (v : FY' ⋙ Q' ≅ P ⋙ FX')
    (a : FY ⋙ EY ≅ FY') (b : FX ⋙ EX ≅ FX') (c : Q ⋙ EX ≅ EY ⋙ Q')
    (h : ∀ N : F,
      RP.map ((conjugateIsoEquiv fx' (fx.comp ex) b).hom.app N) ≫
          (conjugateIsoEquiv (p.comp fx) (fy.comp q) u).hom.app (REX.obj N) =
        (conjugateIsoEquiv (p.comp fx') (fy'.comp q') v).hom.app N ≫
          (conjugateIsoEquiv fy' (fy.comp ey) a).hom.app (RQ'.obj N) ≫
          RFY.map ((conjugateIsoEquiv (ey.comp q') (q.comp ex) c).hom.app N))
    (M : A) :
    EX.map (u.hom.app M) ≫ b.hom.app (P.obj M) =
      c.hom.app (FY.obj M) ≫ Q'.map (a.hom.app M) ≫ v.hom.app M := by
  let α : (FY ⋙ Q) ⋙ EX ≅ P ⋙ FX' :=
    Functor.isoWhiskerRight u EX ≪≫ Functor.associator P FX EX ≪≫
      Functor.isoWhiskerLeft P b
  let β : (FY ⋙ Q) ⋙ EX ≅ P ⋙ FX' :=
    Functor.associator FY Q EX ≪≫ Functor.isoWhiskerLeft FY c ≪≫
      (Functor.associator FY EY Q').symm ≪≫ Functor.isoWhiskerRight a Q' ≪≫ v
  have hh : α = β := by
    apply (conjugateIsoEquiv (p.comp fx') ((fy.comp q).comp ex)).injective
    dsimp only [α, β]
    rw [conjugateIsoEquiv_trans _ ((p.comp fx).comp ex),
      conjugateIsoEquiv_trans _ (p.comp (fx.comp ex)),
      conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
      conjugateIsoEquiv_isoWhiskerRight]
    rw [conjugateIsoEquiv_trans _ (fy.comp (q.comp ex)),
      conjugateIsoEquiv_trans _ (fy.comp (ey.comp q')),
      conjugateIsoEquiv_trans _ ((fy.comp ey).comp q'),
      conjugateIsoEquiv_trans _ (fy'.comp q'),
      conjugateIsoEquiv_isoWhiskerRight,
      conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator,
      conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator]
    ext N
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc] using h N
  have hhM := congrArg (fun e ↦ e.hom.app M) hh
  simpa only [α, β, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc] using hhM

end CategoryTheory
