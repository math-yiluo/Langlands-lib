/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionData
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! The component calculation underlying shift compatibility of refinement restriction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

private theorem counitRestriction_shift
    {A B C S : Type*} [Category A] [Category B] [Category C] [Category S]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift S ℤ]
    {L : A ⥤ B} {P : B ⥤ A} {F : B ⥤ C} {G : A ⥤ C} {K : S ⥤ B}
    [L.CommShift ℤ] [P.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [K.CommShift ℤ]
    (ε : P ⋙ L ⟶ 𝟭 B) (α : G ⟶ L ⋙ F)
    [NatTrans.CommShift ε ℤ] [NatTrans.CommShift α ℤ]
    (n : ℤ) (M : S) :
    (((K ⋙ P) ⋙ G).commShiftIso n).hom.app M ≫
        (α.app (P.obj (K.obj M)) ≫ F.map (ε.app (K.obj M)))⟦n⟧' =
      (α.app (P.obj (K.obj ((shiftFunctor S n).obj M))) ≫
        F.map (ε.app (K.obj ((shiftFunctor S n).obj M)))) ≫
          ((K ⋙ F).commShiftIso n).hom.app M := by
  let θ : ((K ⋙ P) ⋙ G) ⟶ K ⋙ F :=
    (Functor.associator K P G).hom ≫
      Functor.whiskerLeft K (Functor.whiskerLeft P α ≫
        (Functor.associator P L F).inv ≫ Functor.whiskerRight ε F ≫
          (Functor.leftUnitor F).hom)
  have : NatTrans.CommShift θ ℤ := by dsimp only [θ]; infer_instance
  have hθ (N : S) : θ.app N =
      α.app (P.obj (K.obj N)) ≫ F.map (ε.app (K.obj N)) := by
    simp [θ]
  simpa only [hθ] using NatTrans.shift_app_comm θ n M

private theorem pullAdjunction_shift {U V : Scheme.{u}} (R : Coefficients.{u})
    (g : U ⟶ V) :
    (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)).CommShift ℤ := by
  unfold proEtaleRingDerivedAdjunction
  exact canonicalRightDerivedAdjunctionShift
    (proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g))

private theorem geometricPullComposition_shift (R : Coefficients.{u})
    {U V W : Scheme.{u}}
    (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    (geometricPullComposition R h k hc).hom.CommShift ℤ := by
  dsimp only [geometricPullComposition, Iso.trans_hom]
  infer_instance

private theorem pull_eqToIso_shift (R : Coefficients.{u})
    {U V : Scheme.{u}} {g h : U ⟶ V} (e : g = h) :
    NatTrans.CommShift (eqToIso (congrArg (fun k : U ⟶ V ↦ pull R k) e)).hom ℤ := by
  cases e
  dsimp
  infer_instance

private theorem refinementPull_shift (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i)) :
    (refinementPull R r hi).hom.CommShift ℤ := by
  dsimp only [refinementPull, Iso.trans_hom]
  let := pull_eqToIso_shift R r.i_hom.symm
  let := geometricPullComposition_shift R c.i r.hom hi
  infer_instance

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, the exact pullback compositor and proper counit
calculation on the distinguished open component.
Proof: the component map is the composite of the normalized pullback comparison with
the derived proper counit.  Both factors commute with the canonical integer
cochain shifts, and their composite gives the displayed equation.
(blueprint: lem-sf-refinement-restriction-component-shift).
-/
theorem refinementRestriction_component_shift
    (n : ℤ) (M : DerivedCategory (pbcModules X (R.ring X))) :
    (( ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙
      pull R d.i).commShiftIso n).hom.app M ≫
      (refinementRestriction R r hi M)⟦n⟧' =
    refinementRestriction R r hi ((shiftFunctor _ n).obj M) ≫
      (((openExtension R c.i).mapDerivedCategory ⋙ pull R c.i).commShiftIso n).hom.app M := by
  -- Normalize the transport along the open triangle before using the categorical API.
  revert hi
  rcases c with ⟨Zc, gc, ic, hc, hpc, hoc⟩
  rcases d with ⟨Zd, gd, jd, hd, hpd, hod⟩
  rcases r with ⟨v, hv, hvg⟩
  change Zc ⟶ Zd at v
  change ic ≫ v = jd at hv
  change v ≫ gd = gc at hvg
  subst jd
  intro hi
  let c : Compactification f := ⟨Zc, gc, ic, hc, hpc, hoc⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ v, hd, hpd, hod⟩
  let r : c.Refinement d := ⟨v, rfl, hvg⟩
  let := pullAdjunction_shift R r.hom
  let := refinementPull_shift R r hi
  simpa only [refinementRestriction.eq_def] using counitRestriction_shift
    (L := pull R r.hom) (P := push R r.hom) (F := pull R c.i) (G := pull R d.i)
    (K := (openExtension R c.i).mapDerivedCategory)
    (proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit
    (refinementPull R r hi).hom n M

end WeilConjectures.PurCompactSupport
