/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestriction
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarGeometricPullComposition
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import all WeilConjectures.SixFunctors.PurCompactSupport.ProperScalarComposition
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenScalarUnitSquare

/-! # Scalar naturality of the canonical inner open-refinement map

Source: Stacks 03DI, 0F7B, 0F7I, 07A6; open-unit and proper-counit mate pasting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.reductionDerivedChange
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport
attribute [local instance 100000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  SheafOfModules.instAbelian
attribute [local irreducible] geometricPullComposition scalarPull openComparison properComparison
  refinementPull proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction openDerivedAdjunction

@[irreducible] private def restrictionComposite
    {C A B : Type*} [Category C] [Category A] [Category B]
    {F : B ⥤ A} {P : A ⥤ B} (adj : F ⊣ P)
    (U₁ : A ⥤ C) (U₂ : B ⥤ C) (k : U₂ ≅ F ⋙ U₁) : P ⋙ U₂ ⟶ U₁ :=
  Functor.whiskerLeft P k.hom ≫ (Functor.associator P F U₁).inv ≫
    Functor.whiskerRight adj.counit U₁ ≫ (Functor.leftUnitor U₁).hom

private theorem restrictionComposite_app
    {C A B : Type*} [Category C] [Category A] [Category B]
    {F : B ⥤ A} {P : A ⥤ B} (adj : F ⊣ P)
    (U₁ : A ⥤ C) (U₂ : B ⥤ C) (k : U₂ ≅ F ⋙ U₁) (N : A) :
    (restrictionComposite adj U₁ U₂ k).app N =
      k.hom.app (P.obj N) ≫ U₁.map (adj.counit.app N) := by
  simp [restrictionComposite]

private theorem coefficient_refinement_forward
    {CA DA EA CB DB EB : Type*}
    [Category CA] [Category DA] [Category EA]
    [Category CB] [Category DB] [Category EB]
    {J₁A : CA ⥤ DA} {J₂A : CA ⥤ EA}
    {U₁A : DA ⥤ CA} {U₂A : EA ⥤ CA}
    {J₁B : CB ⥤ DB} {J₂B : CB ⥤ EB}
    {U₁B : DB ⥤ CB} {U₂B : EB ⥤ CB}
    (a₁A : J₁A ⊣ U₁A) (a₂A : J₂A ⊣ U₂A)
    (a₁B : J₁B ⊣ U₁B) (a₂B : J₂B ⊣ U₂B)
    (RA : DA ⥤ EA) (RB : DB ⥤ EB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (tA : RA ⋙ U₂A ⟶ U₁A) (tB : RB ⋙ U₂B ⟶ U₁B)
    (s₁ : U₁A ⋙ QX ≅ Q₁ ⋙ U₁B) (s₂ : U₂A ⋙ QX ≅ Q₂ ⋙ U₂B)
    (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hχ : ∀ M, U₂B.map (χ.app M) ≫ tB.app (Q₁.obj M) ≫ s₁.inv.app M =
      s₂.inv.app (RA.obj M) ≫ QX.map (tA.app M))
    (K : CA) (αA : J₂A.obj K ⟶ RA.obj (J₁A.obj K))
    (αB : J₂B.obj (QX.obj K) ⟶ RB.obj (J₁B.obj (QX.obj K)))
    (b₁ : Q₁.obj (J₁A.obj K) ⟶ J₁B.obj (QX.obj K)) [IsIso b₁]
    (b₂ : Q₂.obj (J₂A.obj K) ⟶ J₂B.obj (QX.obj K)) [IsIso b₂]
    (hb₁ : a₁B.unit.app (QX.obj K) ≫ U₁B.map (inv b₁) =
      QX.map (a₁A.unit.app K) ≫ s₁.hom.app (J₁A.obj K))
    (hb₂ : a₂B.unit.app (QX.obj K) ≫ U₂B.map (inv b₂) =
      QX.map (a₂A.unit.app K) ≫ s₂.hom.app (J₂A.obj K))
    (hA : a₂A.homEquiv _ _ αA ≫ tA.app (J₁A.obj K) = a₁A.unit.app K)
    (hB : a₂B.homEquiv _ _ αB ≫ tB.app (J₁B.obj (QX.obj K)) =
      a₁B.unit.app (QX.obj K)) [Mono (tB.app (J₁B.obj (QX.obj K)))] :
    Q₂.map αA ≫ χ.app (J₁A.obj K) ≫ RB.map b₁ = b₂ ≫ αB := by
  exact AlgebraicGeometry.Etale.coefficient_refinement_of_restriction
    a₁A a₂A a₁B a₂B RA RB QX Q₁ Q₂ tA tB s₁.symm s₂.symm χ hχ K αA αB
    (asIso b₁) (asIso b₂) hb₁ hb₂ hA hB

private abbrev restrictionAll (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : _) :=
  restrictionComposite
    (proEtaleRingDerivedAdjunction r.hom (R.ring d.Z) (R.ring c.Z) (R.pull r.hom))
    (pull R c.i) (pull R d.i) (refinementPull R r hc)

private theorem inverse_pull_composition {R S : Coefficients.{u}} (a : Change R S)
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) (g : U ⟶ W)
    (w : h ≫ k = g)
    (hR : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h))
    (hS : S.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (S.ring W) (S.ring V) (S.ring U) (S.pull k) (S.pull h))
    (N : DerivedCategory (proEtaleRingModules W (R.ring W))) :
    let kR : pull R g ≅ pull R k ⋙ pull R h := eqToIso (congrArg (fun t ↦ pull R t) w.symm) ≪≫
      geometricPullComposition R h k hR
    let kS : pull S g ≅ pull S k ⋙ pull S h := eqToIso (congrArg (fun t ↦ pull S t) w.symm) ≪≫
      geometricPullComposition S h k hS
    kS.hom.app ((pbcDerivedExtend (a.map W)).obj N) ≫
        (pull S h).map ((scalarPull a k).inv.app N) ≫
        (scalarPull a h).inv.app ((pull R k).obj N) =
      (scalarPull a g).inv.app N ≫ (pbcDerivedExtend (a.map U)).map (kR.hom.app N) := by
  subst g
  dsimp only
  simp (config := { dsimp := false }) only [eqToIso_refl, Iso.refl_trans]
  have he : (pbcDerivedExtend (a.map U)).mapIso
        ((geometricPullComposition R h k hR).symm.app N) ≪≫ (scalarPull a (h ≫ k)).app N =
      (scalarPull a h).app ((pull R k).obj N) ≪≫
        (pull S h).mapIso ((scalarPull a k).app N) ≪≫
        (geometricPullComposition S h k hS).symm.app
          ((pbcDerivedExtend (a.map W)).obj N) := by
    apply Iso.ext
    exact scalarPull_geometric_composition a h k hR hS N
  simpa (config := { dsimp := false }) only [Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc] using (congrArg Iso.inv he).symm

private theorem inverse_of_unit
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {Z : D} (β : A ⟶ B) [IsIso β]
    (η : Z ⟶ F.obj B) (v : Z ⟶ F.obj A) (h : v ≫ F.map β = η) :
    η ≫ F.map (inv β) = v := by
  apply (cancel_mono (F.map β)).mp
  simp (config := { dsimp := false }) only [Category.assoc, ← F.map_comp,
    IsIso.inv_hom_id, F.map_id, Category.comp_id]
  exact h.symm

private theorem inverse_open_unit {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : _)
    [IsIso ((openComparison a j).app M)] :
    (openDerivedAdjunction S j).unit.app ((pbcDerivedExtend (a.map U)).obj M) ≫
        (pull S j).map (inv ((openComparison a j).app M)) =
      (pbcDerivedExtend (a.map U)).map ((openDerivedAdjunction R j).unit.app M) ≫
        (scalarPull a j).hom.app ((openExtension R j).mapDerivedCategory.obj M) := by
  exact inverse_of_unit (pull S j) ((openComparison a j).app M)
    ((openDerivedAdjunction S j).unit.app ((pbcDerivedExtend (a.map U)).obj M)) _
    ((Category.assoc _ _ _).trans (_root_.coefficientOpen_unit a j M))

private theorem proper_counit {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (N : DerivedCategory (proEtaleRingModules U (R.ring U))) :
    (pull S g).map ((properComparison a g).app N) ≫
        (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)).counit.app
          ((pbcDerivedExtend (a.map U)).obj N) =
      (scalarPull a g).inv.app ((push R g).obj N) ≫
        (pbcDerivedExtend (a.map U)).map
          ((proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)).counit.app N) := by
  have h := mateEquiv_counit
    (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g))
    (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g))
    (TwoSquare.mk _ _ _ _ (scalarPull a g).inv) N
  rw [properComparison_mate_square] at h
  exact h

private theorem refinementPull_def (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : _) :
    refinementPull R r hc =
      eqToIso (congrArg (fun g : X ⟶ d.Z ↦ pull R g) r.i_hom.symm) ≪≫
        geometricPullComposition R c.i r.hom hc := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  unfold refinementPull
  rfl

private theorem refinement_pull_scalar {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hR : _)
    (hS : _)
    (N : DerivedCategory (proEtaleRingModules d.Z (R.ring d.Z))) :
    (refinementPull S r hS).hom.app ((pbcDerivedExtend (a.map d.Z)).obj N) ≫
        (pull S c.i).map ((scalarPull a r.hom).inv.app N) ≫
        (scalarPull a c.i).inv.app ((pull R r.hom).obj N) =
      (scalarPull a d.i).inv.app N ≫
        (pbcDerivedExtend (a.map X)).map ((refinementPull R r hR).hom.app N) := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  change DerivedCategory (proEtaleRingModules Zd (R.ring Zd)) at N
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  rw [refinementPull_def, refinementPull_def]
  exact inverse_pull_composition a c.i r.hom d.i r.i_hom hR hS N

private theorem restriction_scalar {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hR : _) (hS : _) (N : DerivedCategory (proEtaleRingModules c.Z (R.ring c.Z))) :
    (pull S d.i).map ((properComparison a r.hom).app N) ≫
        (restrictionAll S r hS).app ((pbcDerivedExtend (a.map c.Z)).obj N) ≫
        (scalarPull a c.i).inv.app N =
      (scalarPull a d.i).inv.app ((push R r.hom).obj N) ≫
        (pbcDerivedExtend (a.map X)).map ((restrictionAll R r hR).app N) := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  change DerivedCategory (proEtaleRingModules Zc (R.ring Zc)) at N
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  simp only [restrictionAll, restrictionComposite_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (refinementPull S r hS).hom.naturality
    ((properComparison a r.hom).app N)]
  rw [← (pull S c.i).map_comp_assoc, proper_counit, (pull S c.i).map_comp]
  simp only [Category.assoc]
  have hn := (scalarPull a c.i).inv.naturality
    ((proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app N)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [hn]
  simpa only [Category.assoc, Functor.comp_obj, Functor.map_comp] using
    congrArg (fun z ↦ z ≫ (pbcDerivedExtend (a.map X)).map
      ((pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
        (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app N)))
      (refinement_pull_scalar a r hR hS ((push R r.hom).obj N))

private theorem restrictionAll_open_app (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : _) (M : _) :
    (restrictionAll R r hc).app ((openExtension R c.i).mapDerivedCategory.obj M) =
      refinementRestriction R r hc M := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  simp only [restrictionAll, restrictionComposite_app, refinementRestriction]

private theorem restrictionAll_normalization (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : _)
    (M : _) :
    (openDerivedAdjunction R d.i).homEquiv _ _ ((refinementOpenMap R r hc).app M) ≫
        (restrictionAll R r hc).app ((openExtension R c.i).mapDerivedCategory.obj M) =
      (openDerivedAdjunction R c.i).unit.app M := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  rw [restrictionAll_open_app]
  exact refinementOpenMap_normalization R r hc M

private theorem restrictionAll_open_isIso (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hc : _)
    (M : _) :
    IsIso ((restrictionAll R r hc).app ((openExtension R c.i).mapDerivedCategory.obj M)) := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  rw [restrictionAll_open_app]
  obtain ⟨θ, hθ, hIso, _⟩ := exists_refinementRestriction R r hc
  have := hIso
  rw [← hθ]
  infer_instance

/-- The inner canonical refinement map commutes with the open and proper scalar mates.
Source: Stacks 03DI, 0F7B, 0F7I, 07A6; Zheng 5.13--5.15.
(blueprint: lem-sf-refinement-open-scalar-square).

Proof: transpose the asserted equation under the S-open adjunction for d.i.
The transpose of refinementOpenMap is the c.i-open unit followed by the inverse
of refinementRestrictionNat. The scalar proper map transposes to scalar extension
of the proper counit after scalarPull inverse. The scalar open map is normalized
by the open unit. The coefficient pullback composition square commutes: take mates
of the ordinary restriction/direct-image composition square, whose section maps
are restriction along the same fibre-product associator with unchanged coefficients.
After this substitution, naturality of scalarPull and the proper counit identify
the two transposes after postcomposition with refinementRestrictionNat for S.
That transformation is invertible by exists_refinementRestriction, so cancel it.
The remaining equality is precisely the open-unit normalization of openComparison;
the adjunction triangle identities cancel its middle unit and counit. Injectivity
of the Hom adjunction proves the equation. This calculation uses actual derived
maps, with no inference from finite reductions and no choice of an exceptional
operation. It applies to arbitrary unbounded inputs and compatible coefficient
sheaves. For an empty open or zero object all maps are the unique zero maps; for
an identity refinement the formula is open coefficient-map naturality. -/
theorem refinementOpenMap_scalar
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hR : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))
    (hS : S.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (S.ring d.Z) (S.ring c.Z) (S.ring X) (S.pull r.hom) (S.pull c.i))
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pbcDerivedExtend (a.map d.Z)).map ((refinementOpenMap R r hR).app M) ≫
        (properComparison a r.hom).app ((openExtension R c.i).mapDerivedCategory.obj M) ≫
        (push S r.hom).map ((openComparison a c.i).app M) =
      (openComparison a d.i).app M ≫
        (refinementOpenMap S r hS).app ((pbcDerivedExtend (a.map X)).obj M) := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change h ≫ gd = gc at hhg
  subst id
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ h, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, rfl, rfl⟩
  let JS := (openExtension S c.i).mapDerivedCategory
  let TX := pbcDerivedExtend (a.map X)
  let TC := pbcDerivedExtend (a.map c.Z)
  let TD := pbcDerivedExtend (a.map d.Z)
  let tR := restrictionAll R r hR
  let tS := restrictionAll S r hS
  have := openComparison_isIso a c.i M
  have := openComparison_isIso a d.i M
  have := restrictionAll_open_isIso S r hS (TX.obj M)
  exact coefficient_refinement_forward
    (openDerivedAdjunction R c.i) (openDerivedAdjunction R d.i)
    (openDerivedAdjunction S c.i) (openDerivedAdjunction S d.i)
    (push R r.hom) (push S r.hom) TX TC TD tR tS
    (scalarPull a c.i) (scalarPull a d.i) (properComparison a r.hom)
    (restriction_scalar a r hR hS) M
    ((refinementOpenMap R r hR).app M) ((refinementOpenMap S r hS).app (TX.obj M))
    ((openComparison a c.i).app M) ((openComparison a d.i).app M)
    (inverse_open_unit a c.i M) (inverse_open_unit a d.i M)
    (restrictionAll_normalization R r hR M)
    (restrictionAll_normalization S r hS (TX.obj M))

end WeilConjectures.PurCompactSupport
