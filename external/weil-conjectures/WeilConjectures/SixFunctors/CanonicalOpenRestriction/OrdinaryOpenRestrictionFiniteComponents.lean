/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OpenSystemCounitEvaluation

/-! # Finite components of ordinary quotient restriction

Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I;
Cohomology on Sites, Tag 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe t u a b c d e f av bv cv dv ev fv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

/-- Transport a restriction-evaluation square through the two coefficient equivalences.
Source: Stacks 03DJ and 0941
(blueprint: lem-sf-ordinary-open-restriction-evaluation-mate). -/
def transportRestrictionEvaluation
    {A : Type a} {B : Type b} {C : Type c}
    {D : Type d} {E : Type e} {F : Type f}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C]
    [Category.{dv} D] [Category.{ev} E] [Category.{fv} F]
    (q : A ≌ B) (p : D ≌ E) (G : C ⥤ B) (V : B ⥤ E)
    (W : A ⥤ D) (H : C ⥤ F) (R : F ⥤ E)
    (τ : q.functor ⋙ V ≅ W ⋙ p.functor) (ν : G ⋙ V ≅ H ⋙ R) :
    (G ⋙ q.inverse) ⋙ W ≅ H ⋙ (R ⋙ p.inverse) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ p.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (G ⋙ q.inverse) τ.symm) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (Functor.associator G q.inverse q.functor ≪≫
          Functor.isoWhiskerLeft G q.counitIso ≪≫ Functor.rightUnitor G) V) _ ≪≫
    Functor.isoWhiskerRight ν _ ≪≫ Functor.associator _ _ _

/-- Component formula for transport through two coefficient equivalences.
Source: Stacks 03DJ and 0941
(blueprint: lem-sf-ordinary-open-restriction-evaluation-mate). -/
theorem transportRestrictionEvaluation_app
    {A : Type a} {B : Type b} {C : Type c}
    {D : Type d} {E : Type e} {F : Type f}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C]
    [Category.{dv} D] [Category.{ev} E] [Category.{fv} F]
    (q : A ≌ B) (p : D ≌ E) (G : C ⥤ B) (V : B ⥤ E)
    (W : A ⥤ D) (H : C ⥤ F) (R : F ⥤ E)
    (τ : q.functor ⋙ V ≅ W ⋙ p.functor) (ν : G ⋙ V ≅ H ⋙ R) (N : C) :
    (transportRestrictionEvaluation q p G V W H R τ ν).app N =
      p.unitIso.app _ ≪≫ p.inverse.mapIso (τ.app (q.inverse.obj (G.obj N))).symm ≪≫
        p.inverse.mapIso (V.mapIso (q.counitIso.app (G.obj N))) ≪≫
          p.inverse.mapIso (ν.app N) := by
  apply Iso.ext
  simp only [transportRestrictionEvaluation, Functor.comp_obj, Functor.id_obj,
    Iso.app_hom, Iso.app_inv, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.comp_id]
  rw [p.inverse.map_id, p.inverse.map_id]
  simp only [Category.id_comp]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] (o : Operations l E j)

/-- The natural form of the fixed ordinary restriction-evaluation comparison.
Source: Stacks 03DJ and 0941
(blueprint: lem-sf-ordinary-open-restriction-evaluation-mate). -/
def ordinaryRestrictionEvaluation (n : ℕ) :
    systemRestriction l E j o ⋙ coefficientSequenceEvaluation l E U n ≅
      coefficientSequenceEvaluation l E X n ⋙ finiteRestriction l E j o n :=
  transportRestrictionEvaluation o.systems (o.finite n) _ _ _ _ _
    (o.transportEvaluation n) (o.openSystems.restrictionEvaluation n)

/-- Its components retain exactly the originally prescribed units and counits.
Source: Stacks 03DJ and 0941
(blueprint: lem-sf-ordinary-open-restriction-evaluation-mate). -/
theorem ordinaryRestrictionEvaluation_app (n : ℕ) (N : coefficientSequenceModules l E X) :
    (ordinaryRestrictionEvaluation l E j o n).app N =
      counitRestrictionEvaluation l E j o n N := by
  exact transportRestrictionEvaluation_app o.systems (o.finite n) _ _ _ _ _
    (o.transportEvaluation n) (o.openSystems.restrictionEvaluation n) N

/-- Evaluation transports a right mate to its finite right mate.
Source: Stacks 03DJ and 0E8I; ordinary adjunction counit calculation.
(blueprint: lem-sf-ordinary-open-restriction-evaluation-mate).

Proof: apply the inverse finite Hom bijection. Naturality moves the finite counit
past p, and hε replaces it by the evaluated system counit. Move μ across the mate
by naturality and use the system mate-counit equation. Move p past the integral
counit. The inverse form of hr then gives the finite mate-counit word. The Hom
bijection is injective, so the original maps agree. -/
theorem evaluation_right_mate
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    {P : Type e} {Q : Type f}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C] [Category.{dv} D]
    [Category.{ev} P] [Category.{fv} Q]
    {L : A ⥤ B} {R : B ⥤ A} {K : C ⥤ D} {H : D ⥤ C}
    {Lf : P ⥤ Q} {Rf : Q ⥤ P}
    (adj : L ⊣ R) (sys : K ⊣ H) (fin : Lf ⊣ Rf)
    (F : A ⥤ C) (G : B ⥤ D) (ec : C ⥤ P) (ed : D ⥤ Q)
    (S : A ⥤ P) (T : B ⥤ Q)
    (p : G ⋙ ed ≅ T) (q : F ⋙ ec ≅ S)
    (μ : K ⋙ ed ≅ ec ⋙ Lf) (ν : H ⋙ ec ≅ ed ⋙ Rf)
    (hε : ∀ Z : D, Lf.map (ν.hom.app Z) ≫ fin.counit.app (ed.obj Z) =
      μ.inv.app (H.obj Z) ≫ ed.map (sys.counit.app Z))
    (r : L ⋙ G ≅ F ⋙ K) (α : L ⋙ T ≅ S ⋙ Lf)
    (hr : ∀ M : A, ed.map (r.hom.app M) ≫ μ.hom.app (F.obj M) ≫
      Lf.map (q.hom.app M) = p.hom.app (L.obj M) ≫ α.hom.app M)
    (N : B) :
    ec.map ((mateEquiv adj sys (TwoSquare.mk _ _ _ _ r.inv)).app N) ≫
        ν.hom.app (G.obj N) ≫ Rf.map (p.hom.app N) =
      q.hom.app (R.obj N) ≫
        (mateEquiv adj fin (TwoSquare.mk _ _ _ _ α.inv)).app N := by
  let s : R ⋙ F ⟶ G ⋙ H :=
    (mateEquiv adj sys (TwoSquare.mk _ _ _ _ r.inv))
  let sf : R ⋙ S ⟶ T ⋙ Rf :=
    (mateEquiv adj fin (TwoSquare.mk _ _ _ _ α.inv))
  change ec.map (s.app N) ≫ ν.hom.app (G.obj N) ≫ Rf.map (p.hom.app N) =
    q.hom.app (R.obj N) ≫ sf.app N
  have hs : K.map (s.app N) ≫ sys.counit.app (G.obj N) =
      r.inv.app (R.obj N) ≫ G.map (adj.counit.app N) :=
    mateEquiv_counit adj sys (TwoSquare.mk _ _ _ _ r.inv) N
  have hsf : Lf.map (sf.app N) ≫ fin.counit.app (T.obj N) =
      α.inv.app (R.obj N) ≫ T.map (adj.counit.app N) :=
    mateEquiv_counit adj fin (TwoSquare.mk _ _ _ _ α.inv) N
  have hi (M : A) : μ.inv.app (F.obj M) ≫ ed.map (r.inv.app M) ≫
      p.hom.app (L.obj M) = Lf.map (q.hom.app M) ≫ α.inv.app M := by
    apply (cancel_mono (α.hom.app M)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hr M, ← ed.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    rw [ed.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
  apply (fin.homEquiv _ _).symm.injective
  change Lf.map _ ≫ fin.counit.app _ = Lf.map _ ≫ fin.counit.app _
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
  have hn := fin.counit.naturality (p.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hn
  rw [hn, reassoc_of% (hε (G.obj N))]
  have hμ := μ.inv.naturality (s.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hμ
  rw [reassoc_of% hμ, ← ed.map_comp_assoc, hs, ed.map_comp]
  simp only [Category.assoc]
  have hp := p.hom.naturality (adj.counit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hp
  rw [hp, reassoc_of% (hi (R.obj N)), hsf]

end WeilConjectures.CanonicalOpenRestriction
