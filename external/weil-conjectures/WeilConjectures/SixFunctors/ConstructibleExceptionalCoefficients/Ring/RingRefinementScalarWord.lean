/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingOpenRefinement
import Mathlib.Tactic.DefEqTransformations
import WeilConjectures.SixFunctors.PurCompactSupport.ProperScalarComposition
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenScalarSquare

/-! # Scalar naturality of the ordinary proper/open refinement word

Source: Stacks 0F7B and 0F7I; Zheng Section 5, Lemma 5.13 and Constructions 5.14--5.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local irreducible] PurCompactSupport.geometricPushComposition
  PurCompactSupport.geometricPullComposition PurCompactSupport.openDerivedAdjunction
  PurCompactSupport.comparison PurCompactSupport.properComparison
  PurCompactSupport.openComparison
  PurCompactSupport.refinementRestriction reductionDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local instance] constructionInclusionShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem normalized_refinement_unique
    {R : PurCompactSupport.Coefficients.{w}}
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))
    (M : DerivedCategory (pbcModules X (R.ring X)))
    (ε : (PurCompactSupport.openExtension R d.i).mapDerivedCategory.obj M ⟶
      (PurCompactSupport.push R r.hom).obj
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj M))
    (hε : (PurCompactSupport.openDerivedAdjunction R d.i).homEquiv _ _ ε ≫
      PurCompactSupport.refinementRestriction R r hi M =
        (PurCompactSupport.openDerivedAdjunction R c.i).unit.app M) :
    ε = (PurCompactSupport.refinementOpenMap R r hi).app M := by
  obtain ⟨θ, happ, hθ, _⟩ := PurCompactSupport.exists_refinementRestriction R r hi
  let := hθ
  have : IsIso (PurCompactSupport.refinementRestriction R r hi M) := by
    rw [← happ M]
    infer_instance
  apply (PurCompactSupport.openDerivedAdjunction R d.i).homEquiv _ _ |>.injective
  apply (cancel_mono (PurCompactSupport.refinementRestriction R r hi M)).mp
  exact hε.trans (PurCompactSupport.refinementOpenMap_normalization R r hi M).symm

private theorem refinement_word_square
    {XR CR DR YR XS CS DS YS : Type*}
    [Category XR] [Category CR] [Category DR] [Category YR]
    [Category XS] [Category CS] [Category DS] [Category YS]
    (TX : XR ⥤ XS) (TC : CR ⥤ CS) (TD : DR ⥤ DS) (TY : YR ⥤ YS)
    (JcR : XR ⥤ CR) (JdR : XR ⥤ DR) (JcS : XS ⥤ CS) (JdS : XS ⥤ DS)
    (PrR : CR ⥤ DR) (PrS : CS ⥤ DS) (PdR : DR ⥤ YR) (PdS : DS ⥤ YS)
    (PcR : CR ⥤ YR) (PcS : CS ⥤ YS)
    (qR : PrR ⋙ PdR ≅ PcR) (qS : PrS ⋙ PdS ≅ PcS)
    (χr : PrR ⋙ TD ⟶ TC ⋙ PrS) (χd : PdR ⋙ TY ⟶ TD ⋙ PdS)
    (χc : PcR ⋙ TY ⟶ TC ⋙ PcS)
    (βc : JcR ⋙ TC ⟶ TX ⋙ JcS) (βd : JdR ⋙ TD ⟶ TX ⋙ JdS)
    (αS : JdS ⟶ JcS ⋙ PrS) (M : XR) (N : XS) (e : N ≅ TX.obj M)
    (εR : JdR.obj M ≅ PrR.obj (JcR.obj M))
    (εS : JdS.obj N ≅ PrS.obj (JcS.obj N))
    (hεS : εS.hom = αS.app N)
    (hopen : TD.map εR.hom ≫ χr.app (JcR.obj M) ≫ PrS.map (βc.app M) =
      βd.app M ≫ αS.app (TX.obj M))
    (hc : TY.map (qR.inv.app (JcR.obj M)) ≫ χd.app (PrR.obj (JcR.obj M)) ≫
      PdS.map (χr.app (JcR.obj M)) =
        χc.app (JcR.obj M) ≫ qS.inv.app (TC.obj (JcR.obj M))) :
    TY.map (qR.inv.app (JcR.obj M) ≫ PdR.map εR.inv) ≫
        (χd.app (JdR.obj M) ≫ PdS.map (βd.app M)) =
      (χc.app (JcR.obj M) ≫ PcS.map (βc.app M)) ≫ PcS.map (JcS.map e.inv) ≫
        (qS.inv.app (JcS.obj N) ≫ PdS.map εS.inv) ≫ PdS.map (JdS.map e.hom) := by
  have hopen' : χr.app (JcR.obj M) ≫ PrS.map (βc.app M) ≫
      PrS.map (JcS.map e.inv) ≫ εS.inv ≫ JdS.map e.hom =
        TD.map εR.inv ≫ βd.app M := by
    apply (cancel_epi (TD.map εR.hom)).mp
    rw [← TD.map_comp_assoc, εR.hom_inv_id, TD.map_id, Category.id_comp]
    rw [reassoc_of% hopen]
    have hn := αS.naturality e.inv
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, ← hεS]
    simp only [Iso.hom_inv_id_assoc]
    rw [← JdS.map_comp, e.inv_hom_id, JdS.map_id]
    simp only [Category.comp_id]
  have hn := χd.naturality εR.inv
  dsimp only [Functor.comp_map] at hn
  have hq := qS.inv.naturality (βc.app M ≫ JcS.map e.inv)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← PdS.map_comp, ← hopen']
  simp only [Functor.map_comp]
  rw [reassoc_of% hc]
  have hq' : qS.inv.app (TC.obj (JcR.obj M)) ≫
      PdS.map (PrS.map (βc.app M)) ≫ PdS.map (PrS.map (JcS.map e.inv)) =
    PcS.map (βc.app M) ≫ PcS.map (JcS.map e.inv) ≫ qS.inv.app (JcS.obj N) := by
    simpa only [Functor.map_comp, Category.assoc] using hq.symm
  rw [reassoc_of% hq']

private theorem refinement_normalized_word_square
    {XR CR DR YR XS CS DS YS : Type*}
    [Category XR] [Category CR] [Category DR] [Category YR]
    [Category XS] [Category CS] [Category DS] [Category YS]
    (TX : XR ⥤ XS) (TC : CR ⥤ CS) (TD : DR ⥤ DS) (TY : YR ⥤ YS)
    (JcR : XR ⥤ CR) (JdR : XR ⥤ DR) (JcS : XS ⥤ CS) (JdS : XS ⥤ DS)
    (PrR : CR ⥤ DR) (PrS : CS ⥤ DS) (PdR : DR ⥤ YR) (PdS : DS ⥤ YS)
    (PcR : CR ⥤ YR) (PcS : CS ⥤ YS)
    (qR : PrR ⋙ PdR ≅ PcR) (qS : PrS ⋙ PdS ≅ PcS)
    (χr : PrR ⋙ TD ⟶ TC ⋙ PrS) (χd : PdR ⋙ TY ⟶ TD ⋙ PdS)
    (χc : PcR ⋙ TY ⟶ TC ⋙ PcS)
    (βc : JcR ⋙ TC ⟶ TX ⋙ JcS) (βd : JdR ⋙ TD ⟶ TX ⋙ JdS)
    (αS : JdS ⟶ JcS ⋙ PrS) (M : XR) (N : XS) (e : N ≅ TX.obj M)
    (εR : JdR.obj M ≅ PrR.obj (JcR.obj M))
    (εS : JdS.obj N ≅ PrS.obj (JcS.obj N))
    (αR : JdR ⟶ JcR ⋙ PrR)
    (hεR : εR.hom = αR.app M)
    (hεS : εS.hom = αS.app N)
    (hopen : TD.map (αR.app M) ≫ χr.app (JcR.obj M) ≫ PrS.map (βc.app M) =
      βd.app M ≫ αS.app (TX.obj M))
    (hc : TY.map (qR.inv.app (JcR.obj M)) ≫ χd.app (PrR.obj (JcR.obj M)) ≫
      PdS.map (χr.app (JcR.obj M)) =
        χc.app (JcR.obj M) ≫ qS.inv.app (TC.obj (JcR.obj M)))
    (δc : TY.obj (PcR.obj (JcR.obj M)) ⟶ PcS.obj (JcS.obj (TX.obj M)))
    (δd : TY.obj (PdR.obj (JdR.obj M)) ⟶ PdS.obj (JdS.obj (TX.obj M)))
    (hδc : δc = χc.app (JcR.obj M) ≫ PcS.map (βc.app M))
    (hδd : δd = χd.app (JdR.obj M) ≫ PdS.map (βd.app M)) :
    TY.map (qR.inv.app (JcR.obj M) ≫ PdR.map εR.inv) ≫ δd =
      δc ≫ PcS.map (JcS.map e.inv) ≫
        (qS.inv.app (JcS.obj N) ≫ PdS.map εS.inv) ≫ PdS.map (JdS.map e.hom) := by
  rw [hδc, hδd]
  rw [← hεR] at hopen
  exact refinement_word_square TX TC TD TY JcR JdR JcS JdS PrR PrS PdR PdS PcR PcS
    qR qS χr χd χc βc βd αS M N e εR εS hεS hopen hc

private meta def normalizeCoefficientAliases (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let names := #[``pbcModules, ``proEtaleRingModules, ``reductionModules,
    ``reductionModuleRing, ``adicLisseForget, ``proEtaleRingModules_hasDerivedCategory,
    ``reductionModulesHasDerivedCategory, ``PurCompactSupport.push,
    ``PurCompactSupport.image]
  let e ← Lean.Meta.deltaExpand e names.contains
  Lean.Core.betaReduce e

private theorem ambient_refinement_scalar
    {R S : PurCompactSupport.Coefficients.{w}} (a : PurCompactSupport.Change R S)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (hiR : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))
    (hiS : S.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
      (S.ring d.Z) (S.ring c.Z) (S.ring X) (S.pull r.hom) (S.pull c.i))
    (hgR : R.pull (r.hom ≫ d.g) = proEtaleRingCompositeCoefficients r.hom d.g
      (R.ring Y) (R.ring d.Z) (R.ring c.Z) (R.pull d.g) (R.pull r.hom))
    (hgS : S.pull (r.hom ≫ d.g) = proEtaleRingCompositeCoefficients r.hom d.g
      (S.ring Y) (S.ring d.Z) (S.ring c.Z) (S.pull d.g) (S.pull r.hom))
    (M : DerivedCategory (pbcModules X (R.ring X)))
    (N : DerivedCategory (pbcModules X (S.ring X)))
    (e : N ≅ (pbcDerivedExtend (a.map X)).obj M)
    (εR : (PurCompactSupport.openExtension R d.i).mapDerivedCategory.obj M ≅
      (PurCompactSupport.push R r.hom).obj
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj M))
    (εS : (PurCompactSupport.openExtension S d.i).mapDerivedCategory.obj N ≅
      (PurCompactSupport.push S r.hom).obj
        ((PurCompactSupport.openExtension S c.i).mapDerivedCategory.obj N))
    (hεR : εR.hom = (PurCompactSupport.refinementOpenMap R r hiR).app M)
    (hεS : εS.hom = (PurCompactSupport.refinementOpenMap S r hiS).app N) :
    let JcR := (PurCompactSupport.openExtension R c.i).mapDerivedCategory
    let JcS := (PurCompactSupport.openExtension S c.i).mapDerivedCategory
    let JdS := (PurCompactSupport.openExtension S d.i).mapDerivedCategory
    let PcS := PurCompactSupport.push S c.g
    let PdR := PurCompactSupport.push R d.g
    let PdS := PurCompactSupport.push S d.g
    let qR : PurCompactSupport.push R r.hom ⋙ PurCompactSupport.push R d.g ≅
        PurCompactSupport.push R c.g :=
      PurCompactSupport.geometricPushComposition R r.hom d.g hgR ≪≫
        eqToIso (congrArg (fun h ↦ PurCompactSupport.push R h) r.hom_g)
    let qS : PurCompactSupport.push S r.hom ⋙ PurCompactSupport.push S d.g ≅
        PurCompactSupport.push S c.g :=
      PurCompactSupport.geometricPushComposition S r.hom d.g hgS ≪≫
        eqToIso (congrArg (fun h ↦ PurCompactSupport.push S h) r.hom_g)
    (pbcDerivedExtend (a.map Y)).map (qR.inv.app (JcR.obj M) ≫ PdR.map εR.inv) ≫
        (PurCompactSupport.comparison a d).app M =
      (PurCompactSupport.comparison a c).app M ≫ PcS.map (JcS.map e.inv) ≫
        (qS.inv.app (JcS.obj N) ≫ PdS.map εS.inv) ≫ PdS.map (JdS.map e.hom) := by
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change (PurCompactSupport.openExtension R id).mapDerivedCategory.obj M ≅
    (PurCompactSupport.push R h).obj
      ((PurCompactSupport.openExtension R ic).mapDerivedCategory.obj M) at εR
  change (PurCompactSupport.openExtension S id).mapDerivedCategory.obj N ≅
    (PurCompactSupport.push S h).obj
      ((PurCompactSupport.openExtension S ic).mapDerivedCategory.obj N) at εS
  change h ≫ gd = gc at hhg
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, id, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, hih, rfl⟩
  dsimp (config := { proj := false }) only
  have hc := by
    as_aux_lemma =>
      exact PurCompactSupport.properComparison_inverse_composition a r.hom d.g c.g
        r.hom_g hgR hgS ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj M)
  have hopen := by
    as_aux_lemma =>
      exact PurCompactSupport.refinementOpenMap_scalar a r hiR hiS M
  have hδc := by
    as_aux_lemma =>
      exact PurCompactSupport.comparison_factorization a c M
  have hδd := by
    as_aux_lemma =>
      exact PurCompactSupport.comparison_factorization a d M
  have hs := by
    as_aux_lemma =>
      exact refinement_normalized_word_square
        (pbcDerivedExtend (a.map X)) (pbcDerivedExtend (a.map c.Z))
        (pbcDerivedExtend (a.map d.Z)) (pbcDerivedExtend (a.map Y))
        (PurCompactSupport.openExtension R c.i).mapDerivedCategory
        (PurCompactSupport.openExtension R d.i).mapDerivedCategory
        (PurCompactSupport.openExtension S c.i).mapDerivedCategory
        (PurCompactSupport.openExtension S d.i).mapDerivedCategory
        (PurCompactSupport.push R r.hom) (PurCompactSupport.push S r.hom)
        (PurCompactSupport.push R d.g) (PurCompactSupport.push S d.g)
        (PurCompactSupport.push R c.g) (PurCompactSupport.push S c.g)
        (PurCompactSupport.geometricPushComposition R r.hom d.g hgR ≪≫
          eqToIso (congrArg (fun h ↦ PurCompactSupport.push R h) r.hom_g))
        (PurCompactSupport.geometricPushComposition S r.hom d.g hgS ≪≫
          eqToIso (congrArg (fun h ↦ PurCompactSupport.push S h) r.hom_g))
        (PurCompactSupport.properComparison a r.hom) (PurCompactSupport.properComparison a d.g)
        (PurCompactSupport.properComparison a c.g)
        (PurCompactSupport.openComparison a c.i) (PurCompactSupport.openComparison a d.i)
        (PurCompactSupport.refinementOpenMap S r hiS) M N e εR εS
        (PurCompactSupport.refinementOpenMap R r hiR) hεR hεS hopen
  run_tac do
    Mathlib.Tactic.runDefEqTactic (checkDefEq := false)
      (fun _ e => normalizeCoefficientAliases e)
      (some (← `(Lean.Parser.Tactic.location|
        at $(Lean.mkIdent `hc) $(Lean.mkIdent `hs)
          $(Lean.mkIdent `hδc) $(Lean.mkIdent `hδd) ⊢))) "coefficient aliases"
  with_reducible exact hs hc _ _ hδc hδd

/-- Completed scalar extension preserves the normalized proper/open refinement word.
The input is an ordinary open-unit comparison, before any chosen exceptional operation.
Source: Zheng 5.13--5.15; Stacks 0F7B and 0F7I, coefficient mate pasting
(blueprint: lem-sf-ring-refinement-scalar-word).

Proof: use a finite integral basis for the extension of coefficient fields, with
its compatible reductions on the ramified en subsystem. On the coefficient-system
site the proper scalar map is the counit-tensor mate and the open scalar map is
normalized by the open unit. Pasting these squares with the normalized open
refinement gives the same open transpose in either order. The adjunction bijection
makes the system maps equal. Whisker by the outer proper image and paste the proper
compositor; its counit formula respects these same coefficient squares. Invert the
open refinement maps. Apply normalized cofinal realization to this equality of
actual system maps, using the primitive proper, open and generator-map identities.
This gives the ordinary scalar square with target the scalar extension of K.
The supplied open comparisons are the constructed ones: open full faithfulness
makes the unit invertible, and the transpose of an invertible comparison is then
invertible too. Its normalization forces refinementRestriction to be invertible.
Postcomposition with that restriction and the Hom adjunction are injective, so
two normalized components coincide.
Finally transport that vertex to K' by e: insert e.inv before the refinement and
e.hom after it, using naturality. Finite-Tor bounds ensure the normalized tower
realization applies. The argument uses only the relative proper/open refinement;
absolute separatedness of X or Y is not needed. No equality of system arrows is
inferred from equality at finite reductions. -/
theorem ring_refinement_scalar_word
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (hi : ∀ s : RingStage.{max u v} l, (s.coefficients l).pull (c.i ≫ r.hom) =
        proEtaleRingCompositeCoefficients c.i r.hom
          ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
          ((s.coefficients l).ring X)
          ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
    (hg : ∀ s : RingStage.{max u v} l, (s.coefficients l).pull (r.hom ≫ d.g) =
        proEtaleRingCompositeCoefficients r.hom d.g
          ((s.coefficients l).ring Y) ((s.coefficients l).ring d.Z)
          ((s.coefficients l).ring c.Z)
          ((s.coefficients l).pull d.g) ((s.coefficients l).pull r.hom))
    (ε : ∀ s : RingStage.{max u v} l, RingStage.inclusion.{u, v} l Ω X s ⋙
          (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory ≅
        RingStage.inclusion.{u, v} l Ω X s ⋙
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory ⋙
            PurCompactSupport.push (s.coefficients l) r.hom))
    (hε : ∀ (s : RingStage.{max u v} l) (K : C.{u, v} l Ω X (s.stage l)),
        (PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _
            ((ε s).hom.app K) ≫
            PurCompactSupport.refinementRestriction (s.coefficients l) r (hi s)
              ((RingStage.inclusion.{u, v} l Ω X s).obj K) =
          (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit.app
            ((RingStage.inclusion.{u, v} l Ω X s).obj K))
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (K : C.{u, v} l Ω X (.integral E)) (K' : C.{u, v} l Ω X (.integral L))
    (e : (RingStage.inclusion.{u, v} l Ω X (.integral L)).obj K' ≅
      (pbcDerivedExtend ((PurCompactSupport.completedChange l E.carrier L.carrier i).map X)).obj
        ((RingStage.inclusion.{u, v} l Ω X (.integral E)).obj K)) :
    let a := PurCompactSupport.completedChange l E.carrier L.carrier i
    let Hc := PurCompactSupport.image ((RingStage.integral L).coefficients l) c
    let Hd := PurCompactSupport.image ((RingStage.integral L).coefficients l) d
    (pbcDerivedExtend (a.map Y)).map
        ((ringRefinementWord.{u, v} l Ω r (.integral E) (hg _) (ε _)).hom.app K) ≫
        (PurCompactSupport.comparison a d).app K.obj =
      (PurCompactSupport.comparison a c).app K.obj ≫ Hc.map e.inv ≫
        (ringRefinementWord.{u, v} l Ω r (.integral L) (hg _) (ε _)).hom.app K' ≫
        Hd.map e.hom := by
  have _ := hl
  have hE := normalized_refinement_unique.{max u v} r (hi (.integral E)) K.obj
    ((ε (.integral E)).hom.app K) (hε (.integral E) K)
  have hL := normalized_refinement_unique.{max u v} r (hi (.integral L)) K'.obj
    ((ε (.integral L)).hom.app K') (hε (.integral L) K')
  rcases c with ⟨Zc, gc, ic, hfc, hpc, hic⟩
  rcases d with ⟨Zd, gd, id, hfd, hpd, hid⟩
  rcases r with ⟨h, hih, hhg⟩
  change Zc ⟶ Zd at h
  change ic ≫ h = id at hih
  change ∀ s : RingStage.{max u v} l,
    RingStage.inclusion.{u, v} l Ω X s ⋙
      (PurCompactSupport.openExtension (s.coefficients l) id).mapDerivedCategory ≅
    RingStage.inclusion.{u, v} l Ω X s ⋙
      ((PurCompactSupport.openExtension (s.coefficients l) ic).mapDerivedCategory ⋙
        PurCompactSupport.push (s.coefficients l) h) at ε
  change h ≫ gd = gc at hhg
  subst gc
  let c : Compactification f := ⟨Zc, h ≫ gd, ic, hfc, hpc, hic⟩
  let d : Compactification f := ⟨Zd, gd, id, hfd, hpd, hid⟩
  let r : c.Refinement d := ⟨h, hih, rfl⟩
  have h := ambient_refinement_scalar.{max u v}
    (PurCompactSupport.completedChange l E.carrier L.carrier i)
    r (hi (.integral E)) (hi (.integral L)) (hg (.integral E)) (hg (.integral L))
    K.obj K'.obj e ((ε (.integral E)).app K) ((ε (.integral L)).app K') hE hL
  dsimp only [ringRefinementWord, properOpenRefinementWord,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, PurCompactSupport.image, Functor.comp,
    RingStage.coefficients, RingStage.inclusion, ObjectProperty.ι, inducedFunctor,
    PurCompactSupport.push] at h ⊢
  with_reducible exact h

end WeilConjectures.ConstructibleExceptionalCoefficients
