/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingOpenMapInvertibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison

/-! # The open-unit step of ring-stage compactification refinement

Source: Stacks 0F7B and 0F7I; Zheng Section 5, Lemma 5.13 and Constructions 5.14--5.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] constructionInclusionShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The proper/open word, with explicit components and generic naturality.
Source: composition and naturality of functor isomorphisms
(blueprint: lem-sf-ring-open-refinement). -/
def properOpenRefinementWord
    {A B C D Z : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category Z]
    (I : A ⥤ B) (Jc : B ⥤ C) (Jd : B ⥤ D)
    (Pr : C ⥤ D) (Pd : D ⥤ Z) (Pc : C ⥤ Z)
    (q : Pr ⋙ Pd ≅ Pc) (ε : I ⋙ Jd ≅ I ⋙ (Jc ⋙ Pr)) :
    I ⋙ (Jc ⋙ Pc) ≅ I ⋙ (Jd ⋙ Pd) :=
  NatIso.ofComponents
    (fun K ↦ q.symm.app (Jc.obj (I.obj K)) ≪≫ Pd.mapIso (ε.app K).symm) (by
      intro K L f
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
        Functor.mapIso_hom, Functor.comp_map]
      rw [← Category.assoc, q.inv.naturality]
      simp only [Functor.comp_map, Category.assoc]
      rw [← Pd.map_comp]
      have h := ε.inv.naturality f
      dsimp only [Functor.comp_map] at h
      rw [h, Pd.map_comp])

/-- Push the inverse open-unit isomorphism through the outer proper map, after the
inverse proper compositor. This is an explicit word, independent of any chosen
exceptional operation or scalar comparison.
Source: Stacks 0F7B, 0F7I
(blueprint: lem-sf-ring-open-refinement). -/
def ringRefinementWord {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{max u v} l)
    (hg : (s.coefficients l).pull (r.hom ≫ d.g) =
      proEtaleRingCompositeCoefficients r.hom d.g
        ((s.coefficients l).ring Y) ((s.coefficients l).ring d.Z)
        ((s.coefficients l).ring c.Z)
        ((s.coefficients l).pull d.g) ((s.coefficients l).pull r.hom))
    (ε : RingStage.inclusion.{u, v} l Ω X s ⋙
        (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory ≅
      RingStage.inclusion.{u, v} l Ω X s ⋙
        ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory ⋙
          PurCompactSupport.push (s.coefficients l) r.hom)) :
    RingStage.inclusion.{u, v} l Ω X s ⋙ PurCompactSupport.image (s.coefficients l) c ≅
      RingStage.inclusion.{u, v} l Ω X s ⋙ PurCompactSupport.image (s.coefficients l) d :=
  let I := RingStage.inclusion.{u, v} l Ω X s
  let Jc := (PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory
  let Jd := (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory
  let Pr := PurCompactSupport.push (s.coefficients l) r.hom
  let Pd := PurCompactSupport.push (s.coefficients l) d.g
  let q := PurCompactSupport.geometricPushComposition (s.coefficients l) r.hom d.g hg ≪≫
    eqToIso (congrArg (fun h ↦ PurCompactSupport.push (s.coefficients l) h) r.hom_g)
  properOpenRefinementWord I Jc Jd Pr Pd
    (PurCompactSupport.push (s.coefficients l) c.g) q ε

private theorem ringStagePull_comp (s : RingStage.{w} l)
    {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W) :
    (s.coefficients l).pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      ((s.coefficients l).ring W) ((s.coefficients l).ring V)
      ((s.coefficients l).ring U) ((s.coefficients l).pull k)
      ((s.coefficients l).pull h) := by
  cases s with
  | integral E => exact PurCompactSupport.completedPull_comp l E.carrier h k
  | finite E n =>
    exact (proEtaleConstantRingCompositeCoefficients_eq h k
      (Padic.coefficientExtensionRing l E.carrier n)).symm

private theorem pushCongr_shift (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} {g h : U ⟶ V} (e : g = h) :
    (eqToIso (congrArg (fun k : U ⟶ V ↦ PurCompactSupport.push R k) e)).hom.CommShift ℤ := by
  cases e
  dsimp
  infer_instance

private theorem properOpenRefinementWord_shift
    {A B C D Z : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category Z]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift Z ℤ]
    (I : A ⥤ B) (Jc : B ⥤ C) (Jd : B ⥤ D)
    (Pr : C ⥤ D) (Pd : D ⥤ Z) (Pc : C ⥤ Z)
    [I.CommShift ℤ] [Jc.CommShift ℤ] [Jd.CommShift ℤ]
    [Pr.CommShift ℤ] [Pd.CommShift ℤ] [Pc.CommShift ℤ]
    (q : Pr ⋙ Pd ≅ Pc) (ε : I ⋙ Jd ≅ I ⋙ (Jc ⋙ Pr))
    [q.hom.CommShift ℤ] [ε.hom.CommShift ℤ] :
    (properOpenRefinementWord I Jc Jd Pr Pd Pc q ε).hom.CommShift ℤ := by
  have he : properOpenRefinementWord I Jc Jd Pr Pd Pc q ε =
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft Jc q.symm) ≪≫
        Functor.isoWhiskerLeft I (Functor.associator Jc Pr Pd).symm ≪≫
        (Functor.associator I (Jc ⋙ Pr) Pd).symm ≪≫
        Functor.isoWhiskerRight ε.symm Pd ≪≫ Functor.associator I Jd Pd := by
    ext K
    simp [properOpenRefinementWord]
  rw [he]
  dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom]
  infer_instance

/-- The open-unit comparison is an isomorphism on the full finite-Tor ring-stage domain;
its proper pushforward word preserves the inherited shifts.
Source: Stacks 0F7B, 0F7I; Zheng 5.13--5.15; the exceptional construction, step 6
(blueprint: lem-sf-ring-open-refinement).

Proof: for a finite coefficient ring, restrict the proper image of extension by zero
to the open X. Open restriction and the clopen section in the inverse image of X
identify this restriction with the input. The adjunct of the inverse identification
is the open-unit comparison. Proper base change on the complement shows its cone
vanishes for bounded constructible inputs of etale origin, hence for this finite-Tor
subcategory. Its transpose is exactly the displayed open unit. All constituents are
natural, so they define the stated natural isomorphism, rather than unrelated choices
of objectwise maps. For completed integral coefficients apply the same word to the
normalized strict reduction system of the finite-Tor input. Finite-level proper
base change makes its cone vanish at every evaluation; conservative system
evaluations make the actual system comparison invertible. Apply total limit to
this isomorphism. The primitive open/proper and generator-map identities of
integral compactification system realization identify its value with the stated
ordinary open-unit word, including the transpose normalization. System transport
and naturality of the primitive realizations assemble the components naturally.
All these are actual system maps before total limit; no equality of arrows is
inferred from reductions alone. Canonical exact open
and proper derived adjunctions, their units and counits, and the pullback
compositor commute with shifts. Their inverse-transpose word and the conjugate
proper compositor therefore do too. In the integral case uniqueness of the
open-unit construction on the shifted normalized system identifies the shifted
comparison with the comparison on the shifted input. On the Roos totalizer the
shift by r acts by the product shift on the first cone coordinate and by (-1)^r
times that shift on the second. Termwise primitive maps respect these formulas;
the normalization comparison has zero second component, which remains zero.
Pasting these squares gives shift compatibility
of the explicit component word ringRefinementWord. The construction applies to identity refinements
and zero inputs, and requires only relative separatedness of f. -/
theorem exists_ring_open_refinement
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (s : RingStage.{max u v} l) :
    ∃ (hi : (s.coefficients l).pull (c.i ≫ r.hom) =
        proEtaleRingCompositeCoefficients c.i r.hom
          ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
          ((s.coefficients l).ring X)
          ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
      (hg : (s.coefficients l).pull (r.hom ≫ d.g) =
        proEtaleRingCompositeCoefficients r.hom d.g
          ((s.coefficients l).ring Y) ((s.coefficients l).ring d.Z)
          ((s.coefficients l).ring c.Z)
          ((s.coefficients l).pull d.g) ((s.coefficients l).pull r.hom))
      (ε : RingStage.inclusion.{u, v} l Ω X s ⋙
          (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory ≅
        RingStage.inclusion.{u, v} l Ω X s ⋙
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory ⋙
            PurCompactSupport.push (s.coefficients l) r.hom)),
      (∀ K : C.{u, v} l Ω X (s.stage l),
        (PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _
            (ε.hom.app K) ≫
            PurCompactSupport.refinementRestriction (s.coefficients l) r hi
              ((RingStage.inclusion.{u, v} l Ω X s).obj K) =
          (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit.app
            ((RingStage.inclusion.{u, v} l Ω X s).obj K)) ∧
        (ringRefinementWord.{u, v} l Ω r s hg ε).hom.CommShift ℤ := by
  let hi := ringStagePull_comp l s c.i r.hom
  let hg := ringStagePull_comp l s r.hom d.g
  let I := RingStage.inclusion.{u, v} l Ω X s
  let α := Functor.whiskerLeft I
    (PurCompactSupport.refinementOpenMap (s.coefficients l) r hi)
  have hα : IsIso α := by
    let : ∀ K, IsIso (α.app K) := fun K ↦ ringOpenMap_isIso l Ω D hl r s hi K
    exact NatIso.isIso_of_isIso_app α
  let := hα
  let ε := asIso α
  refine ⟨hi, hg, ε, ?_, ?_⟩
  · intro K
    exact PurCompactSupport.refinementOpenMap_normalization (s.coefficients l) r hi (I.obj K)
  · let := PurCompactSupport.refinementOpenMap_shift (s.coefficients l) r hi
    have : ε.hom.CommShift ℤ := by
      dsimp only [ε, α, asIso]
      infer_instance
    let := this
    let := PurCompactSupport.geometricPushComposition_shift (s.coefficients l)
      r.hom d.g hg
    let := pushCongr_shift (s.coefficients l) r.hom_g
    have hq : (PurCompactSupport.geometricPushComposition (s.coefficients l)
        r.hom d.g hg ≪≫ eqToIso (congrArg
          (fun h ↦ PurCompactSupport.push (s.coefficients l) h) r.hom_g)).hom.CommShift ℤ := by
      dsimp only [Iso.trans_hom]
      infer_instance
    let := hq
    dsimp only [ringRefinementWord]
    apply properOpenRefinementWord_shift

end WeilConjectures.ConstructibleExceptionalCoefficients
