/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingEndpointPasting
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedPushComposition

/-! # Cancellation of the fixed finite endpoint coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.finite
  AlgebraicGeometry.Scheme.ProEt CategoryTheory.MorphismProperty
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

attribute [local irreducible] finiteFixedOpenAt finiteFixedPushIso
  FrobeniusExchange.fixedCompactModel FrobeniusExchange.fixedRefinementOpen
  PurCompactSupport.finiteImageIso sfIntrinsicDerivedEquivalence
  PurCompactSupport.geometricPushComposition
  AlgebraicGeometry.ProEtale.finiteDirectImageComposition

private theorem cancel_endpoint_coordinates
    {C D T C' D' T' : Type*}
    [Category C] [Category D] [Category T]
    [Category C'] [Category D'] [Category T']
    (e : C ⥤ C') (ed : D ⥤ D') (q : T ⥤ T')
    (F : C' ⥤ D') (G : D' ⥤ T') (H : C' ⥤ T')
    (F₀ : C ⥤ D) (G₀ : D ⥤ T) (H₀ : C ⥤ T)
    (a : e ⋙ F ≅ F₀ ⋙ ed) (b : ed ⋙ G ≅ G₀ ⋙ q)
    (c : e ⋙ H ≅ H₀ ⋙ q) (z : H ≅ F ⋙ G)
    {M : C} {N : D} {Mc : C'} {Nd : D'} {Ic Id : T'}
    (uc : Mc ≅ e.obj M) (ud : Nd ≅ ed.obj N) (v : N ≅ F₀.obj M)
    {P : T} (z₁ : H₀.obj M ≅ P) (z₂ : P ≅ G₀.obj (F₀.obj M))
    (ic : H.obj Mc ≅ Ic) (id : G.obj Nd ≅ Id)
    {Uc Ud : T'} (ac : Ic ≅ Uc) (bc : Uc ≅ q.obj (H₀.obj M))
    (ad : Id ≅ Ud) (bd : Ud ≅ q.obj (G₀.obj N))
    (hz : z.app (e.obj M) ≪≫ G.mapIso (a.app M) ≪≫ b.app (F₀.obj M) =
      c.app M ≪≫ q.mapIso (z₁ ≪≫ z₂))
    (hc : H.mapIso uc ≪≫ c.app M = ic ≪≫ ac ≪≫ bc)
    (hd : G.mapIso ud ≪≫ b.app N = id ≪≫ ad ≪≫ bd) :
    z.app Mc ≪≫ G.mapIso
        (ud ≪≫ ed.mapIso v ≪≫ (a.app M).symm ≪≫ F.mapIso uc.symm).symm ≪≫ id =
      ic ≪≫ ac ≪≫ bc ≪≫ q.mapIso (z₁ ≪≫ z₂ ≪≫ G₀.mapIso v.symm) ≪≫
        bd.symm ≪≫ ad.symm := by
  have h : (z.app Mc ≪≫ G.mapIso
        (ud ≪≫ ed.mapIso v ≪≫ (a.app M).symm ≪≫ F.mapIso uc.symm).symm) ≪≫
        (G.mapIso ud ≪≫ b.app N) =
      (H.mapIso uc ≪≫ c.app M) ≪≫ q.mapIso ((z₁ ≪≫ z₂) ≪≫ G₀.mapIso v.symm) := by
    apply Iso.ext
    have hn := z.hom.naturality uc.hom
    have hb := b.hom.naturality v.inv
    simp only [Functor.comp_map] at hn hb
    have hh := congrArg Iso.hom hz
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp] at hh
    simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_trans,
      Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Category.assoc]
    rw [← reassoc_of% hn]
    simp only [Iso.inv_hom_id_map_assoc]
    rw [hb, reassoc_of% hh]
  rw [hc, hd] at h
  have hh := congrArg (fun t ↦ t ≪≫ (ad ≪≫ bd).symm) h
  simpa only [Iso.trans_assoc, Iso.trans_symm, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.refl_trans, Iso.trans_refl] using hh

/-- The explicit finite open witness has the specified intrinsic endpoint word.
This is only the endpoint equation, without existence or open-adjunction normalization.
Source: compactification-coherence proof, second paragraph; Stacks 03D6 and 0F7B
(blueprint: lem-sf-finite-ring-endpoint-cancellation).

Proof: start with finiteFixedPushIso_composition for r.hom and d.g. Insert the
explicit definition of finiteFixedRefinementOpenIso. Naturality cancels its two
inner inverse coordinate pairs, leaving the fixed proper/open map whiskered by
the outer direct image. At each endpoint apply finiteFixedEndpointModelAt: the
remaining open/direct-image coordinate is finiteImageIso followed by the inverse
image of the equivalence counit and fixedCompactModel. Associate the fixed
compositor at the object, and postcompose by the inverse of the
endpoint coordinate at d. Cancel the two inverse pairs. The remaining right word is
finiteImageIso at c followed by intrinsicRefinement: expand recordedRefinementCore
and apply recordedCore_intrinsic, or use the definition of intrinsicRefinement with
exactly its original category instances. This argument uses neither hi nor the
open-unit equation. Identity refinements, zero objects and empty opens use the same
isomorphism cancellation; no nonvanishing or nonemptiness assumption is required. -/
theorem finiteFixedEndpointCancellation
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin
      (Padic.coefficientExtensionRing l E (n + 1)) X)
    (hg : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (r.hom ≫ d.g) =
      proEtaleRingCompositeCoefficients r.hom d.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull d.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)) :
      ((PurCompactSupport.geometricPushComposition
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r.hom d.g hg ≪≫
      eqToIso (congrArg (fun h ↦ PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) h) r.hom_g)).symm.app _) ≪≫
      (PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.g).mapIso
          (finiteFixedRefinementOpenIso l E n r O).symm ≪≫
      (PurCompactSupport.finiteImageIso l E n d).app O.K =
    (PurCompactSupport.finiteImageIso l E n c).app O.K ≪≫
      FrobeniusExchange.intrinsicRefinement
        (Padic.coefficientExtensionRing l E (n + 1)) r O := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let e := sfIntrinsicDerivedEquivalence X A
  let K := e.inverse.obj O.K
  let Jc := (AlgebraicGeometry.ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory
  let Pc := (AlgebraicGeometry.ProEtale.lowerStar B c.g).rightDerivedFunctor
  let Pd := (AlgebraicGeometry.ProEtale.lowerStar B d.g).rightDerivedFunctor
  let Pr := (AlgebraicGeometry.ProEtale.lowerStar B r.hom).rightDerivedFunctor
  let z := (PurCompactSupport.geometricPushComposition R r.hom d.g hg ≪≫
    eqToIso (congrArg (fun h ↦ PurCompactSupport.push R h) r.hom_g)).symm
  let z₁ := (eqToIso (congrArg (fun h ↦
    (AlgebraicGeometry.ProEtale.lowerStar B h).rightDerivedFunctor) r.hom_g.symm)).app
      (Jc.obj K)
  let z₂ := (AlgebraicGeometry.ProEtale.finiteDirectImageComposition
    (ULift.{w + 1} A) r.hom d.g).app (Jc.obj K)
  have h := cancel_endpoint_coordinates
    (sfIntrinsicDerivedEquivalence c.Z A).functor
    (sfIntrinsicDerivedEquivalence d.Z A).functor
    (sfIntrinsicDerivedEquivalence Y A).functor
    (PurCompactSupport.push R r.hom) (PurCompactSupport.push R d.g)
    (PurCompactSupport.push R c.g) Pr Pd Pc
    (finiteFixedPushIso l E n r.hom) (finiteFixedPushIso l E n d.g)
    (finiteFixedPushIso l E n c.g) z
    (finiteFixedOpenAt l E n c.i O) (finiteFixedOpenAt l E n d.i O)
    (FrobeniusExchange.fixedRefinementOpen A r O) z₁ z₂
    ((PurCompactSupport.finiteImageIso l E n c).app O.K)
    ((PurCompactSupport.finiteImageIso l E n d).app O.K)
    ((sfIntrinsicCompactSupport c A).mapIso (e.counitIso.app O.K).symm)
    ((FrobeniusExchange.fixedCompactModel A c).app K)
    ((sfIntrinsicCompactSupport d A).mapIso (e.counitIso.app O.K).symm)
    ((FrobeniusExchange.fixedCompactModel A d).app K)
    (finiteFixedPushIso_composition l E n r.hom d.g c.g r.hom_g hg (Jc.obj K))
    (finiteFixedEndpointModelAt l E n c O) (finiteFixedEndpointModelAt l E n d O)
  exact h

end WeilConjectures.ConstructibleExceptionalCoefficients
