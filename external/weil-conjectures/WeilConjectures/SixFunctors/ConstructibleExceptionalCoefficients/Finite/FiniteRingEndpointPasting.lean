/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates

/-! # Finite endpoint pasting before cancelling realization coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.finite
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

private theorem endpoint_coordinates
    {C₀ C₁ D₀ D₁ Y₀ Y₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Category Y₀] [Category Y₁]
    (ec : C₀ ⥤ C₁) (ed : D₀ ⥤ D₁) (q : Y₀ ⥤ Y₁)
    (J₀ : C₀ ⥤ D₀) (J₁ J₂ : C₁ ⥤ D₁)
    (P₀ : D₀ ⥤ Y₀) (P₁ P₂ : D₁ ⥤ Y₁)
    (o : J₁ ≅ J₂) (p : P₁ ≅ P₂)
    (u : ec ⋙ J₂ ≅ J₀ ⋙ ed) (v : ed ⋙ P₂ ≅ P₀ ⋙ q)
    {M : C₀} {M' : C₁} (a : M' ≅ ec.obj M) :
    P₁.mapIso (J₁.mapIso a ≪≫ (Functor.isoWhiskerLeft ec o ≪≫ u).app M) ≪≫
        (Functor.isoWhiskerLeft ed p ≪≫ v).app (J₀.obj M) =
      (Functor.isoWhiskerRight o P₁ ≪≫ Functor.isoWhiskerLeft J₂ p).app M' ≪≫
        (J₂ ⋙ P₂).mapIso a ≪≫
        ((Functor.associator ec J₂ P₂).symm ≪≫ Functor.isoWhiskerRight u P₂ ≪≫
          Functor.associator J₀ ed P₂ ≪≫ Functor.isoWhiskerLeft J₀ v ≪≫
          (Functor.associator J₀ P₀ q).symm).app M := by
  apply Iso.ext
  have ho := o.hom.naturality a.hom
  have hp := p.hom.naturality (u.hom.app M)
  have ha := p.hom.naturality (J₂.map a.hom)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [← P₁.map_comp_assoc (J₁.map a.hom) (o.hom.app (ec.obj M)), ho,
    P₁.map_comp, Category.assoc, reassoc_of% hp, ← reassoc_of% ha]

/-- The open/direct-image coordinates at one finite compactification endpoint.
Source: compactification-coherence proof, second paragraph; Stacks 00YV and 03D6
(blueprint: lem-sf-finite-ring-endpoint-pasting).

Proof: apply naturality to the finite open comparison and then to the separately
derived finite direct-image comparison. The fixed realization comparisons paste
by the functor associator. The equivalence counit identifies the retained object
with the original one. This is the generic endpoint_coordinates calculation. -/
theorem finiteFixedEndpointModelAt
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} (c : Compactification f)
    (O : FrobeniusExchange.CompactOrigin (Padic.coefficientExtensionRing l E (n + 1)) X) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let e := sfIntrinsicDerivedEquivalence X A
    let K := e.inverse.obj O.K
    (PurCompactSupport.push R c.g).mapIso (finiteFixedOpenAt l E n c.i O) ≪≫
      (finiteFixedPushIso l E n c.g).app
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{w + 1} (ULift.{w + 1} A)) c.i).mapDerivedCategory.obj K) =
    (PurCompactSupport.finiteImageIso l E n c).app O.K ≪≫
      (sfIntrinsicCompactSupport c A).mapIso (e.counitIso.app O.K).symm ≪≫
      (FrobeniusExchange.fixedCompactModel A c).app K := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let ringAdd : (proEtaleRingModuleDirectImage c.g (R.ring Y) (R.ring c.Z)
      (R.pull c.g)).Additive :=
    proEtaleRingModuleDirectImage_additive c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)
  let pushAdd := (proEtaleConstantModuleDirectImage_additive_leftExact c.g A).1
  let openAdd := (sfIntrinsicExtensionByZero_exact c.i A).1
  let openLim := (sfIntrinsicExtensionByZero_exact c.i A).2.1
  let openColim := (sfIntrinsicExtensionByZero_exact c.i A).2.2
  let o := @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
    _ openAdd _ _ openLim openColim (PurCompactSupport.finiteOpenIso l E n c.i)
  let p := @Functor.rightDerivedFunctorNatIso _ _ _ _ _ _ _ _ _ _ _
    ringAdd pushAdd (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n c.g))
  exact endpoint_coordinates _ _ _ _ _ _ _ _ _ o p
    (FrobeniusExchange.fixedDerivedOpenModel A c.i)
    (sfIntrinsicDerivedDirectImageComparison c.g A)
    ((sfIntrinsicDerivedEquivalence X A).counitIso.app O.K).symm

end WeilConjectures.ConstructibleExceptionalCoefficients
