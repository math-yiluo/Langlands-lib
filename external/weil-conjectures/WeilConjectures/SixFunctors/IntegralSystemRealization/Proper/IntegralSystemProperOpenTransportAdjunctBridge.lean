/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenLambdaBridge

/-! Bridge cancellation form of the transported adjunct normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  DerivedCategory.Q CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  CategoryTheory.constantSheaf CategoryTheory.Functor.mapDerivedCategoryNatIso
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem left_transport
    {A B : Type*} [Category A] [Category B]
    {J J' : A ⥤ B} {P P' : B ⥤ A}
    (a : J ⊣ P) (a' : J' ⊣ P') (e : P ≅ P')
    {X : A} {Y : B} (f : J'.obj X ⟶ Y) :
    a.homEquiv _ _ (((a.ofNatIsoRight e).leftAdjointUniq a').hom.app X ≫ f) ≫
        e.hom.app Y = a'.homEquiv _ _ f := by
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]

private theorem adjunct_bridge_assembly
    {A B : Type*} [Category A] [Category B]
    {J J' : A ⥤ B} {P P' : B ⥤ A}
    (a : J ⊣ P) (a' : J' ⊣ P') (e : P ≅ P') (eJ : J ≅ J')
    (heJ : eJ = (a.ofNatIsoRight e).leftAdjointUniq a')
    {X X' : A} {Y Y' : B} (v : X ≅ X') (t : Y' ≅ Y)
    (g : J'.obj X' ⟶ Y') (w : P.obj Y ≅ X) (z : P'.obj Y' ≅ X')
    (hl : w.hom ≫ v.hom = P.map t.inv ≫ e.hom.app Y' ≫ z.hom)
    (hg : a'.homEquiv _ _ g = z.inv) :
    a.homEquiv _ _ (J.map v.hom ≫ eJ.hom.app X' ≫ g ≫ t.hom) ≫ e.hom.app Y =
      w.inv ≫ e.hom.app Y := by
  have hinv := congrArg (fun f ↦ w.inv ≫ f ≫ z.inv) hl
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at hinv
  rw [eJ.hom.naturality_assoc, heJ, left_transport,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, hg]
  rw [← Category.assoc, hinv]
  simp only [Category.assoc]
  rw [← e.hom.naturality t.hom, ← Category.assoc (P.map t.inv),
    ← P.map_comp, t.inv_hom_id, P.map_id, Category.id_comp]

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The bridge-transported intrinsic gamma has the prescribed adjunct after converting
its codomain to canonical semilinear coordinates.  This is the mate-cancellation
step: expand the four bridge factors, apply the intrinsic `gamma_adjunct` equation,
and identify the resulting composite with `properOpenLambda`; the final item
cancels the displayed canonical pullback isomorphism.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0F7B and 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-adjunct-bridge)
-/
theorem transportedGamma_adjunct_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (o.extension i).adj.homEquiv _ _
        (((Operations.shriek l E o i).map ((b.push l E r).hom.app M) ≫
          (b.shriek l E i).hom.app
            ((ProEtale.SemilinearProperOpen.R (scalarRings l E)
              (scalarTransitions l E) r).obj M) ≫
          (ProEtale.SemilinearProperOpen.gamma (scalarRings l E)
            (scalarTransitions l E) k r p i h).app M ≫
          (b.push l E p).inv.app
            ((ProEtale.SemilinearProperOpen.J (scalarRings l E)
              (scalarTransitions l E) k).obj M) ≫
          (Operations.push l E o p).map
            ((b.shriek l E k).inv.app M))) ≫
      (b.pull l E i).hom.app
        ((Operations.shriek l E o k ⋙ Operations.push l E o p).obj M) =
      (properOpenLambda l E o c a k r p i h).inv.app M ≫
        (b.pull l E i).hom.app
          ((Operations.shriek l E o k ⋙ Operations.push l E o p).obj M) := by
  let t := (b.push l E p).symm.app
      ((ProEtale.SemilinearProperOpen.J
        (scalarRings l E) (scalarTransitions l E) k).obj M) ≪≫
    (Operations.push l E o p).mapIso ((b.shriek l E k).symm.app M)
  let v := (b.push l E r).hom.app M
  let g := (ProEtale.SemilinearProperOpen.gamma
    (scalarRings l E) (scalarTransitions l E) k r p i h).app M
  let z := ProEtale.SemilinearProperOpen.lambda
    (scalarRings l E) (scalarTransitions l E) k r p i h
  have hl := properOpenLambda_bridge l E o c a b k r p i h M
  change (properOpenLambda l E o c a k r p i h).hom.app M ≫ v =
    (pull l E i).map t.inv ≫ (b.pull l E i).hom.app _ ≫ z.hom.app M at hl
  exact adjunct_bridge_assembly (o.extension i).adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) i)
    (b.pull l E i) (b.shriek l E i) (by unfold CanonicalBridge.shriek; rfl)
    ((b.push l E r).app M) t g
    ((properOpenLambda l E o c a k r p i h).app M) (z.app M) hl
    (ProEtale.SemilinearProperOpen.gamma_adjunct
      (scalarRings l E) (scalarTransitions l E) k r p i h M).1

end WeilConjectures.IntegralSystemRealization
