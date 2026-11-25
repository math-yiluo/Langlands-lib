/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.CompactSupportProperImageTower.CompactSupportProperImageTower
import WeilConjectures.SmoothPurity.Sf.SfNormalizedInputTransition
import WeilConjectures.SmoothPurity.Sf.SfDirectImageRestrictionPasting

/-! # The ordinary direct-image adjacent coefficient identity

Source: Stacks Tags 03EK, 06YY, 0D6E and 0D6J; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-sf-direct-image-adjacent-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

private theorem presentationOfPasting
    {A B AY BY C D : Type*}
    [Category A] [Category B] [Category AY] [Category BY] [Category C] [Category D]
    (R : A ⥤ C) (S : B ⥤ C) (P : B ⥤ A) (Q : BY ⥤ AY)
    (Dm : A ⥤ AY) (Dn : B ⥤ BY) (RY : AY ⥤ D) (SY : BY ⥤ D) (G : C ⥤ D)
    (cX : P ⋙ R ≅ S) (cY : Q ⋙ RY ≅ SY) (d : P ⋙ Dm ≅ Dn ⋙ Q)
    (cm : R ⋙ G ≅ Dm ⋙ RY) (cn : S ⋙ G ≅ Dn ⋙ SY)
    (U : A) (V : B) (f : U ⟶ P.obj V) (t : R.obj U ⟶ S.obj V)
    (hi : R.map f ≫ cX.hom.app V = t)
    (hc : cm.hom.app (P.obj V) ≫ RY.map (d.hom.app V) ≫
        cY.hom.app (Dn.obj V) = G.map (cX.hom.app V) ≫ cn.hom.app V) :
    cm.inv.app U ≫ G.map t ≫ cn.hom.app V =
      RY.map (Dm.map f ≫ d.hom.app V) ≫ cY.hom.app (Dn.obj V) := by
  apply (cancel_epi (cm.hom.app U)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← hi, G.map_comp]
  simp only [Category.assoc, RY.map_comp]
  rw [← hc]
  have hn := cm.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- The completed restriction square transports the canonical reduction map to the
finite direct-image coefficient square. This is an identity of adjacent arrows for
an arbitrary completed-coefficient complex; it does not construct an inverse system
or assume that the complex is derived complete.

Source: Stacks Tags 03EK, 06YY, 0D6E and 0D6J; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-sf-direct-image-adjacent-presentation).

Proof: compute on a K-flat representative of K. The adjunction defining reductionMap
has unit x ↦ 1 tensor x, so its adjunct sends a tensor x to the quotient of a tensor x.
After completed scalar restriction and its composition comparison this is precisely
sfDerivedReductionTransition, by its characterization on K-flat representatives.
The two finite direct images are definitionally equal: both coefficient maps are the
sheafification transpose of the constant-section map. The ordinary completed/finite
restriction squares and d.ordinary preserve these sections by their normalizations.
Their composite pastes agree on sections. Derive the pastes using a K-injective
representative, resolving its restriction once more when necessary. The equations
sfDerivedRestrictionComparison_existsUnique and d.normalization identify these pastes
with the displayed derived comparisons. Cancel the invertible comparison maps and
apply functoriality to the preceding reduction identity; this gives the claimed
formula. K-flat localization and naturality extend it to arbitrary K. The proof never
assumes that restriction preserves K-injectives and applies to zero complexes too. -/
theorem sfDirectImageTransition_presentation
    (d : CompactSupportProperImageTower.DirectData l E p)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    sfDirectImageTransition l E p K n =
      (coefficientFiniteDerivedRestriction l E Y (n + 1)).map
        ((compactSupportLevelDirectImage l E p (n + 1)).rightDerivedFunctor.map
          (CompactSupportProperImageTower.reductionMap l E X K n) ≫
          (d.comparison n).hom.app ((coefficientFiniteDerivedExtension l E X n).obj K)) ≫
        (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n)).hom.app
          ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
            ((coefficientFiniteDerivedExtension l E X n).obj K)) := by
  have h := presentationOfPasting
    (coefficientFiniteDerivedRestriction l E X (n + 1))
    (coefficientFiniteDerivedRestriction l E X n)
    (normalizedDVRRes l E X (Nat.le_succ n))
    (normalizedDVRRes l E Y (Nat.le_succ n))
    (compactSupportLevelDirectImage l E p (n + 1)).rightDerivedFunctor
    (compactSupportLevelDirectImage l E p n).rightDerivedFunctor
    (coefficientFiniteDerivedRestriction l E Y (n + 1))
    (coefficientFiniteDerivedRestriction l E Y n)
    (sfCompletedDerivedDirectImage l E p)
    (compactSupportSystemRestrictionComp l E X (Nat.le_succ n))
    (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n))
    (d.comparison n)
    (sfDerivedRestrictionComparison l E p (n + 1))
    (sfDerivedRestrictionComparison l E p n)
    ((coefficientFiniteDerivedExtension l E X (n + 1)).obj K)
    ((coefficientFiniteDerivedExtension l E X n).obj K)
    (CompactSupportProperImageTower.reductionMap l E X K n)
    ((sfDerivedReductionTransition l E X n).app K)
    (sfNormalizedInputTransition l E K n)
    (sfDirectImageRestriction_pasting l E p d n _)
  simpa only [sfDirectImageTransition, sfDirectImageTerm, sfFiniteDerivedDirectImage,
    coefficientFiniteDerivedExtension, coefficientFiniteDerivedRestriction,
    Functor.comp_obj] using h

end WeilConjectures
