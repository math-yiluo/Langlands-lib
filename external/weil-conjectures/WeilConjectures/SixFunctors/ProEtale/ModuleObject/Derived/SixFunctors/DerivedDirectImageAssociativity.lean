/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-! Source: blueprint composition isomorphism and its canonicity and associativity. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Canonical derived direct-image associativity.
Source: blueprint composition isomorphism; Canonicity and associativity;
Stacks Tags 08BJ, 070I, 070Y and 0D6E.
(blueprint: lem-sfb-derived-direct-image-associativity).

Proof: Choose a K-injective resolution I of the input. Exact inverse image is left adjoint to
each direct image, so each intermediate direct image of I is K-injective. The universal
right-derived comparison, evaluated on Q(I), is lowerStarComp.inv followed by the
canonical evaluation isomorphisms. Thus both bracketings are the cells of the two
underived inverse compositors, with the displayed associator. The equation
lowerStarComp_assoc identifies these underived composites, including lowerStarCongr
for the equality of the two composite scheme maps. Apply the finite word diagram
descent theorem to obtain equality on the entire unbounded derived category.
-/
theorem derivedDirectImageAssociativity
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    DirectImageCompositionAssociative Λ f g h := by
  -- Apply generic derived associativity with the scheme-map transport in the third cell.
  have ho := congrArg Iso.hom (lowerStarComp_assoc Λ f g h)
  have hc := Functor.rightDerivedFunctorCompIso'_assoc
    (lowerStar Λ f) (lowerStar Λ g) (lowerStar Λ h)
    (lowerStar Λ (f ≫ g)) (lowerStar Λ (g ≫ h)) (lowerStar Λ (f ≫ g ≫ h))
    (lowerStarComp Λ f g) (lowerStarComp Λ g h)
    (lowerStarComp Λ (f ≫ g) h ≪≫ lowerStarCongr Λ (Category.assoc f g h))
    (lowerStarComp Λ f (g ≫ h)) (by
      apply NatTrans.ext
      funext M
      have hm := congr_app ho M
      simpa using hm.symm)
  have hpost : Functor.rightDerivedFunctorCompIso'
      (lowerStar Λ (f ≫ g)) (lowerStar Λ h)
      (lowerStarComp Λ (f ≫ g) h ≪≫ lowerStarCongr Λ (Category.assoc f g h)) =
      Functor.rightDerivedFunctorCompIso' (lowerStar Λ (f ≫ g)) (lowerStar Λ h)
        (lowerStarComp Λ (f ≫ g) h) ≪≫
        Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h)) := by
    apply Iso.ext
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorNatIso,
      Functor.rightDerivedFunctorNatTrans_comp]
  rw [hpost] at hc
  have hci :
      Functor.isoWhiskerRight
          (Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ g)
            (lowerStarComp Λ f g)) (lowerStar Λ h).rightDerivedFunctor ≪≫
        Functor.rightDerivedFunctorCompIso' (lowerStar Λ (f ≫ g)) (lowerStar Λ h)
          (lowerStarComp Λ (f ≫ g) h) ≪≫
        Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h)) =
      Functor.isoWhiskerLeft (lowerStar Λ f).rightDerivedFunctor
          (Functor.rightDerivedFunctorCompIso' (lowerStar Λ g) (lowerStar Λ h)
            (lowerStarComp Λ g h)) ≪≫
        Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) (lowerStar Λ (g ≫ h))
          (lowerStarComp Λ f (g ≫ h)) := Iso.ext hc
  have he {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
      directImageComposition Λ a b =
        (Functor.rightDerivedFunctorCompIso' (lowerStar Λ a) (lowerStar Λ b)
          (lowerStarComp Λ a b)).symm := by
    apply Iso.ext
    rfl
  have ht : lowerStarCongr Λ (Category.assoc f g h) =
      eqToIso (congrArg (lowerStar Λ) (Category.assoc f g h)) := rfl
  unfold DirectImageCompositionAssociative
  rw [← ht]
  simp only [he]
  apply NatTrans.ext
  funext M
  apply (cancel_epi
    ((Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (Category.assoc f g h))).inv.app
      M)).1
  have hi := congrArg (fun e ↦ e.inv.app M) hci
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.assoc] at hi
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.comp_id]
  simpa only [Iso.inv_hom_id_app_assoc, Category.assoc] using hi

end AlgebraicGeometry.ProEtale.CondensedRing
