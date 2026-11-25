/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement

set_option linter.privateModule false

/-! # Composition of the normalized coefficient identifications

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md, (1)--(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Transpose the direct-image composition through the three ring-sheaf adjunctions.
private theorem ring_coefficient_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (T : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj R ≅ T)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj S ≅ T)
    (hc : proEtaleRingDirectImageMap (f ≫ g) R T c =
      proEtaleRingDirectImageMap g R S cg ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (proEtaleRingDirectImageMap f S T cf) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eFG := (MorphismProperty.Over.pullbackComp
            (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
            (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).hom.app T) :
    c = proEtaleRingCompositeCoefficients f g R S T cg cf := by
  apply Iso.ext
  have h := adjunct_comp_comparison
    (proEtaleSheafAdjunction g CommRingCat.{u + 1})
    (proEtaleSheafAdjunction f CommRingCat.{u + 1})
    (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1})
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
        (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X))
    (proEtaleRingDirectImageMap g R S cg) (proEtaleRingDirectImageMap f S T cf)
  rw [← hc] at h
  simpa only [proEtaleRingCompositeCoefficients, proEtaleRingInverseImageComp,
    proEtaleRingDirectImageMap, ← Adjunction.homEquiv_unit,
    Equiv.symm_apply_apply, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv] using h

private abbrev reconstructedRing {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :=
  sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R

-- Keep reconstructed rings abstract while checking the section formula.
private theorem reconstructed_coefficient_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RX : Sheaf (ProEt.topology X) Ab.{u + 1})
    (RY : Sheaf (ProEt.topology Y) Ab.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) Ab.{u + 1})
    [MonObj RX] [IsCommMonObj RX] [MonObj RY] [IsCommMonObj RY]
    [MonObj RZ] [IsCommMonObj RZ]
    (af : RY ⟶ (ProEtale.lowerStar Ab.{u + 1} f).obj RX)
    (ag : RZ ⟶ (ProEtale.lowerStar Ab.{u + 1} g).obj RY)
    (afComp : RZ ⟶ (ProEtale.lowerStar Ab.{u + 1} (f ≫ g)).obj RX)
    (ha : afComp = ag ≫ (ProEtale.lowerStar Ab.{u + 1} g).map af ≫
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app RX)
    (cfComp : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj
      (reconstructedRing RZ) ≅ reconstructedRing RX)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (reconstructedRing RZ) ≅ reconstructedRing RY)
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (reconstructedRing RY) ≅ reconstructedRing RX)
    (hcComp : ∀ V r, ((proEtaleRingDirectImageMap (f ≫ g)
      (reconstructedRing RZ)
      (reconstructedRing RX) cfComp).hom.app V).hom r =
        (afComp.hom.app V).hom r)
    (hcf : ∀ V r, ((proEtaleRingDirectImageMap f
      (reconstructedRing RY)
      (reconstructedRing RX) cf).hom.app V).hom r =
        (af.hom.app V).hom r)
    (hcg : ∀ V r, ((proEtaleRingDirectImageMap g
      (reconstructedRing RZ)
      (reconstructedRing RY) cg).hom.app V).hom r =
        (ag.hom.app V).hom r) :
    cfComp = proEtaleRingCompositeCoefficients f g
      (reconstructedRing RZ) (reconstructedRing RY)
      (reconstructedRing RX) cg cf := by
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
      (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  let p := proEtaleRingDirectImageMap f (reconstructedRing RY)
    (reconstructedRing RX) (cf)
  let q := proEtaleRingDirectImageMap g (reconstructedRing RZ)
    (reconstructedRing RY) (cg)
  let r := proEtaleRingDirectImageMap (f ≫ g) (reconstructedRing RZ)
    (reconstructedRing RX) (cfComp)
  have hr : r = q ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map p ≫
      e.hom.app (reconstructedRing RX) := by
    ext V x
    change ((proEtaleRingDirectImageMap (f ≫ g) (reconstructedRing RZ)
        (reconstructedRing RX) (cfComp)).hom.app V).hom x =
      ((reconstructedRing RX).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
          V.unop).op).hom
        (((proEtaleRingDirectImageMap f (reconstructedRing RY)
          (reconstructedRing RX) (cf)).hom.app
          (Opposite.op ((proEtaleBaseChange g).obj V.unop))).hom
          (((proEtaleRingDirectImageMap g (reconstructedRing RZ)
            (reconstructedRing RY) (cg)).hom.app V).hom x))
    rw [hcComp, hcf, hcg]
    exact (InternalModuleOperations.coefficient_comp_apply f g
      RX RY RZ
      af ag afComp ha
      V x).symm
  exact ring_coefficient_comp f g (reconstructedRing RZ)
    (reconstructedRing RY) (reconstructedRing RX)
    (cfComp) (cg) (cf) hr

private theorem coefficient_comp (G : ScalarSixGeometry.{u}) (Λ : ScalarSixRing.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G.coefficient Λ (f ≫ g) = proEtaleRingCompositeCoefficients f g
      (scalarSixSectionRing Λ Z) (scalarSixSectionRing Λ Y) (scalarSixSectionRing Λ X)
      (G.coefficient Λ g) (G.coefficient Λ f) := by
  exact reconstructed_coefficient_comp f g
    (condensedRingObj Λ.X X) (condensedRingObj Λ.X Y) (condensedRingObj Λ.X Z)
    (condensedPushforwardHom Λ.X f) (condensedPushforwardHom Λ.X g)
    (condensedPushforwardHom Λ.X (f ≫ g)) (condensedPushforwardHom_comp Λ.X f g)
    (G.coefficient Λ (f ≫ g)) (G.coefficient Λ g) (G.coefficient Λ f)
    (G.coefficientNormalization Λ (f ≫ g)) (G.coefficientNormalization Λ f)
    (G.coefficientNormalization Λ g)

end AlgebraicGeometry.ProEtale.CondensedRing
