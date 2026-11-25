/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralRootTransportModuleLift
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralRootTransportModuleUnit

/-! # Module adjunction glue for integral root transport

This file isolates the categorical step that turns an additive semilinear map into a
module isomorphism. The root-limit comparison and its tensor formula are handled by
the parent transport theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage completedIntegralCoefficientSheafUnrestricted
  MorphismProperty.Over.pullback constantSheaf Padic
attribute [local instance_reducible] PurCompactSupport.completed
attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted

/--
The module adjunction transports an additive semilinear isomorphism. This is the
categorical middle of the integral root transport argument; it does not mention the
root comparison or any tensor formula.
Source: Stacks Project, Modules on Sites, Tag 03EL, and the module adjunction
constructed in `ProEtaleOperationsCanonicalAdjunction`.
Proof: regard the additive map as a map into the direct image by its completed
coefficient semilinearity. Transpose it under the canonical module adjunction. The
underlying additive map is invertible, so reflection of isomorphisms along the
forgetful sheaf functor makes the transpose invertible. The adjunction unit identity
then gives the displayed sectionwise formula.
(blueprint: new-weil-frobenius-integral-root-transport-module-glue). -/
theorem frobeniusIntegralRootTransport_moduleGlue
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)))
    (hφ : IsIso φ)
    (hscalar : ∀ (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
      (t : (purTwistIntegralModule Y l E).val.obj (op V)),
      φ.hom.app (op V)
          (@SMul.smul _ _ (purTwistIntegralAction Y l E (op V)).toSMul a t) =
        @SMul.smul _ _
          (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a)
          (φ.hom.app (op V) t)) :
    ∃ e : (proEtaleRingModulePullback g (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l E).pull
          g)).obj (purTwistIntegralModule Y l E) ≅ (purTwistIntegralModule X l E),
      ∀ (V : Y.ProEt)
        (t : (purTwistIntegralModule Y l E).val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g (completedIntegralCommRingSheafUnrestricted l E Y)
            (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l
              E).pull g)).unit.app (purTwistIntegralModule Y l E)).val.app (op V) t) =
        φ.hom.app (op V) t := by
  obtain ⟨f, hf⟩ := frobeniusIntegralRootTransport_moduleLift l E g φ hscalar
  let adj := proEtaleRingModuleAdjunction g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    ((PurCompactSupport.completed l E).pull g)
  have hunit : IsIso ((SheafOfModules.toSheaf _).map (adj.unit.app
      (purTwistIntegralModule Y l E))) :=
    frobeniusIntegralRootTransport_moduleUnit_isIso l E g
  have hcomp : (SheafOfModules.toSheaf _).map (adj.unit.app
      (purTwistIntegralModule Y l E)) ≫
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map
        ((SheafOfModules.toSheaf _).map f) = φ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext t
    exact hf V.unop t
  have hmap : IsIso ((SheafOfModules.toSheaf _).map f) := by
    have h := proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
      g AddCommGrpCat.{u + 1}
    letI : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).IsEquivalence := h.1
    letI : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).IsEquivalence :=
      (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).isEquivalence_right_of_isEquivalence_left
    have hc : IsIso ((SheafOfModules.toSheaf _).map (adj.unit.app
        (purTwistIntegralModule Y l E)) ≫
        (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map
          ((SheafOfModules.toSheaf _).map f)) := by
      rw [hcomp]
      exact hφ
    have hd : IsIso ((proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map
        ((SheafOfModules.toSheaf _).map f)) :=
      IsIso.of_isIso_comp_left
        ((SheafOfModules.toSheaf _).map (adj.unit.app
          (purTwistIntegralModule Y l E)))
        ((proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map
          ((SheafOfModules.toSheaf _).map f))
    exact isIso_of_reflects_iso ((SheafOfModules.toSheaf _).map f)
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1})
  have hfiso : IsIso f := by
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf _)
  let e : (proEtaleRingModulePullback g (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l E).pull
        g)).obj (purTwistIntegralModule Y l E) ≅
      (purTwistIntegralModule X l E) := asIso f
  refine ⟨e, ?_⟩
  intro V t
  exact hf V t

end WeilConjectures
