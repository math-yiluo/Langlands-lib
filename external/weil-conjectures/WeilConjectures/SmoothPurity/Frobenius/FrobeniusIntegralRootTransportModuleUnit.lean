/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage

/-! # Invertibility of the module adjunction unit for an isomorphic scheme map
-/

@[expose] public section
set_option autoImplicit false
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

/-- The module adjunction unit is invertible along an isomorphism of schemes.
Source: Stacks Project, Modules on Sites, Tags 09A5 and 03EL.
Proof: inverse image of sheaves on the pro-etale site is an equivalence for an
isomorphism of schemes; transport this equivalence through scalar extension and
reflect its unit along the underlying sheaf functor.
(blueprint: new-weil-frobenius-integral-root-transport-module-unit). -/
theorem frobeniusIntegralRootTransport_moduleUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso ((SheafOfModules.toSheaf _).map
      ((proEtaleRingModuleAdjunction g (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X) ((PurCompactSupport.completed l E).pull
          g)).unit.app (purTwistIntegralModule Y l E))) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let S := completedIntegralCommRingSheafUnrestricted l E X
  let c := (PurCompactSupport.completed l E).pull g
  let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
    g CommRingCat.{u + 1}).1
  have : IsIso (proEtaleRingDirectImageMap g R S c) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let ρ := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap g R S c)
  let e := isoModulePushforwardEquivalence g
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ρ
  let : (proEtaleRingModuleDirectImage g R S c).IsEquivalence := e.isEquivalence_functor
  exact Functor.map_isIso (SheafOfModules.toSheaf _) _

end WeilConjectures
