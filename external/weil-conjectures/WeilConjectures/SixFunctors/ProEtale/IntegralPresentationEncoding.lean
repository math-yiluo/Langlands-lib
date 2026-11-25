/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion

/-! # Data for relabelling an integral coefficient presentation

Stacks Project, Tag 06YY, isomorphism-of-coefficients specialization
(auxiliary; not a blueprint node).

This packages specified data, without choosing an isomorphism or an equivalence.
The forward functor is fixed to section-action followed by restriction along the
inverse ring isomorphism. The comparison theorem normalizes the ring isomorphism
against every finite quotient. No existence assertion is part of this definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Specified coefficient relabelling and its concrete section-action equivalence.
Source: Stacks 06YY; blueprint integral-criterion-reductions, final sentence
(auxiliary; not a blueprint node). -/
structure Encoding where
  /-- The isomorphism from reconstructed section rings to completed coefficients. -/
  ringIso : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (AdicCompletion.ring l E X) ≅
    WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  /-- The module equivalence retaining the underlying abelian sheaves. -/
  modules : AdicCompletion.Modules l E X ≌ WeilConjectures.scalarReductionSource.{u, u} l E X
  /-- Its forward functor is the prescribed scalar relabelling. -/
  functor_eq : modules.functor =
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)).functor ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ringIso.inv)
  /-- Forward section-action preserves addition. -/
  [additive : modules.functor.Additive]
  /-- Its inverse preserves addition. -/
  [inverseAdditive : modules.inverse.Additive]

attribute [instance] Encoding.additive Encoding.inverseAdditive

end AlgebraicGeometry.ProEtale.IntegralPresentation
