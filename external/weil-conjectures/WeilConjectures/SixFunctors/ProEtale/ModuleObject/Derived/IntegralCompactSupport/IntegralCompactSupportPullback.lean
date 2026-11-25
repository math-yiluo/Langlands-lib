/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs

import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-! # Preservation on the ordinary integral localizing category -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]
/-- Source: blueprint proposition-construction-independence-rf-shriek steps 2, 3 and 6.
(blueprint: lem-sfb-total-derived-pullback).

Proof: Standing schemes are qcqs. Specialize localizingClosure_ctf_equals_bc to O_E
with the identity coefficient-ring isomorphism. Write ht for Dctf = Dbc and he for
the resulting equality of their localizing closures. Inverse image pulls a finite
constructible stratification back to one on the source; the finite constant scalar
models pull back on each stratum. The exact-derived homology comparison then preserves
bounded constructibility. Flatness is preserved by inverse image, so a bounded flat
representative of a finite-Tor complex remains a bounded flat representative after
pullback. This gives the constructible clause of UnboundedLocalizingPullback, by the
argument of pullback_constructible and pullback_of_constructible in its source module.
Transport that clause along ht. The total derived pullback is exact and is a left
adjoint, hence preserves ordinary coproducts. The inverse image of the target localizing
closure is therefore localizing and contains all source generators; minimality gives
preservation of the localizing closure. Transport this along he. The argument uses no
characteristic restriction on k and includes zero objects and empty schemes. -/
theorem pullback_of_ctf_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Spaces k} (v : X ⟶ Y) :
    (∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) Y.obj.left K →
      generators (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left ((pull
        (Profinite.padicIntegersRingObj ℓ E.val) v.hom.left).obj K)) ∧
    (∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) Y.obj.left K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left ((pull
        (Profinite.padicIntegersRingObj ℓ E.val) v.hom.left).obj K)) := by
  let R := Profinite.padicIntegersRingObj ℓ E.val
  let : IsSeparated X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2.2
  let : IsSeparated Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2.2
  let : CompactSpace X.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  let : CompactSpace Y.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  let : QuasiSeparatedSpace X.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated X.obj.hom
  let : QuasiSeparatedSpace Y.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  have hc := pullback_constructible R v.hom.left
  obtain ⟨H⟩ := pullback_of_constructible R v.hom.left hc
  have he (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] :
      localizingClosureProEtale R Z = localizing R Z :=
    (localizingClosure_ctf_equals_bc ℓ Z R
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.2.1
  constructor
  · intro K hK
    exact pullback_bounded_constructible R v.hom.left hc K hK
  · intro K hK
    have hK' : localizingClosureProEtale R Y.obj.left K :=
      (congrFun (he Y.obj.left).symm K).mp hK
    exact (congrFun (he X.obj.left) _).mp (H.localizing ⟨K, hK'⟩)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
