/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCycles
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityLocal
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingExistence
import WeilConjectures.TraceFormula.Specialization.NearbyDualityLocal

/-!

# Nearby cycles commute with Verdier duality

For a trait model `M` over the base, the duality map `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K` built from
the dualizing maps `θ` is an isomorphism (`NearbyCyclesModel.isIso_nearbyDualityMap`). Since the
dualizing maps exist (`NearbyCyclesModel.nonempty_nearbyDualizingData`), nearby cycles commute
with Verdier duality (`NearbyCyclesModel.nonempty_nearbyCycles_verdierDual_iso`, blueprint
`proposition-nearby-cycles-commute-verdier-duality`), in particular for the specialization to the
normal cone of a rational point (`ProEtale.CondensedRing.nonempty_specialization_verdierDual_iso`),
and the specialization of the universal kernel `K ⊠ D K` is the universal kernel of the
specialization (`ProEtale.CondensedRing.nonempty_specializationProd_externalProduct_iso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **Nearby cycles commute with Verdier duality**: for a trait model `M` over the base,
`Ψ(D_X K) ≅ D_{X'}(Ψ K)` for every bounded constructible `K`, the duality being relative to `k` on
`X` and to `k'` on the special fibre. -/
theorem nonempty_nearbyCycles_verdierDual_iso (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
        (verdierDual ℓ K) ≅
      verdierDual ℓ ((boundedConstructibleNearbyCycles
        (h.preservesBoundedConstructible ℓ)).obj K)) :=
  let ⟨D⟩ := nonempty_nearbyDualizingData ℓ k k'
  have := isIso_nearbyDualityMap ℓ D h K
  ⟨asIso (nearbyDualityMap ℓ D h K)⟩

end NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable (k') (x : RationalPoint X)

/-- **Nearby cycles commute with Verdier duality** (Gabber; Illusie, *Autour du théorème de
monodromie locale*, Thm. 4.2; blueprint `proposition-nearby-cycles-commute-verdier-duality`), for
the specialization to the normal cone: `Sp_{X,x}(D_X K) ≅ D(Sp_{X,x} K)`. Here
`Sp_{X,x} = Li^* Rj_* Lε^*` with `ε : X_Ω ⟶ X` the base change to the geometric
generic point; the duality on the geometric generic fibre `X_Ω` is relative to `Ω`, and
`Lε^* D_X ≅ D_{X_Ω} Lε^*` on bounded constructible complexes since `ε` is a base change of
fields. This only asserts that some isomorphism exists, which is weaker than the node: the node
asserts that the canonical map `δ_{X,M}`, the adjoint of `θ_X ∘ S_X ev ∘ μ_X`, is an
isomorphism. It is the instance of `NearbyCyclesModel.nonempty_nearbyCycles_verdierDual_iso` for
the deformation model, whose geometric generic fibre is the base change of `X`
(`ProEtale.CondensedRing.isPullback_deformationModel_ε`). -/
theorem nonempty_specialization_verdierDual_iso
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((specialization k' x).obj (verdierDual ℓ K) ≅
      verdierDual ℓ ((specialization k' x).obj K)) :=
  NearbyCyclesModel.nonempty_nearbyCycles_verdierDual_iso ℓ
    (q := deformationTotalToTrait X x.left.ker k') (g := deformationGenericToPoint X x.left.ker k')
    (.of_isPullback ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      isPullback_deformationSpecialFibre X _ k'⟩ ⟨deformationTotalToBase X _ k', rfl,
        deformationTotalToBase_hom X _ k'⟩
      (isPullback_deformationModel_ε k' x.left.ker)) K

/-- **Nearby cycles of the universal kernel**: the specialization of the universal kernel
`K ⊠ D K` is the universal kernel of the specialization,
`Ψ_{X×X}(K ⊠ D_X K) ≅ Ψ_X K ⊠ Ψ_X D_X K ≅ Ψ_X K ⊠ D Ψ_X K`, by Gabber's Künneth formula
(`ProEtale.CondensedRing.isIso_specializationKunnethMap`, blueprint
`proposition-external-kunneth-formula-nearby-cycles`) and the commutation of nearby cycles with
Verdier duality (`ProEtale.CondensedRing.nonempty_specialization_verdierDual_iso`, blueprint
`proposition-nearby-cycles-commute-verdier-duality`). -/
theorem nonempty_specializationProd_externalProduct_iso
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((specializationProd k' x).obj (externalProduct ℓ K (verdierDual ℓ K)) ≅
      externalProduct ℓ ((specialization k' x).obj K)
        (verdierDual ℓ ((specialization k' x).obj K))) :=
  have e := nonempty_specialization_verdierDual_iso (ℓ := ℓ) k' x K
  ⟨(asIso (specializationKunnethMap (ℓ := ℓ) k' x K _)).symm ≪≫
    whiskerLeftIso _ ((boundedConstructibleUpperStar _ ℓ _).mapIso e.some)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
