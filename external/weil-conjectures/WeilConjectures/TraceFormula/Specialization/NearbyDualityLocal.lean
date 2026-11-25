/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityCompactification
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict

/-!

# Nearby duality is local on the total space

The restriction `M.restrictOpen V` of a trait model `M` over the base to an open `V` of its total
space (keeping the identification `ε`) is again a trait model over the base
(`NearbyCyclesModel.IsTraitModelOfBase.restrictOpen`), and the inclusion is a morphism of models
over `𝟙 X` and the open immersion `i⁻¹ V ⟶ X'` of special fibres. By the compatibility of the
duality map with open restriction
(`NearbyCyclesModel.isIso_map_nearbyDualityMap_iff_of_isOpenImmersion`) and since invertibility of
a morphism of complexes is local
(`ProEtale.CondensedRing.isIso_of_forall_exists_isIso_upperStar_map`),
Gabber's theorem for all trait models over the base follows from the case of affine total spaces
(`NearbyCyclesModel.isIso_nearbyDualityMap`, from
`NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`).

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

/-- **Nearby duality is local on the total space**: the duality map `δ_{M,K}` of a trait model over
the base is an isomorphism as soon as every point of the special fibre lies in an open `V` of the
total space with quasi-compact inclusion such that the duality maps of the restriction
`M.restrictOpen V` are isomorphisms. -/
theorem isIso_nearbyDualityMap_of_forall_exists_restrictOpen (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (H : ∀ x : X'.left, ∃ (V : M.total.Opens) (_ : QuasiCompact V.ι), M.i x ∈ V ∧
      ∀ K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        IsIso (nearbyDualityMap ℓ D (h.restrictOpen V) K')) :
    IsIso (nearbyDualityMap ℓ D h K) := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  suffices IsIso ((boundedConstructible _).ι.map (nearbyDualityMap ℓ D h K)) from
    isIso_of_fully_faithful (boundedConstructible _).ι _
  refine isIso_of_forall_exists_isIso_upperStar_map _ _ fun x ↦ ?_
  obtain ⟨V, _, hxV, hV⟩ := H x
  refine ⟨M.i ⁻¹ᵁ V, hxV, ?_⟩
  have : IsOpenImmersion (M.restrictOpenHom V).total := inferInstanceAs (IsOpenImmersion V.ι)
  have hiff := isIso_map_nearbyDualityMap_iff_of_isOpenImmersion (j := 𝟙 X) (D := D)
    (j' := M.restrictSpecialFibreι V) ℓ (M.restrictOpenHom V) h (h.restrictOpen V)
    (isPullback_morphismRestrict M.j V).flip rfl rfl K
  have := hiff.2 (hV _)
  exact (boundedConstructible _).ι.map_isIso
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (M.restrictSpecialFibreι V)).map (nearbyDualityMap ℓ D h K))

/-- **Gabber's theorem: nearby cycles commute with Verdier duality** (Illusie, *Autour du
théorème de monodromie locale*, Thm. 4.2; SGA 7 XIII; blueprint
`proposition-nearby-cycles-commute-verdier-duality`). For a trait model `M` over the base of a
separated `k`-scheme `X` of finite type, over the strictly henselian trait `S = Spec k'⟦t⟧`, the
duality map `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K`, adjoint to `θ_M ∘ Ψ(ev) ∘ μ_Ψ` with the dualizing map
`θ_M = β_a(ℚ̄_ℓ)`, is an isomorphism for every bounded constructible `K`. By open locality
(`NearbyCyclesModel.isIso_nearbyDualityMap_of_forall_exists_restrictOpen`) this is the case of
affine total spaces, `NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`. -/
theorem isIso_nearbyDualityMap (D : NearbyDualizingData k k' ℓ) (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (nearbyDualityMap ℓ D h K) := by
  refine isIso_nearbyDualityMap_of_forall_exists_restrictOpen ℓ D h K fun x ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := M.i x) (U := ⊤) trivial
  have : IsAffine V := hV
  have hM := h.isTraitModelOver.isTraitModel.isNoetherian_total
  refine ⟨V, inferInstance, hxV, fun K' ↦ ?_⟩
  have : IsAffine (M.restrictOpen V).total := hV
  exact isIso_nearbyDualityMap_of_isAffine ℓ D (h.restrictOpen V) K'

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
