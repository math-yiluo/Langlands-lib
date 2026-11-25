/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen

/-!

# Nearby duality: passing to a larger model

The duality map `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K` of a trait model over the base
(`NearbyCyclesModel.nearbyDualityMap`) is natural in `K`
(`CategoryTheory.Verdier.map_pre_comp_nearbyDualityMap`), so its invertibility only depends on
the isomorphism class of `K` (`NearbyCyclesModel.isIso_nearbyDualityMap_of_iso`).

If `M` is an open sub-model of a trait model `M̄` over the base, over open immersions
`j : X ⟶ X̄` and `j' : X' ⟶ X̄'` (an open immersion of total spaces compatible with the structure
morphisms, with cartesian square of geometric generic fibres), then Gabber's theorem for `M̄`
implies it for `M` (`NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`): the restriction
of `δ_{M̄, j_! K}` to `X'` is identified with `δ_{M, j^* j_! K}`
(`NearbyCyclesModel.isIso_map_nearbyDualityMap_iff_of_isOpenImmersion`) and `j^* j_! K ≅ K`.
This is the step "open locality allows a compactification and extension by zero" of the proof of
blueprint `proposition-nearby-cycles-commute-verdier-duality`, for compactifications by trait models
over the base.

A compactification of an affine total space over the trait
(`NearbyCyclesModel.exists_isProper_openImmersion_of_isAffine`) is in general not a trait model
over the base: its geometric generic fibre need not be open in `X̄ ×_k Spec Ω` for a proper
`k`-scheme `X̄` through which the identification factors. Producing such a compactification needs
gluing `𝒳` with `X̄ ×_k η` along `𝒳_η` and a relative Nagata compactification over `X̄ ×_k S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The image `(pre f).app W` of an isomorphism `f` is an isomorphism. -/
lemma isIso_pre_app {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] {A B : C}
    (f : A ⟶ B) [IsIso f] (W : C) : IsIso ((pre f).app W) :=
  ⟨(pre (inv f)).app W, by rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id, pre_id,
    NatTrans.id_app], by rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id,
    NatTrans.id_app]⟩

/-- **The duality map is invariant under isomorphisms of the coefficients**: if `K ≅ K'` and
`δ_{M,K'}` is an isomorphism, then so is `δ_{M,K}` (naturality of `δ`,
`CategoryTheory.Verdier.map_pre_comp_nearbyDualityMap`). -/
lemma isIso_nearbyDualityMap_of_iso (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : K ≅ K') [IsIso (nearbyDualityMap ℓ D h K')] : IsIso (nearbyDualityMap ℓ D h K) := by
  have hsq := Verdier.map_pre_comp_nearbyDualityMap
    (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ)) (D.θ h)
    (fun x y ↦ boundedConstructibleTensorMap_natural (h.preservesBoundedConstructible ℓ) x y)
    e.hom
  have := isIso_pre_app e.hom (dualizingComplex ℓ X)
  have := isIso_pre_app ((boundedConstructibleNearbyCycles
    (h.preservesBoundedConstructible ℓ)).map e.hom) (dualizingComplex ℓ X')
  have : IsIso ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).map
      ((pre e.hom).app (dualizingComplex ℓ X)) ≫ nearbyDualityMap ℓ D h K) := by
    have : IsIso (Verdier.nearbyDualityMap
        (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ)) (D.θ h) K') :=
      ‹IsIso (nearbyDualityMap ℓ D h K')›
    rw [show nearbyDualityMap ℓ D h K = Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ)) (D.θ h) K from rfl, hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left ((boundedConstructibleNearbyCycles
    (h.preservesBoundedConstructible ℓ)).map ((pre e.hom).app (dualizingComplex ℓ X)))
      (nearbyDualityMap ℓ D h K)

variable {Xc : Over (Spec (.of k))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom]
  [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom] {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Passing to a larger model** (blueprint `proposition-nearby-cycles-commute-verdier-duality`,
"open locality allows a compactification and extension by zero"): let `φ : M ⟶ M̄` be a morphism of
trait models over the base, over open immersions `j : X ⟶ X̄` and `j' : X' ⟶ X̄'`, whose map of
total spaces is an open immersion compatible with the structure morphisms and whose square of
geometric generic fibres is cartesian. If the duality map of `M̄` is an isomorphism at the
extension by zero `j_! K`, then the duality map of `M` is an isomorphism at `K`: the restriction
of `δ_{M̄, j_! K}` along `j'` is identified with `δ_{M, j^* j_! K}`
(`NearbyCyclesModel.isIso_map_nearbyDualityMap_iff_of_isOpenImmersion`), and `K ≅ j^* j_! K`. -/
theorem isIso_nearbyDualityMap_of_openSubmodel (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) (hc : Mc.IsTraitModelOfBase k qc gc) (j : X ⟶ Xc)
    [IsOpenImmersion j.left] (j' : X' ⟶ Xc') [IsOpenImmersion j'.left]
    (φ : M.Hom Mc j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic M.j Mc.j φ.total) (hq : q = φ.total ≫ qc)
    (hg : g = φ.generic ≫ gc) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsIso (nearbyDualityMap ℓ D hc
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        K))) :
    IsIso (nearbyDualityMap ℓ D h K) := by
  have := (isIso_map_nearbyDualityMap_iff_of_isOpenImmersion ℓ φ D hc h hφ hq hg
    ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      K)).1 inferInstance
  let e : K ≅ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        K) :=
    asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app K)
  exact isIso_nearbyDualityMap_of_iso ℓ D h e

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
