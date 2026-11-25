/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityProper
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseInduction
public import WeilConjectures.TraceFormula.Specialization.GenericBaseMeasureSlice

/-!

# Nearby duality: reduction to proper models

In Illusie's proof of Gabber's theorem (*Autour du théorème de monodromie locale*, Thm. 4.2;
blueprint `proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"), open locality
allows a compactification of the total space and an extension by zero of the coefficients, which
reduces the theorem to proper models. This file carries out this reduction for trait models over the
base (`NearbyCyclesModel.IsTraitModelOfBase`):

* every trait model over the base with affine total space is an open sub-model of a trait model
  over the base with proper total space
  (`NearbyCyclesModel.exists_isProper_openSubmodel_of_isAffine`);
* for a proper model, the duality map `δ_{M,K}` is an isomorphism
  (`NearbyCyclesModel.isIso_nearbyDualityMap_of_isProper`) as soon as its global sections are
  (`NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isProper`, blueprint
  `lemma-nearby-duality-proper-direct-image` (3)) and it is an isomorphism away from finitely many
  closed points of the special fibre
  (`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper`, generic
  slicing and induction on the dimension), by
  `NearbyCyclesModel.isIso_nearbyDualityMap_of_isIso_lowerStar`;
* hence Gabber's theorem for affine total spaces
  (`NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`) by passing to the larger model
  (`NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

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

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSepClosed k']
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- **Compactification of trait models over the base** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "open locality allows a projective
compactification"): a trait model `M` over the base with affine total space `𝒳` is an open sub-model
of a trait model `M̄` over the base with proper total space and proper `X̄`, `X̄'`, over open
immersions `j : X ⟶ X̄` and `j' : X' ⟶ X̄'`, in the sense of
`NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`.

This holds without the affineness assumption
(`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`): with `X̄` a Nagata
compactification of `X` over `k` and `Z = X̄ ×_k S`, the morphism `(e, q) : 𝒳 ⟶ Z` is an open
immersion over the generic point of `S` (fpqc descent), and a compactification of it which is an
isomorphism over `Z_η` (`AlgebraicGeometry.exists_isProper_isPullback_of_isOpenImmersion`) is the
required total space. -/
theorem exists_isProper_openSubmodel_of_isAffine (h : M.IsTraitModelOfBase k q g)
    [IsAffine M.total] :
    ∃ (Xc : Over (Spec (.of k))) (_ : LocallyOfFiniteType Xc.hom) (_ : QuasiCompact Xc.hom)
      (_ : IsSeparated Xc.hom) (_ : IsProper (toPoint Xc).left) (Xc' : Over (Spec (.of k')))
      (_ : LocallyOfFiniteType Xc'.hom) (_ : QuasiCompact Xc'.hom) (_ : IsSeparated Xc'.hom)
      (_ : IsProper (toPoint Xc').left) (Mc : NearbyCyclesModel Xc.left Xc'.left)
      (qc : Mc.total ⟶ trait k') (gc : Mc.generic ⟶ Spec (.of (traitGenericField k')))
      (_ : Mc.IsTraitModelOfBase k qc gc)
      (_ : IsPullback Mc.ε gc Xc.hom (traitGenericPoint k' ≫ traitToBase k k'))
      (_ : IsProper qc) (j : X ⟶ Xc)
      (_ : IsOpenImmersion j.left) (j' : X' ⟶ Xc') (_ : IsOpenImmersion j'.left)
      (φ : M.Hom Mc j.left j'.left) (_ : IsOpenImmersion φ.total),
      IsPullback φ.generic M.j Mc.j φ.total ∧ q = φ.total ≫ qc ∧ g = φ.generic ≫ gc :=
  h.exists_isProper_openSubmodel

/-- **Global sections of the duality map of a proper model** (blueprint
`lemma-nearby-duality-proper-direct-image` (3)): if `X`, `X'` and the total space of the trait model
`M` over the base are proper, then `RΓ(X', δ_{M,K})` is an isomorphism; proper exchange for the
structure morphism `a` (`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`, invertible
for proper `q`) and global Verdier duality identify it with the identity of
`RHom(RΓ(X ×_k Spec Ω, K), ℚ̄_ℓ)`.

This is `NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isIso` (the formal identity of
blueprint `lemma-nearby-duality-proper-direct-image` (1), with the lax monoidal structure of `Ra_*`,
its compatibility with `χ_a`, the proper axiom of `D` and global Verdier duality on both fibres),
with the invertibility of `χ_a`
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app`, which needs the geometric
generic fibre to be all of `X ×_k Spec Ω`) and of the duality map of the trait
(`NearbyCyclesModel.isIso_nearbyDualityMap_traitModel`). -/
theorem isIso_lowerStar_nearbyDualityMap_of_isProper (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleLowerStar ℓ
      (toPoint X')).map (nearbyDualityMap ℓ D h K)) := by
  have := isIso_nearbyDualityMap_traitModel ℓ (k := k) (k' := k')
    ((boundedConstructibleLowerStar ℓ (toPoint X)).obj K)
  exact isIso_lowerStar_nearbyDualityMap_of_isIso ℓ D h hgen K
    (fun A ↦ h.isIso_pushforwardExchange_app ℓ hgen A)

/-- **Finite support of the cone of the duality map of a proper model** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"): if `X`, `X'` and the
total space of the trait model `M` over the base are proper, then the duality map `δ_{M,K}` is an
isomorphism away from finitely many closed points of the special fibre.

This follows from Gabber's theorem for trait models over a generic base
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper_of_measure`, with
`S = ∅`). That theorem is proved by induction on the transcendence-degree measure
`AlgebraicGeometry.genericBaseMeasure`, which does not increase under dense compactification
(`genericBaseMeasure_le_of_isOpenImmersion`) and drops under generic slicing
(`IsTraitModelOfGenericBase.genericBaseMeasure_genericSliceBase_add_one_le`). The slice step is
`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase` (blueprint
`lemma-nearby-duality-slice--1`). -/
theorem exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper
    (D : NearbyDualizingData k k' ℓ) (h : M.IsTraitModelOfBase k q g)
    [IsProper (toPoint X).left] [IsProper (toPoint X').left] [IsProper q]
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMap ℓ D h K)) :=
  exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper_of_measure ℓ genericBaseMeasure
    (fun j _ hj ↦ genericBaseMeasure_le_of_isOpenImmersion j hj)
    (fun h _ hb ↦ h.genericBaseMeasure_genericSliceBase_add_one_le hb
      (transcendental_traitSliceCoord _))
    D h hgen K

/-- **Gabber's theorem for proper models** (Illusie, *Autour du théorème de monodromie locale*,
Thm. 4.2; blueprint `proposition-nearby-cycles-commute-verdier-duality`): if `X`, `X'` and the total
space of the trait model `M` over the base are proper, the duality map `δ_{M,K}` is an isomorphism
for every bounded constructible `K`. Its cone has no global sections
(`NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isProper`) and finite support
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper`), hence vanishes
(`NearbyCyclesModel.isIso_nearbyDualityMap_of_isIso_lowerStar`). -/
theorem isIso_nearbyDualityMap_of_isProper (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (nearbyDualityMap ℓ D h K) := by
  obtain ⟨S, hS, hU⟩ := exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper ℓ D h hgen K
  exact isIso_nearbyDualityMap_of_isIso_lowerStar ℓ D h K S hS hU
    (isIso_lowerStar_nearbyDualityMap_of_isProper ℓ D h hgen K)

/-- **Gabber's theorem for affine total spaces** (Illusie, *Autour du théorème de monodromie
locale*, Thm. 4.2; SGA 7 XIII; blueprint `proposition-nearby-cycles-commute-verdier-duality`). For a
trait model `M` over the base of a separated `k`-scheme `X` of finite type, over the strictly
henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed), whose total space is affine, the duality
map `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K`, adjoint to `θ_M ∘ Ψ(ev) ∘ μ_Ψ` with the dualizing map
`θ_M = β_a(ℚ̄_ℓ)` of blueprint `prose-E-15`, is an isomorphism for every bounded
constructible `K`. There is no Tate twist: the duality on the geometric generic fibre is relative
to `Ω`, the one on the special fibre relative to `k'`. The blueprint node is stated for finite
`ℓ`-primary coefficients and `D^b_ctf`; for bounded constructible `ℚ̄_ℓ`-complexes the canonical
map is the limit of the finite ones (Bhatt–Scholze, §6.8). The general case is reduced to this one
by open locality (`NearbyCyclesModel.isIso_nearbyDualityMap`).

The model is an open sub-model of a proper one
(`NearbyCyclesModel.exists_isProper_openSubmodel_of_isAffine`), for which the duality map is an
isomorphism at the extension by zero of `K`
(`NearbyCyclesModel.isIso_nearbyDualityMap_of_isProper`); restricting back gives the claim
(`NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`). -/
theorem isIso_nearbyDualityMap_of_isAffine (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsAffine M.total]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (nearbyDualityMap ℓ D h K) := by
  obtain ⟨Xc, _, _, _, _, Xc', _, _, _, _, Mc, qc, gc, hc, hcgen, _, j, _, j', _, φ, _, hφ, hq,
    hg⟩ :=
    exists_isProper_openSubmodel_of_isAffine h
  exact isIso_nearbyDualityMap_of_openSubmodel ℓ D h hc j j' φ hφ hq hg K
    (isIso_nearbyDualityMap_of_isProper ℓ D hc hcgen _)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
