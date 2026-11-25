/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBase

/-!

# Nearby duality over a generic base

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`), over the strictly henselian trait
`S = Spec k'⟦t⟧`, and `D` a family of dualizing maps over generic bases
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`). The **duality map**
(`NearbyCyclesModel.nearbyDualityMapOfGenericBase`)
```
δ_{M,K} : Ψ D_{X₁} K ⟶ D_{X'} Ψ K
```
is the adjoint of `θ_M ∘ Ψ(ev) ∘ μ_Ψ` (`CategoryTheory.Verdier.nearbyDualityMap`), as for trait
models over a base field (`NearbyCyclesModel.nearbyDualityMap`). This file adapts the formal
properties of the latter:
* the restriction of `M` to an open of its total space with quasi-compact inclusion is a trait
  model over the same generic base (`NearbyCyclesModel.IsTraitModelOfGenericBase.restrictOpen`);
* nearby duality and open restriction
  (`NearbyCyclesModel.isIso_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion`,
  `NearbyCyclesModel.isIso_map_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion`);
* nearby duality is local on the total space
  (`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_forall_exists_restrictOpen`);
* invariance under isomorphisms of the coefficients and passing to a larger model
  (`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_iso`,
  `NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_openSubmodel`).

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

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section Restrict

/-- The map `𝒳_{V,η} ⟶ 𝒳_η` of generic fibres induced by an open `V` of the total space of a
model over the trait. -/
noncomputable def restrictGenericFibreMap (V : M.total.Opens) :
    pullback (V.ι ≫ q) (traitGenericSpec k') ⟶ pullback q (traitGenericSpec k') :=
  pullback.lift (pullback.fst _ _ ≫ V.ι) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma restrictGenericFibreMap_fst (V : M.total.Opens) :
    restrictGenericFibreMap (q := q) V ≫ pullback.fst _ _ = pullback.fst _ _ ≫ V.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma restrictGenericFibreMap_snd (V : M.total.Opens) :
    restrictGenericFibreMap (q := q) V ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The generic fibre of the restriction to an open `V` is the preimage of `V`. -/
lemma isPullback_restrictGenericFibreMap (V : M.total.Opens) :
    IsPullback (restrictGenericFibreMap (q := q) V) (pullback.fst _ _) (pullback.fst _ _) V.ι := by
  refine IsPullback.of_right ?_ (restrictGenericFibreMap_fst V)
    (IsPullback.of_hasPullback q (traitGenericSpec k')).flip
  rw [restrictGenericFibreMap_snd]
  exact (IsPullback.of_hasPullback _ _).flip

instance (V : M.total.Opens) : IsOpenImmersion (restrictGenericFibreMap (q := q) V) :=
  MorphismProperty.of_isPullback (isPullback_restrictGenericFibreMap (q := q) V).flip
    (inferInstanceAs (IsOpenImmersion V.ι))

/-- The inclusion of the geometric generic fibre of the restriction to an open `V` into its
generic fibre is the restriction of that of `M`. -/
@[reassoc]
lemma genericFibreInclusion_restrictOpen_comp (hM : M.IsTraitModelOver q g) (V : M.total.Opens)
    [QuasiCompact V.ι] :
    genericFibreInclusion (M.restrictOpen V) (X' := M.restrictSpecialFibre V) (V.ι ≫ q)
        ((M.j ⁻¹ᵁ V).ι ≫ g) (hM.restrictOpen V).isPullback_j.w ≫ restrictGenericFibreMap V =
      (M.j ⁻¹ᵁ V).ι ≫ genericFibreInclusion M q g hM.isPullback_j.w := by
  apply pullback.hom_ext
  · simp only [Category.assoc, restrictGenericFibreMap_fst, genericFibreInclusion_fst_assoc,
      genericFibreInclusion_fst, restrictOpen_j]
    exact morphismRestrict_ι M.j V
  · simp [restrictGenericFibreMap_snd, genericFibreInclusion_snd]

/-- The restriction of a trait model over the generic base to an open `V` of its total space with
quasi-compact inclusion is a trait model over the same generic base. -/
lemma IsTraitModelOfGenericBase.restrictOpen (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (V : M.total.Opens) [QuasiCompact V.ι] :
    (M.restrictOpen V).IsTraitModelOfGenericBase (X' := M.restrictSpecialFibre V) X₁ ι (V.ι ≫ q)
      ((M.j ⁻¹ᵁ V).ι ≫ g) := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := h.exists_openImmersion_genericFibre
  refine ⟨h.isTraitModelOver.restrictOpen V, restrictGenericFibreMap V ≫ w, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hw₁, restrictGenericFibreMap_snd]
  · rw [restrictOpen_ε, ← hw₂, Category.assoc,
      genericFibreInclusion_restrictOpen_comp_assoc h.isTraitModelOver V]

end Restrict

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The **duality map** `δ_{M,K} : Ψ D_{X₁} K ⟶ D_{X'} Ψ K` of a trait model `M` over the generic
base (blueprint `proposition-nearby-cycles-commute-verdier-duality`): the adjoint of
`θ_M ∘ Ψ(ev) ∘ μ_Ψ`, with `θ_M` the dualizing map of the family `D`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`). This is the generic-base version of
`NearbyCyclesModel.nearbyDualityMap`. -/
noncomputable def nearbyDualityMapOfGenericBase (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
        (verdierDual ℓ K) ⟶
      verdierDual ℓ ((boundedConstructibleNearbyCycles
        (h.preservesBoundedConstructible (ℓ := ℓ))).obj K) :=
  Verdier.nearbyDualityMap
    (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ))) (D.θ h) K

section OpenRestriction

variable {Y₁ : Over (Spec (.of F))} [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom]
  [IsSeparated Y₁.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y₁.left Y'.left}
  {j : Y₁ ⟶ X₁} {j' : Y' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Nearby duality over a generic base and open restriction, after a further functor**: for an
open sub-model `φ : N ⟶ M` of trait models over the generic base and any functor `G` on the
special fibre of `N`, `G(j'^* δ_{M,K})` is invertible if and only if `G(δ_{N, j^* K})` is. -/
theorem isIso_map_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion {E : Type*}
    [Category E] (G : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ E)
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (φ : N.Hom M j.left j'.left) (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : qN = φ.total ≫ q)
    (hg : gN = φ.generic ≫ g) (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (G.map ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (nearbyDualityMapOfGenericBase ℓ D hM K))) ↔
      IsIso (G.map (nearbyDualityMapOfGenericBase ℓ D hN
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) := by
  have e := nearbyDualityMap_restrict_boundedConstructible φ
    (hN.preservesBoundedConstructible (ℓ := ℓ))
    (hM.preservesBoundedConstructible (ℓ := ℓ)) (D.θ hM)
    (D.θ hN) (dualizingComplexUpperStarIso ℓ j).hom
    (dualizingComplexUpperStarIso ℓ j').hom
    (D.map_θ_comp_dualizingComplexUpperStarIso hM hN j j' φ hφ hq hg)
    K
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ
      (hN.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ))) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  have := isIso_nearbyDualityMap_upperStar_of_isOpenImmersion j' (dualizingComplexUpperStarIso ℓ j')
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj K)
  have := isIso_nearbyDualityMap_upperStar_of_isOpenImmersion j (dualizingComplexUpperStarIso ℓ j) K
  rw [← isIso_comp_right_iff _ (G.map (Verdier.nearbyDualityMap (Functor.LaxMonoidal.μ
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j'))
    (dualizingComplexUpperStarIso ℓ j').hom
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj K))),
    ← G.map_comp]
  unfold nearbyDualityMapOfGenericBase
  rw [e]
  simp only [G.map_comp]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Nearby duality over a generic base and open restriction** (blueprint
`lemma-nearby-duality-proper-direct-image` (2)): for a morphism `φ : N ⟶ M` of trait models over the
generic base, over open immersions `j : Y₁ ⟶ X₁` and `j' : Y' ⟶ X'`, whose map of total spaces is an
open immersion compatible with the structure morphisms and whose square of geometric generic fibres
is cartesian, `j'^* δ_{M,K}` is an isomorphism if and only if `δ_{N, j^* K}` is. -/
theorem isIso_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (φ : N.Hom M j.left j'.left)
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : qN = φ.total ≫ q)
    (hg : gN = φ.generic ≫ g) (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (nearbyDualityMapOfGenericBase ℓ D hM K)) ↔
      IsIso (nearbyDualityMapOfGenericBase ℓ D hN
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) :=
  isIso_map_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion ℓ (𝟭 _) D φ hM hN hφ hq hg K

end OpenRestriction

/-- **Nearby duality over a generic base is local on the total space**: the duality map
`δ_{M,K}` of a trait model over the generic base is an isomorphism as soon as every point of the
special fibre lies in an open `V` of the total space with quasi-compact inclusion such that the
duality maps of the restriction `M.restrictOpen V` are isomorphisms. -/
theorem isIso_nearbyDualityMapOfGenericBase_of_forall_exists_restrictOpen
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (H : ∀ x : X'.left, ∃ (V : M.total.Opens) (_ : QuasiCompact V.ι), M.i x ∈ V ∧
      ∀ K' : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        IsIso (nearbyDualityMapOfGenericBase ℓ D (h.restrictOpen V) K')) :
    IsIso (nearbyDualityMapOfGenericBase ℓ D h K) := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  suffices IsIso ((boundedConstructible _).ι.map (nearbyDualityMapOfGenericBase ℓ D h K)) from
    isIso_of_fully_faithful (boundedConstructible _).ι _
  refine isIso_of_forall_exists_isIso_upperStar_map _ _ fun x ↦ ?_
  obtain ⟨V, _, hxV, hV⟩ := H x
  refine ⟨M.i ⁻¹ᵁ V, hxV, ?_⟩
  have : IsOpenImmersion (M.restrictOpenHom V).total := inferInstanceAs (IsOpenImmersion V.ι)
  have hiff := isIso_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion (j := 𝟙 X₁) (D := D)
    (j' := M.restrictSpecialFibreι V) ℓ (M.restrictOpenHom V) h (h.restrictOpen V)
    (isPullback_morphismRestrict M.j V).flip rfl rfl K
  have := hiff.2 (hV _)
  exact (boundedConstructible _).ι.map_isIso
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (M.restrictSpecialFibreι V)).map (nearbyDualityMapOfGenericBase ℓ D h K))

/-- **The duality map over a generic base is invariant under isomorphisms of the coefficients**:
if `K ≅ K'` and `δ_{M,K'}` is an isomorphism, then so is `δ_{M,K}` (naturality of `δ`,
`CategoryTheory.Verdier.map_pre_comp_nearbyDualityMap`). -/
lemma isIso_nearbyDualityMapOfGenericBase_of_iso (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {K K' : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : K ≅ K') [IsIso (nearbyDualityMapOfGenericBase ℓ D h K')] :
    IsIso (nearbyDualityMapOfGenericBase ℓ D h K) := by
  have hsq := Verdier.map_pre_comp_nearbyDualityMap
    (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ))) (D.θ h)
    (fun x y ↦ boundedConstructibleTensorMap_natural (h.preservesBoundedConstructible (ℓ := ℓ)) x y)
    e.hom
  have := isIso_pre_app e.hom (dualizingComplex ℓ X₁)
  have := isIso_pre_app ((boundedConstructibleNearbyCycles
    (h.preservesBoundedConstructible (ℓ := ℓ))).map e.hom) (dualizingComplex ℓ X')
  have : IsIso ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).map
      ((pre e.hom).app (dualizingComplex ℓ X₁)) ≫ nearbyDualityMapOfGenericBase ℓ D h K) := by
    have : IsIso (Verdier.nearbyDualityMap
        (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ))) (D.θ h) K') :=
      ‹IsIso (nearbyDualityMapOfGenericBase ℓ D h K')›
    unfold nearbyDualityMapOfGenericBase
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left ((boundedConstructibleNearbyCycles
    (h.preservesBoundedConstructible (ℓ := ℓ))).map ((pre e.hom).app (dualizingComplex ℓ X₁)))
      (nearbyDualityMapOfGenericBase ℓ D h K)

variable {Xc : Over (Spec (.of F))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom]
  [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom] {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Passing to a larger model over the generic base** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "open locality allows a compactification and
extension by zero"): let `φ : M ⟶ M̄` be a morphism of trait models over the generic base, over open
immersions `j : X₁ ⟶ X̄₁` and `j' : X' ⟶ X̄'`, whose map of total spaces is an open immersion
compatible with the structure morphisms and whose square of geometric generic fibres is cartesian.
If the duality map of `M̄` is an isomorphism at the extension by zero `j_! K`, then the duality map
of `M` is an isomorphism at `K`. -/
theorem isIso_nearbyDualityMapOfGenericBase_of_openSubmodel
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hc : Mc.IsTraitModelOfGenericBase Xc ι qc gc) (j : X₁ ⟶ Xc)
    [IsOpenImmersion j.left] (j' : X' ⟶ Xc') [IsOpenImmersion j'.left]
    (φ : M.Hom Mc j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic M.j Mc.j φ.total) (hq : q = φ.total ≫ qc)
    (hg : g = φ.generic ≫ gc) (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsIso (nearbyDualityMapOfGenericBase ℓ D hc
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        K))) :
    IsIso (nearbyDualityMapOfGenericBase ℓ D h K) := by
  have := (isIso_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion ℓ D φ hc h hφ hq hg
    ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      K)).1 inferInstance
  let e : K ≅ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        K) :=
    asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app K)
  exact isIso_nearbyDualityMapOfGenericBase_of_iso ℓ D h e

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
