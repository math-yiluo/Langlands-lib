/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Statement
public import WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension

/-!
# Auxiliary reductions for the induction step of Deligne's generic constructibility

* Passing to the reduction: for a surjective closed immersion `r : X' ⟶ X` (for instance
  `X_red ⟶ X`), the generic constructibility property of `Rj_* K` follows from that of
  `R(r ≫ j)_* r^* K`
  (`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_surjective_closedImmersion`),
  since `K ≅ Rr_* r^* K`, `r^*` being an equivalence.
* An immersion from a scheme into a reduced scheme with open image is an open immersion
  (`AlgebraicGeometry.IsImmersion.isOpenImmersion_of_isOpen_range`).
* Dimension estimates for generic fibres: under embeddings
  (`AlgebraicGeometry.Etale.genericFiberDim_le_of_isEmbedding`) and for a closed subset all of
  whose points in the generic fibre generalize to points of the generic fibre outside it
  (`AlgebraicGeometry.Etale.genericFiberDim_add_one_le_of_generalizes`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- An immersion into a reduced scheme whose image is open is an open immersion: it is a
surjective closed immersion onto that open, which is reduced, hence an isomorphism onto it. -/
lemma IsImmersion.isOpenImmersion_of_isOpen_range {V X : Scheme.{u}} [IsReduced X] (v : V ⟶ X)
    [IsImmersion v] (hv : IsOpen (Set.range v)) : IsOpenImmersion v := by
  let O : X.Opens := ⟨_, hv⟩
  let v' : V ⟶ O := IsOpenImmersion.lift O.ι v (by rw [Opens.range_ι]; rfl)
  have hv' : v' ≫ O.ι = v := IsOpenImmersion.lift_fac _ _ _
  have : IsImmersion v' := by
    have : IsImmersion (v' ≫ O.ι) := by rw [hv']; infer_instance
    exact .of_comp v' O.ι
  have : Surjective v' := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y, O.ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hv', hy]; rfl)⟩⟩
  have := IsClosedImmersion.of_isImmersion_of_surjective v'
  have : IsReduced O := isReduced_of_isOpenImmersion O.ι
  have := isIso_of_isClosedImmersion_of_surjective v'
  rw [← hv']
  infer_instance

/-- A surjective morphism of irreducible schemes maps the generic point to the generic point. -/
lemma Scheme.Hom.apply_genericPoint_of_surjective {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [Surjective f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ_of_surjective f.surjective, closure_univ] at h
  exact h.eq (genericPoint_spec Y)

/-- If every point of `F` has a generalization in `G` outside `F`, and `F` is quasi-sober, then
`dim F + 1 ≤ dim G`. -/
theorem topologicalKrullDim_add_one_le_of_generalizes {X : Type*} [TopologicalSpace X]
    [T0Space X] {F G : Set X} [QuasiSober F] (hFG : F ⊆ G)
    (h : ∀ x ∈ F, ∃ y ∈ G, y ⤳ x ∧ y ∉ F) :
    topologicalKrullDim F + 1 ≤ topologicalKrullDim G := by
  have hi : IsInducing (Set.inclusion hFG) := (IsEmbedding.inclusion hFG).isInducing
  let m := TopologicalSpace.IrreducibleCloseds.map (Set.inclusion hFG) hi.continuous
  let φ : (TopologicalSpace.IrreducibleCloseds F)ᵒᵈ → (TopologicalSpace.IrreducibleCloseds G)ᵒᵈ :=
    fun Z ↦ OrderDual.toDual (m (OrderDual.ofDual Z))
  have hφ : StrictMono φ := fun a b hab ↦
    TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing hi hab
  have := Order.krullDim_add_one_le_of_strictMono φ hφ fun Z ↦ ?_
  · simpa [topologicalKrullDim] using this
  -- a generalization of the generic point of `Z` outside `F`
  let Z' : TopologicalSpace.IrreducibleCloseds F := OrderDual.ofDual Z
  let x : F := Z'.isIrreducible.genericPoint
  have hx : IsGenericPoint x Z' := Z'.isIrreducible.isGenericPoint_genericPoint Z'.isClosed
  obtain ⟨y, hyG, hyx, hyF⟩ := h x.1 x.2
  let y' : G := ⟨y, hyG⟩
  have hyx' : y' ⤳ Set.inclusion hFG x :=
    (IsInducing.subtypeVal.specializes_iff (x := y') (y := Set.inclusion hFG x)).mp hyx
  refine ⟨OrderDual.toDual ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
  change (m Z') <
    ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hZ : ((m Z') : Set G) =
      closure {Set.inclusion hFG x} := by
    change closure (Set.inclusion hFG '' (Z' : Set F)) = _
    have hZ' : (Z' : Set F) = closure {x} := hx.def.symm
    rw [hZ', closure_image_closure hi.continuous, Set.image_singleton]
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · change ((m Z') : Set G) ⊆ _
    rw [hZ]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyx'))
      isClosed_closure
  · have h1 : y' ∈ closure {Set.inclusion hFG x} := by
      rw [← hZ, heq]
      exact subset_closure rfl
    have := congrArg Subtype.val ((specializes_iff_mem_closure.mpr h1).antisymm hyx').eq
    change x.1 = y at this
    exact hyF (this ▸ x.2)

namespace Etale

/-- **The dimension of the generic fibre under an embedding**: if `g : X' ⟶ X` is an embedding
compatible with `f' : X' ⟶ S'`, `f : X ⟶ S` and `π : S' ⟶ S`, with `π` mapping the generic
point to the generic point, then the generic fibre of `f'` has dimension at most that of `f`. -/
lemma genericFiberDim_le_of_isEmbedding {X' X S' S : Scheme.{u}} [IrreducibleSpace S']
    [IrreducibleSpace S] (g : X' ⟶ X) (hg : IsEmbedding g) (f' : X' ⟶ S') (f : X ⟶ S)
    (π : S' ⟶ S) (hπ : π (genericPoint S') = genericPoint S) (w : g ≫ f = f' ≫ π) :
    genericFiberDim f' ≤ genericFiberDim f := by
  unfold genericFiberDim
  rw [IsHomeomorph.topologicalKrullDim_eq _ (f'.fiberHomeo _).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo _).isHomeomorph]
  let φ : f' ⁻¹' {genericPoint S'} → f ⁻¹' {genericPoint S} :=
    fun x ↦ ⟨g x.1, by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply,
        (Set.mem_singleton_iff.mp x.2), hπ]
      rfl⟩
  refine Topology.IsInducing.topologicalKrullDim_le (f := φ) ?_
  exact (hg.isInducing.comp Topology.IsInducing.subtypeVal).codRestrict _

/-- **The dimension of the generic fibre drops on a closed subset whose points generalize out of
it**: if `i : W ⟶ X` is an immersion and every point of the generic fibre of `f : X ⟶ S` in the
image of `i` is a specialization of a point of the generic fibre outside the image, then the
generic fibre of `i ≫ f` has dimension `+ 1 ≤` that of `f`. -/
lemma genericFiberDim_add_one_le_of_generalizes {W X S : Scheme.{u}} [IrreducibleSpace S]
    (i : W ⟶ X) [IsClosedImmersion i] (f : X ⟶ S)
    (h : ∀ x : X, f x = genericPoint S → x ∈ Set.range i →
      ∃ y : X, f y = genericPoint S ∧ y ∉ Set.range i ∧ y ⤳ x) :
    genericFiberDim (i ≫ f) + 1 ≤ genericFiberDim f := by
  unfold genericFiberDim
  -- the generic fibre of `W` is homeomorphic to its image in the generic fibre of `X`
  let G : Set X := f ⁻¹' {genericPoint S}
  let F : Set X := Set.range i ∩ G
  have hFG : F ⊆ G := Set.inter_subset_right
  have hmem : ∀ x : (i ≫ f) ⁻¹' {genericPoint S}, (⇑i ∘ Subtype.val) x ∈ F := fun x ↦
    ⟨⟨x.1, rfl⟩, by
      change f (i x.1) ∈ ({genericPoint S} : Set S)
      rw [← Scheme.Hom.comp_apply]; exact x.2⟩
  have hφ : IsInducing (Set.codRestrict (⇑i ∘ Subtype.val) F hmem) :=
    (i.isEmbedding.isInducing.comp IsInducing.subtypeVal).codRestrict hmem
  have : QuasiSober G := ((f).fiberHomeo (genericPoint S)).symm.isClosedEmbedding.quasiSober
  have hFc : IsClosed (Set.inclusion hFG '' Set.univ : Set G) := by
    rw [Set.image_univ, Set.range_inclusion]
    convert i.isClosedEmbedding.isClosed_range.preimage continuous_subtype_val using 1
    ext x
    simp [F]
  have : QuasiSober F := by
    refine (IsClosedEmbedding.mk (IsEmbedding.inclusion hFG) ?_).quasiSober
    rw [← Set.image_univ]
    exact hFc
  rw [IsHomeomorph.topologicalKrullDim_eq _ ((i ≫ f).fiberHomeo _).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo _).isHomeomorph]
  refine (show topologicalKrullDim ((i ≫ f) ⁻¹' {genericPoint S}) + 1 ≤
      topologicalKrullDim F + 1 by gcongr; exact hφ.topologicalKrullDim_le).trans ?_
  refine topologicalKrullDim_add_one_le_of_generalizes hFG fun x hx ↦ ?_
  obtain ⟨y, hy, hyi, hyx⟩ := h x hx.2 hx.1
  exact ⟨y, hy, hyx, fun hyF ↦ hyi hyF.1⟩

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Passing to a surjective closed immersion of the source**, for instance to the reduction: if
`r : X' ⟶ X` is a surjective closed immersion and `K` a bounded constructible complex on `X`, the
generic constructibility property of `R(r ≫ j)_* r^* K` implies that of `Rj_* K`, since
`K ≅ Rr_* r^* K`. -/
theorem HasDirectImageBaseChangeOnPlus.of_surjective_closedImmersion {S X X' Y : Scheme.{u}}
    {fY : Y ⟶ S} (j : X ⟶ Y) [LocallyOfFiniteType (j ≫ fY)] (r : X' ⟶ X) [IsClosedImmersion r]
    [Surjective r]
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (_root_.DerivedCategory.Plus.ι.obj K)) {U : Set S}
    (h : HasDirectImageBaseChangeOnPlus Λ fY (r ≫ j)
      (((r)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  have : IsFinite r := ((IsClosedImmersion.iff_isFinite_and_mono r).1 inferInstance).1
  have h₁ := HasDirectImageBaseChangeOnPlus.of_comp r j
    (hasDirectImageBaseChangeOnPlus_of_isClosedImmersion (fX := j ≫ fY) r
      (hK.mapDerivedCategory_upperStar r) U) h
  refine h₁.of_iso ?_
  -- `K ≅ Rr_* r^* K`, as `r^*` is an equivalence
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) r
  have : IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).unit :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).unit_isIso_of_L_fully_faithful
  let e : _root_.DerivedCategory.Plus.ι.obj ((r)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
      (((r)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) ≅
      _root_.DerivedCategory.Plus.ι.obj K :=
    ((r)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _) ≪≫
      (rightDerivedFunctorLowerStarIsoMapDerivedCategory _ r).app _ ≪≫
      (Functor.mapDerivedCategoryCompIso ((r)^*[ModuleCat.{u + 1} Λ])
        ((r)_*[ModuleCat.{u + 1} Λ])).app _ ≪≫
      (Functor.mapDerivedCategoryNatIso
        (asIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).unit).symm).app _ ≪≫
      (Functor.mapDerivedCategoryIdIso _).app _
  exact _root_.DerivedCategory.Plus.ι.preimageIso e

end Etale

end AlgebraicGeometry
