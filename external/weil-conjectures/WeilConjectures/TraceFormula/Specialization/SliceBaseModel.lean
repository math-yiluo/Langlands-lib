/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Generic slices of trait models of the base

Let `M` be a trait model over the base of a `k`-scheme `X` (`NearbyCyclesModel.IsTraitModelOfBase`),
with total space `𝒳` over the trait `S = Spec k'⟦t⟧`, and let `e : 𝒳 ⟶ X` be the factorisation of
its identification `ε`. Let `b₀ : X ⟶ 𝔸¹_k` be a coordinate on `X` and `b : 𝒳 ⟶ 𝔸¹_S` a
coordinate on `𝒳` over `S` lifting `e ≫ b₀`. Let `K` be a field extension of `k'` and of the
rational function field `k(x) = RatFunc k` (compatibly over `k`), and let the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`) be taken at the image of `x` in `K`.
The base change of `M` along `σ` (`NearbyCyclesModel.baseChange`) is then a trait model over the
base of the generic fibre `X₁ = X ×_{𝔸¹_k} Spec k(x)` of `b₀`
(`AlgebraicGeometry.genericCoordinateFibre`), as a `k(x)`-scheme, with trait field `K`:
this is `NearbyCyclesModel.isTraitModelOfBase_sliceBaseModel`.

The geometric generic fibre `𝒳'' ×_{K⟦t⟧} Spec Ω_K` of the slice is
`𝒳_η̄ ×_{𝔸¹_Ω} Spec Ω_K`, and the open immersion `𝒳_η̄ ⟶ X ×_k Spec Ω` base changes to an open
immersion into `(X ×_k Spec Ω) ×_{𝔸¹_Ω} Spec Ω_K = X ×_{𝔸¹_k} Spec Ω_K = X₁ ×_{k(x)} Spec Ω_K`.

For `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`) and `x ↦ traitSliceCoord k'`, the
embedding `k(x) ⟶ K` is `AlgebraicGeometry.sliceBaseRingHom`
(`NearbyCyclesModel.isTraitModelOfBase_sliceBaseModel_traitSliceField`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section SliceBaseField

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The coefficientwise map `k[X] ⟶ k'[X] ⟶ k'(X) ⟶ k'(X)^alg` is injective. -/
lemma injective_sliceBasePolynomialMap :
    Function.Injective ((algebraMap (RatFunc k') (traitSliceField k')).comp
      ((algebraMap (Polynomial k') (RatFunc k')).comp
        (Polynomial.mapRingHom (algebraMap k k')))) := by
  rw [RingHom.coe_comp, RingHom.coe_comp]
  exact (algebraMap (RatFunc k') (traitSliceField k')).injective.comp
    ((IsFractionRing.injective (Polynomial k') (RatFunc k')).comp
      (Polynomial.map_injective _ (algebraMap k k').injective))

/-- The embedding `k(x) ⟶ K = k'(x)^alg` of the generic slices, extending `k ⟶ k'` by
`x ↦ x`. -/
noncomputable def sliceBaseRingHom : RatFunc k →+* traitSliceField k' :=
  RatFunc.liftRingHom _
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (injective_sliceBasePolynomialMap k k'))

/-- The embedding `k(x) ⟶ K` maps `x` to the coordinate of the generic slices. -/
lemma sliceBaseRingHom_X : sliceBaseRingHom k k' RatFunc.X = traitSliceCoord k' := by
  rw [sliceBaseRingHom, ← RatFunc.algebraMap_X, RatFunc.liftRingHom_algebraMap]
  simp [traitSliceCoord, RatFunc.algebraMap_X]

/-- The embedding `k(x) ⟶ K` lies over `k ⟶ k'`. -/
lemma sliceBaseRingHom_comp_algebraMap :
    (sliceBaseRingHom k k').comp (algebraMap k (RatFunc k)) =
      (algebraMap k' (traitSliceField k')).comp (algebraMap k k') := by
  ext a
  have hCa : algebraMap k (RatFunc k) a = algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a) :=
    (RatFunc.algebraMap_C a).symm
  rw [RingHom.comp_apply, hCa, sliceBaseRingHom, RatFunc.liftRingHom_algebraMap]
  simp [IsScalarTower.algebraMap_apply k' (RatFunc k') (traitSliceField k'), RatFunc.algebraMap_C]

end SliceBaseField

section SlicePoint

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k'] {K : Type u} [Field K]
  [Algebra k' K] [Algebra (RatFunc k) K] {x : K}

/-- **The generic slice over the base**: if `k(x) ⟶ K` maps `x` to `x` and lies over `k ⟶ k'`,
the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` at `x` lies over the point `x : Spec k(x) ⟶ 𝔸¹_k`
of the base. -/
lemma traitSlice_map_traitToBase (hX : algebraMap (RatFunc k) K RatFunc.X = x)
    (hC : (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k)) =
      (algebraMap k' K).comp (algebraMap k k')) :
    traitSlice x ≫ AffineSpace.map (ULift.{u} (Fin 1)) (traitToBase k k') =
      traitToBase (RatFunc k) K ≫ traitSlicePoint (k' := k) (RatFunc.X : RatFunc k) := by
  simp only [traitToBase, traitSlicePoint, traitSlice]
  rw [AffineSpace.map_SpecMap, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · have := congr($hC a)
    simp only [RingHom.comp_apply] at this
    simp only [traitSliceRingHom, ConcreteCategory.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, RingHom.coe_coe,
      MvPolynomial.algHom_C, PowerSeries.algebraMap_apply, PowerSeries.map_C, this]
  · simp only [traitSliceRingHom, ConcreteCategory.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', RingHom.coe_coe,
      MvPolynomial.aeval_X, PowerSeries.algebraMap_apply, hX]

/-- The geometric generic point `Spec Ω_K ⟶ 𝔸¹_Ω` of the generic slice: the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` restricted to `Spec Ω_K`, as a point of the generic-fibre line
`𝔸¹_Ω = 𝔸¹_S ×_S Spec Ω` over `Spec Ω_K ⟶ Spec Ω`. -/
noncomputable def sliceGenericPoint (x : K) :
    Spec (.of (traitGenericField K)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of (traitGenericField k'))) :=
  (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (traitGenericPoint k')).lift
    (traitGenericPoint K ≫ traitSlice x) (traitGenericPointMap k' K) (by
      rw [Category.assoc, traitSlice_over, traitGenericPoint_traitMap])

@[reassoc (attr := simp)]
lemma sliceGenericPoint_map :
    sliceGenericPoint (k' := k') x ≫ AffineSpace.map _ (traitGenericPoint k') =
      traitGenericPoint K ≫ traitSlice x :=
  (AffineSpace.isPullback_map _).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceGenericPoint_over :
    sliceGenericPoint (k' := k') x ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of (traitGenericField k'))) ↘
          Spec (.of (traitGenericField k')) =
      traitGenericPointMap k' K :=
  (AffineSpace.isPullback_map _).lift_snd _ _ _

/-- The geometric generic point of the generic slice lies over the point `x : Spec k(x) ⟶ 𝔸¹_k`
of the base. -/
lemma sliceGenericPoint_map_traitToBase (hX : algebraMap (RatFunc k) K RatFunc.X = x)
    (hC : (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k)) =
      (algebraMap k' K).comp (algebraMap k k')) :
    sliceGenericPoint (k' := k') x ≫
        AffineSpace.map _ (traitGenericPoint k' ≫ traitToBase k k') =
      (traitGenericPoint K ≫ traitToBase (RatFunc k) K) ≫
        traitSlicePoint (k' := k) (RatFunc.X : RatFunc k) := by
  rw [AffineSpace.map_comp, sliceGenericPoint_map_assoc, traitSlice_map_traitToBase hX hC,
    Category.assoc]

end SlicePoint

section CoordinateBaseChange

variable {n : Type u} {S X T : Scheme.{u}} (b₀ : X ⟶ 𝔸(n; S)) {p : X ⟶ S}
  (hb₀ : b₀ ≫ 𝔸(n; S) ↘ S = p) (f : T ⟶ S)

/-- The base change `X ×_S T ⟶ 𝔸ⁿ_T` of a coordinate `b₀ : X ⟶ 𝔸ⁿ_S` over `S`. -/
noncomputable def coordinateBaseChange : pullback p f ⟶ 𝔸(n; T) :=
  (AffineSpace.isPullback_map f).lift (pullback.fst _ _ ≫ b₀) (pullback.snd _ _) (by
    rw [Category.assoc, hb₀, pullback.condition])

@[reassoc (attr := simp)]
lemma coordinateBaseChange_map :
    coordinateBaseChange b₀ hb₀ f ≫ AffineSpace.map n f = pullback.fst _ _ ≫ b₀ :=
  (AffineSpace.isPullback_map f).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma coordinateBaseChange_over :
    coordinateBaseChange b₀ hb₀ f ≫ 𝔸(n; T) ↘ T = pullback.snd _ _ :=
  (AffineSpace.isPullback_map f).lift_snd _ _ _

/-- The base change of a coordinate is a base change: `X ×_S T = X ×_{𝔸ⁿ_S} 𝔸ⁿ_T`. -/
lemma isPullback_coordinateBaseChange :
    IsPullback (pullback.fst p f) (coordinateBaseChange b₀ hb₀ f) b₀ (AffineSpace.map n f) :=
  IsPullback.of_bot (by rw [coordinateBaseChange_over, hb₀]; exact IsPullback.of_hasPullback p f)
    (coordinateBaseChange_map b₀ hb₀ f).symm (AffineSpace.isPullback_map f)

/-- A coordinate on a base change: if `G = Y ×_S T` and `c : G ⟶ 𝔸ⁿ_T` lifts a coordinate
`b : Y ⟶ 𝔸ⁿ_S` over `S`, then `G = Y ×_{𝔸ⁿ_S} 𝔸ⁿ_T` along `b` and `c`. -/
lemma isPullback_affineSpace_of_isPullback {G Y : Scheme.{u}} {j : G ⟶ Y} {g : G ⟶ T}
    {q : Y ⟶ S} (hj : IsPullback j g q f) {b : Y ⟶ 𝔸(n; S)} (hb : b ≫ 𝔸(n; S) ↘ S = q)
    {c : G ⟶ 𝔸(n; T)} (hc₁ : c ≫ 𝔸(n; T) ↘ T = g) (hc₂ : c ≫ AffineSpace.map n f = j ≫ b) :
    IsPullback c j (AffineSpace.map n f) b :=
  IsPullback.of_right (by rw [hc₁, hb]; exact hj.flip) hc₂ (AffineSpace.isPullback_map f).flip

end CoordinateBaseChange

section GenericCoordinateFibre

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

/-- The generic fibre `X₁ = X ×_{𝔸¹_k} Spec k(x)` of a coordinate `b₀ : X ⟶ 𝔸¹_k`, as a scheme
over the rational function field `k(x)`. -/
noncomputable def genericCoordinateFibre (b₀ : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) :
    Over (Spec (.of (RatFunc k))) :=
  Over.mk (pullback.snd b₀ (traitSlicePoint (k' := k) (RatFunc.X : RatFunc k)))

lemma genericCoordinateFibre_hom (b₀ : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) :
    (genericCoordinateFibre b₀).hom =
      pullback.snd b₀ (traitSlicePoint (k' := k) (RatFunc.X : RatFunc k)) :=
  rfl

end GenericCoordinateFibre

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k'] {K : Type u} [Field K]
  [Algebra k' K] [Algebra (RatFunc k) K] {x : K}
  (hX : algebraMap (RatFunc k) K RatFunc.X = x)
  (hC : (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k)) =
    (algebraMap k' K).comp (algebraMap k k'))
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  (b₀ : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  {e : M.total ⟶ X.left}
  (hbe : b ≫ AffineSpace.map (ULift.{u} (Fin 1)) (traitToBase k k') = e ≫ b₀)

include hX hC hbe in
/-- The two maps from the total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` of the slice to `𝔸¹_k` agree. -/
@[reassoc]
lemma sliceBase_condition :
    (pullback.fst b (traitSlice x) ≫ e) ≫ b₀ =
      (pullback.snd b (traitSlice x) ≫ traitToBase (RatFunc k) K) ≫
        traitSlicePoint (k' := k) (RatFunc.X : RatFunc k) := by
  rw [Category.assoc, Category.assoc, ← hbe, pullback.condition_assoc,
    traitSlice_map_traitToBase hX hC]

/-- The map `𝒳'' ⟶ X₁ = X ×_{𝔸¹_k} Spec k(x)` from the total space of the slice to the generic
fibre of the coordinate `b₀`. -/
noncomputable def sliceBaseTotalMap :
    pullback b (traitSlice x) ⟶ (genericCoordinateFibre b₀).left :=
  pullback.lift _ _ (sliceBase_condition hX hC b₀ hbe)

@[reassoc (attr := simp)]
lemma sliceBaseTotalMap_fst :
    sliceBaseTotalMap hX hC b₀ hbe ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceBaseTotalMap_hom :
    sliceBaseTotalMap hX hC b₀ hbe ≫ (genericCoordinateFibre b₀).hom =
      pullback.snd _ _ ≫ traitToBase (RatFunc k) K :=
  pullback.lift_snd _ _ _

/-- The *slice model over the base*: the base change of `M` along the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`, with total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧`, geometric generic fibre
`𝒳'' ×_{K⟦t⟧} Spec Ω_K`, special fibre `𝒳'' ×_{K⟦t⟧} Spec K`, and identification `ε` through
the map `𝒳'' ⟶ X₁` to the generic fibre of the coordinate `b₀`. -/
@[simps]
noncomputable def sliceBaseModel :
    NearbyCyclesModel (genericCoordinateFibre b₀).left (baseChangeSpecial b (traitSlice x)).left
    where
  total := pullback b (traitSlice x)
  generic := pullback (pullback.snd b (traitSlice x)) (traitGenericPoint K)
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := pullback.fst _ _ ≫ sliceBaseTotalMap hX hC b₀ hbe


/-- **The generic slice of a trait model over the base is a trait model over the base**: for a
trait model `M` over the base of a `k`-scheme `X`, with `ε = j ≫ e`, a coordinate
`b₀ : X ⟶ 𝔸¹_k` over `k`, and a coordinate `b : 𝒳 ⟶ 𝔸¹_S` over `S` lifting `e ≫ b₀`, the base
change of `M` along the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` is a trait model over the base of
the generic fibre `X₁ = X ×_{𝔸¹_k} Spec k(x)` of `b₀`, with base field `k(x)` and trait field
`K`. -/
theorem isTraitModelOfBase_sliceBaseModel {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOfBase k q g)
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (heε : M.j ≫ e = M.ε)
    (hb₀ : b₀ ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) = X.hom) :
    (sliceBaseModel hX hC b₀ hbe).IsTraitModelOfBase (RatFunc k)
      (X := genericCoordinateFibre b₀) (X' := baseChangeSpecial b (traitSlice x))
      (pullback.snd b (traitSlice x)) (pullback.snd _ _) := by
  have hM := h.isTraitModelOver
  have hB := IsTraitModelOver.baseChange hM b hb (traitSlice x) (traitSlice_over x)
  refine ⟨⟨hB.1, hB.2, hB.3, hB.4, hB.5⟩,
    ⟨sliceBaseTotalMap hX hC b₀ hbe, rfl, sliceBaseTotalMap_hom hX hC b₀ hbe⟩, ?_⟩
  obtain ⟨u, hu, hu₁, hu₂⟩ := h.exists_openImmersion
  -- the coordinate `𝒳_η̄ ⟶ X ×_k Spec Ω ⟶ 𝔸¹_Ω` of the geometric generic fibre of `M`
  let pA := coordinateBaseChange b₀ hb₀ (traitGenericPoint k' ≫ traitToBase k k')
  have hR := isPullback_coordinateBaseChange b₀ hb₀ (traitGenericPoint k' ≫ traitToBase k k')
  let a := baseChangeGenericMap hM b hb (traitSlice x) (traitSlice_over x)
  have E1 : u ≫ pA ≫ AffineSpace.map _ (traitGenericPoint k') = M.j ≫ b := by
    refine (AffineSpace.isPullback_map (traitToBase k k')).hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← AffineSpace.map_comp, coordinateBaseChange_map, reassoc_of% hu₁, ← reassoc_of% heε,
        hbe]
    · simp only [Category.assoc]
      rw [AffineSpace.map_over, coordinateBaseChange_over_assoc, reassoc_of% hu₂, hb,
        hM.isPullback_j.w]
  have h1 : IsPullback (u ≫ pA) M.j (AffineSpace.map _ (traitGenericPoint k')) b :=
    isPullback_affineSpace_of_isPullback _ hM.isPullback_j hb
      (by rw [Category.assoc, coordinateBaseChange_over, hu₂]) (by rw [Category.assoc, E1])
  have E2 : a ≫ u ≫ pA = pullback.snd _ _ ≫ sliceGenericPoint x := by
    refine (AffineSpace.isPullback_map (traitGenericPoint k')).hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [E1, baseChangeGenericMap_j_assoc, pullback.condition, pullback.condition_assoc,
        sliceGenericPoint_map]
    · simp only [Category.assoc]
      rw [coordinateBaseChange_over, hu₂, baseChangeGenericMap_g, sliceGenericPoint_over]
  have hi : IsPullback a (pullback.snd _ _) (u ≫ pA) (sliceGenericPoint x) :=
    IsPullback.of_right (by
      rw [baseChangeGenericMap_j, sliceGenericPoint_map]
      exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)) E2 h1.flip
  -- the base change `X₁ ×_{k(x)} Spec Ω_K = (X ×_k Spec Ω) ×_{𝔸¹_Ω} Spec Ω_K`
  let c := hR.lift (pullback.fst (genericCoordinateFibre b₀).hom
      (traitGenericPoint K ≫ traitToBase (RatFunc k) K) ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ sliceGenericPoint x) (by
      rw [Category.assoc, Category.assoc, sliceGenericPoint_map_traitToBase hX hC,
        pullback.condition, ← Category.assoc, ← genericCoordinateFibre_hom, pullback.condition]
      simp only [Category.assoc])
  have hQ : IsPullback c (pullback.snd _ _) pA (sliceGenericPoint x) :=
    IsPullback.of_right (by
      rw [hR.lift_fst, sliceGenericPoint_map_traitToBase hX hC]
      exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _))
      (hR.lift_snd _ _ _) hR
  let u₁ := pullback.lift (pullback.fst _ _ ≫ sliceBaseTotalMap hX hC b₀ hbe)
    (pullback.snd _ _) (by
      rw [Category.assoc, sliceBaseTotalMap_hom, pullback.condition_assoc] :
      (pullback.fst _ _ ≫ sliceBaseTotalMap hX hC b₀ hbe) ≫ (genericCoordinateFibre b₀).hom =
        pullback.snd (pullback.snd b (traitSlice x)) (traitGenericPoint K) ≫
          traitGenericPoint K ≫ traitToBase (RatFunc k) K)
  have E4 : a ≫ u = u₁ ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hu₁, ← heε, baseChangeGenericMap_j_assoc, Category.assoc,
        hR.lift_fst, pullback.lift_fst_assoc, Category.assoc, sliceBaseTotalMap_fst]
    · rw [Category.assoc, hu₂, baseChangeGenericMap_g, Category.assoc,
        ← coordinateBaseChange_over b₀ hb₀, hR.lift_snd_assoc]
      simp only [Category.assoc]
      rw [pullback.lift_snd_assoc, sliceGenericPoint_over]
  have htop : IsPullback a u₁ u c :=
    IsPullback.of_bot (by rw [pullback.lift_snd]; exact hi) E4 hQ
  exact ⟨u₁, MorphismProperty.of_isPullback htop hu, pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _⟩

/-- **The generic slice of a trait model over the base, at `K = k'(x)^alg`**: the case of
`NearbyCyclesModel.isTraitModelOfBase_sliceBaseModel` for the field `K = k'(x)^alg` of the generic
slices (`AlgebraicGeometry.traitSliceField`), the coordinate `x = traitSliceCoord k'` and the
embedding `k(x) ⟶ K` extending `k ⟶ k'` (`AlgebraicGeometry.sliceBaseRingHom`). -/
theorem isTraitModelOfBase_sliceBaseModel_traitSliceField {X : Over (Spec (.of k))}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
    (b₀ : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')} {e : M.total ⟶ X.left}
    (hbe : b ≫ AffineSpace.map (ULift.{u} (Fin 1)) (traitToBase k k') = e ≫ b₀)
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfBase k q g)
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (heε : M.j ≫ e = M.ε)
    (hb₀ : b₀ ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) = X.hom) :
    letI := (sliceBaseRingHom k k').toAlgebra
    (sliceBaseModel (sliceBaseRingHom_X k k') (sliceBaseRingHom_comp_algebraMap k k') b₀
      hbe).IsTraitModelOfBase (RatFunc k) (X := genericCoordinateFibre b₀)
      (X' := baseChangeSpecial b (traitSlice (traitSliceCoord k')))
      (pullback.snd b (traitSlice (traitSliceCoord k'))) (pullback.snd _ _) :=
  letI := (sliceBaseRingHom k k').toAlgebra
  isTraitModelOfBase_sliceBaseModel _ _ b₀ hbe h hb heε hb₀

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
