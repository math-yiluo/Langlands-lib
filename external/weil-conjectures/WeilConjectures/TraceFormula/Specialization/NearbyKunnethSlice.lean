/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.SliceSupport
public import WeilConjectures.TraceFormula.Specialization.TraitSlice

/-!

# The generic slices of the finite-support step of Gabber's Künneth formula

Let `S = Spec k'⟦t⟧` and let `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`), with
`x = X ∈ k'(X)` transcendental (`AlgebraicGeometry.traitSliceCoord`). For a model `M` over `S` with
a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, the special fibre `b_s : 𝒳_s ⟶ 𝔸¹_{k'}` of `b`
(`ProEtale.CondensedRing.NearbyCyclesModel.specialCoordinate`) and the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`), every point of `𝒳_s` lying over the
generic point of the special-fibre line `𝔸¹_{k'}` is in the image of the special fibre
`(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧)_s ⟶ 𝒳_s` of the slice
(`NearbyCyclesModel.mem_range_sliceSpecialMap`). This is how the vanishing of the cone of the
Künneth map over the slices is turned into its vanishing over the generic point of the coordinate
line (blueprint `proposition-external-kunneth-formula-nearby-cycles`, "Finite support").

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k' : Type u) [Field k']

/-- The algebraically closed field `K = k'(X)^alg` of the generic slices: the residue field of the
geometric generic point of the special-fibre line `𝔸¹_{k'}`. -/
abbrev traitSliceField : Type u :=
  AlgebraicClosure (RatFunc k')

/-- The field `K = k'(x)^alg` of the generic slices has the characteristic of `k'`. -/
lemma ringChar_traitSliceField : ringChar (traitSliceField k') = ringChar k' :=
  (Algebra.ringChar_eq k' (traitSliceField k')).symm

/-- The coordinate `x = X ∈ k'(X) ⊆ K` of the generic slices. -/
noncomputable def traitSliceCoord : traitSliceField k' :=
  algebraMap (RatFunc k') (traitSliceField k') RatFunc.X

/-- The coordinate of the generic slices is transcendental over `k'`. -/
lemma transcendental_traitSliceCoord : Transcendental k' (traitSliceCoord k') :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc k') (traitSliceField k')).injective).2
    RatFunc.transcendental_X

/-- The point `x : Spec K ⟶ 𝔸¹_{k'}` of the generic slices is the generic point of the
special-fibre line. -/
lemma isGenericPoint_traitSlicePoint_traitSliceCoord (p : Spec (.of (traitSliceField k'))) :
    IsGenericPoint (traitSlicePoint (k' := k') (traitSliceCoord k') p) Set.univ :=
  isGenericPoint_traitSlicePoint _ (transcendental_traitSliceCoord k') p

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k'} {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The special fibre `b_s : 𝒳_s ⟶ 𝔸¹_{k'}` of a coordinate `b : 𝒳 ⟶ 𝔸¹_S` of a model of finite
type over the trait `S = Spec k'⟦t⟧`: the base change of `b` along the closed point of `S`. -/
noncomputable def specialCoordinate (hM : M.IsTraitModelOver q g) {n : Type u}
    (b : M.total ⟶ 𝔸(n; trait k')) (hb : b ≫ 𝔸(n; trait k') ↘ trait k' = q) :
    X'.left ⟶ 𝔸(n; Spec (.of k')) :=
  (AffineSpace.isPullback_map (n := n) (traitClosedPoint k')).lift (M.i ≫ b) X'.hom (by
    rw [Category.assoc, hb, hM.isPullback_i.w])

@[reassoc (attr := simp)]
lemma specialCoordinate_map (hM : M.IsTraitModelOver q g) {n : Type u}
    (b : M.total ⟶ 𝔸(n; trait k')) (hb : b ≫ 𝔸(n; trait k') ↘ trait k' = q) :
    specialCoordinate hM b hb ≫ AffineSpace.map n (traitClosedPoint k') = M.i ≫ b :=
  (AffineSpace.isPullback_map (n := n) (traitClosedPoint k')).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma specialCoordinate_over (hM : M.IsTraitModelOver q g) {n : Type u}
    (b : M.total ⟶ 𝔸(n; trait k')) (hb : b ≫ 𝔸(n; trait k') ↘ trait k' = q) :
    specialCoordinate hM b hb ≫ 𝔸(n; Spec (.of k')) ↘ Spec (.of k') = X'.hom :=
  (AffineSpace.isPullback_map (n := n) (traitClosedPoint k')).lift_snd _ _ _

/-- The inclusion of the special fibre of a model of finite type over the trait is a closed
immersion: it is a base change of the closed immersion of the closed point of the trait. -/
lemma IsTraitModelOver.isClosedImmersion_i (hM : M.IsTraitModelOver q g) :
    IsClosedImmersion M.i :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hM.isPullback_i.flip inferInstance

/-- The special fibre of a model of finite type over the trait is injective into its total space. -/
lemma IsTraitModelOver.injective_i (hM : M.IsTraitModelOver q g) : Function.Injective M.i :=
  have := hM.isClosedImmersion_i
  M.i.isClosedEmbedding.injective

/-- **The special fibre of a generic slice covers the generic fibre of the coordinate**: for a
coordinate `b : 𝒳 ⟶ 𝔸¹_S` of a model of finite type over the trait and `x ∈ K` transcendental over
`k'`, every point of the special fibre `𝒳_s` whose image under `b_s` is the generic point of the
special-fibre line lies in the image of the special fibre `(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧)_s ⟶ 𝒳_s` of
the generic slice. Indeed `b` maps it to the image of the closed point of `Spec K⟦t⟧` under the
generic slice `σ` (`AlgebraicGeometry.traitClosedPoint_traitSlice`), so it lifts to the fibre
product, and `i : 𝒳_s ⟶ 𝒳` is injective. -/
lemma mem_range_sliceSpecialMap (x : K) (hx : Transcendental k' x) (hM : M.IsTraitModelOver q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (v : X'.left)
    (hv : IsGenericPoint (specialCoordinate hM b hb v) Set.univ) :
    v ∈ Set.range (sliceSpecialMap x hM hb) := by
  let pt : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  have h₁ : specialCoordinate hM b hb v = traitSlicePoint x pt :=
    hv.eq (isGenericPoint_traitSlicePoint x hx pt)
  have h₂ : b (M.i v) = traitSlice x (traitClosedPoint K pt) := by
    rw [← Scheme.Hom.comp_apply, ← specialCoordinate_map hM b hb, Scheme.Hom.comp_apply, h₁,
      ← Scheme.Hom.comp_apply, ← traitClosedPoint_traitSlice, Scheme.Hom.comp_apply]
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ h₂
  obtain ⟨w', hw'₁, hw'₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd b (traitSlice x)) (g := traitClosedPoint K) w pt hw₂
  refine ⟨w', hM.injective_i ?_⟩
  rw [← Scheme.Hom.comp_apply, sliceSpecialMap, hM.isPullback_i.lift_fst, Scheme.Hom.comp_apply,
    hw'₁, hw₁]

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
