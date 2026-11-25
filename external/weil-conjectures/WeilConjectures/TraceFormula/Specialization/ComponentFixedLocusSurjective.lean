/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentFixedLocusModel
public import WeilConjectures.TraceFormula.Specialization.ContractingFixedComponent
public import WeilConjectures.TraceFormula.Specialization.DeformationModelGeneric
public import WeilConjectures.TraceFormula.Specialization.TraitPowMap

/-!
# The deformed fixed locus has no further points

Let `c` be contracting at `y`, `F` a fixed locus of `c` and `j : B ⟶ F` with a rational point `b`
of `B` over `y`. The map `ι_F : 𝒟_b B ⟶ F̃` of total spaces (`componentFixedLocusTotalLift`) is
surjective as soon as `j` is (blueprint `lemma-fixed-point-scheme-deformation`, last assertion,
for `Z = {x}`). Following the blueprint, a point `p` of `F̃ ⊂ 𝒞` lies over the closed or over the
generic point of the trait:

* over the closed point, `p` comes from a point `s` of the special fibre `C' = N_y C ⊗ k'` with
  `γ₁ s = γ₂ s`; as `γ₂` lands in the zero section, so does `γ₁ s`, hence `s` lies on the zero
  section of `C'`, which is a single point, the image of the vertex of `B''`;
* over the generic point, `p` comes from a point of the geometric generic fibre
  `𝒞_Ω = C ×_k Spec Ω`, whose image in `C` lies in `F` since the projection `F̃ ⟶ 𝒞 ⟶ C`
  equalizes `c₁` and `c₂`; as `𝒟_b B_Ω = B ×_C 𝒞_Ω`, it comes from `B` if `j` is surjective.

If moreover `B ⊂ F ⊂ C` is closed, `ι_F` is a surjective closed immersion, hence a universal
homeomorphism. If `F` is connected, `j` is automatically surjective, since then `F` is a single
point (`Correspondence.IsContractingAt.subsingleton_component`).

## Main statements

- `AlgebraicGeometry.mem_range_traitGenericPoint_of_notMem_range_traitClosedPoint`: the trait has
  two points.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationSpecialFibreMap_vertex_mem_range`: the
  vertex is mapped to the zero section.
- `Correspondence.IsContractingAt.surjective_componentFixedLocusTotalLift`: `ι_F` is surjective.
- `Correspondence.IsContractingAt.isUniversalHomeomorphism_componentFixedLocusTotalLift`.
- `IsContractingAt.isUniversalHomeomorphism_componentFixedLocusTotalLift_of_connected`:
  the case of a connected fixed locus.
- `Correspondence.IsContractingAt.isIso_componentFixedLocusTotalLift_of_isReduced`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

section Trait

variable (k' : Type u) [Field k']

/-- **The trait `Spec k'⟦t⟧` has two points**: a point which is not the closed point is the image
of the geometric generic point. -/
lemma mem_range_traitGenericPoint_of_notMem_range_traitClosedPoint (z : trait k')
    (hz : z ∉ Set.range (traitClosedPoint k')) : z ∈ Set.range (traitGenericPoint k') := by
  rw [mem_range_traitClosedPoint_iff] at hz
  have hbot : z.asIdeal = ⊥ := by
    by_contra hne
    have hmax := z.isPrime.isMaximal hne
    refine hz ?_
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun h ↦ by
      simpa using (PowerSeries.isUnit_iff_constantCoeff.mp h)
  obtain ⟨p⟩ : Nonempty (Spec (.of (traitGenericField k'))) :=
    ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (traitGenericField k'))⟩
  refine ⟨p, PrimeSpectrum.ext ?_⟩
  rw [hbot, traitGenericPoint, Spec.map_base]
  change Ideal.comap (algebraMap (PowerSeries k') (traitGenericField k')) p.asIdeal = ⊥
  have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hp, ← RingHom.ker_eq_comap_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  rw [IsScalarTower.algebraMap_apply (PowerSeries k') (FractionRing (PowerSeries k'))] at ha
  exact (IsFractionRing.injective (PowerSeries k') (FractionRing (PowerSeries k')))
    ((map_eq_zero _).mp ha |>.trans (map_zero _).symm)

end Trait

namespace ProEtale.CondensedRing

open Scheme

section Vertex

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The vertex of the special fibre of the deformation to the normal cone of a rational point
lies on the zero section of the normal cone. -/
lemma deformationVertex_mem_range_normalConeZeroSection {X : Over (Spec (.of k))}
    (x : RationalPoint X) (pt : (point k').left) :
    deformationSpecialFibreToNormalCone X x.left.ker k' ((deformationVertex x k').left pt) ∈
      Set.range x.left.ker.normalConeZeroSection := by
  refine ⟨quotientSpecLift x (Spec.map (CommRingCat.ofHom (algebraMap k k')) pt),
    x.left.ker.normalConeToDeformationSpace.isClosedEmbedding.injective ?_⟩
  have e : (deformationVertex x k').left ≫ deformationSpecialFibreToNormalCone X x.left.ker k' ≫
      x.left.ker.normalConeToDeformationSpace =
      Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ quotientSpecLift x ≫
        x.left.ker.normalConeZeroSection ≫ x.left.ker.normalConeToDeformationSpace := by
    rw [deformationSpecialFibreToNormalCone_normalConeToDeformationSpace]
    exact (deformationVertex_toSpace x k').trans (by rw [deformationSpaceVertex])
  have := congrArg (fun f ↦ f pt) e
  simp only [Scheme.Hom.comp_apply] at this
  exact this.symm

/-- **The vertex is mapped to the zero section**: for `f : X ⟶ Y` with `f^* I ⊆ ker x`, the
morphism of special fibres maps the vertex of the tangent cone at `x` into the zero section. -/
lemma deformationSpecialFibreMap_vertex_mem_range {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
    (x : RationalPoint X) {I : Y.left.IdealSheafData}
    (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
        x.left.ker.siteIdeal U') (pt : (point k').left) :
    (deformationSpecialFibreMap f hJ k').left ((deformationVertex x k').left pt) ∈
      Set.range (deformationSpecialFibreZeroSection Y I k').left := by
  rw [range_deformationSpecialFibreZeroSection, Set.mem_preimage, ← Scheme.Hom.comp_apply,
    deformationSpecialFibreMap_toNormalCone, Scheme.Hom.comp_apply]
  obtain ⟨w, hw⟩ := deformationVertex_mem_range_normalConeZeroSection k' x pt
  rw [← hw, ← Scheme.Hom.comp_apply, IdealSheafData.normalConeZeroSection_normalConeMap,
    Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

end Vertex

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  (F : c.FixedLocus) {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)

/-- The projection `F̃ ⟶ 𝒞` of the total space of the deformed fixed locus. -/
noncomputable abbrev deformedFixedLocusTotalFst : deformedFixedLocusTotal hc k' F ⟶
    deformationTotal c.C y.left.ker k' :=
  pullback.fst (deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂)
    (deformationDiagTotal X (y ≫ c.c₁).left.ker k')

instance : IsClosedImmersion (deformedFixedLocusTotalFst hc k' F) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/-- The two deformed legs agree on the total space `F̃` of the deformed fixed locus. -/
@[reassoc]
lemma deformedFixedLocusTotalFst_comp_deformationTotalMap :
    deformedFixedLocusTotalFst hc k' F ≫ deformationTotalMap c.c₁ hc.ker_map_le_c₁ k' =
      deformedFixedLocusTotalFst hc k' F ≫ deformationTotalMap c.c₂ hc.ker_map_le_c₂ k' := by
  have h := pullback.condition (f := deformationProdLiftTotal k' c.c₁ hc.ker_map_le_c₁ c.c₂
    hc.ker_map_le_c₂) (g := deformationDiagTotal X (y ≫ c.c₁).left.ker k')
  have h₁ := h =≫ pullback.fst _ _
  have h₂ := h =≫ pullback.snd _ _
  simp only [Category.assoc, deformationProdLiftTotal, deformationDiagTotal, pullback.lift_fst,
    pullback.lift_snd, Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The projection `F̃ ⟶ 𝒞 ⟶ C` equalizes `c₁` and `c₂`, so it lands in the fixed locus `F`. -/
lemma deformationTotalToBase_deformedFixedLocusTotalFst_mem_range
    (p : deformedFixedLocusTotal hc k' F) :
    deformationTotalToBase c.C y.left.ker k' (deformedFixedLocusTotalFst hc k' F p) ∈
      Set.range F.ι.left := by
  let W : Over (Spec (.of k)) := Over.mk (deformedFixedLocusTotalFst hc k' F ≫
    deformationTotalToTrait c.C y.left.ker k' ≫ traitToBase k k')
  let g : W ⟶ c.C := Over.homMk (deformedFixedLocusTotalFst hc k' F ≫
      deformationTotalToBase c.C y.left.ker k') (by
    rw [Category.assoc, deformationTotalToBase_hom]
    rfl)
  have hg : g ≫ c.c₁ = g ≫ c.c₂ := by
    ext1
    simp only [g, Over.comp_left, Over.homMk_left, Category.assoc]
    rw [← deformationTotalMap_toBase c.c₁ hc.ker_map_le_c₁ k',
      ← deformationTotalMap_toBase c.c₂ hc.ker_map_le_c₂ k',
      deformedFixedLocusTotalFst_comp_deformationTotalMap_assoc]
  refine ⟨(Fork.IsLimit.lift F.isLimit g hg).left p, ?_⟩
  change ((Fork.IsLimit.lift F.isLimit g hg).left ≫ F.ι.left) p = _
  have hl : Fork.IsLimit.lift F.isLimit g hg ≫ F.ι = g := Fork.IsLimit.lift_ι' _ _ _
  rw [← Over.comp_left, hl]
  rfl

include hb in
/-- The geometric generic fibre of `𝒟_b B` is the base change of that of `𝒞` along `B ⟶ C`:
`𝒟_b B_Ω = B ×_C 𝒞_Ω`. -/
lemma isPullback_componentGenericMap :
    IsPullback (deformationGenericMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k')
      (deformationGenericToTotal B b.left.ker k' ≫ deformationTotalToBase B b.left.ker k')
      (deformationGenericToTotal c.C y.left.ker k' ≫ deformationTotalToBase c.C y.left.ker k')
      (j ≫ F.ι).left := by
  have t := (isPullback_deformationModel_ε k' (X := c.C) y.left.ker).flip
  have s := (isPullback_deformationModel_ε k' (X := B) b.left.ker).flip
  have e₁ : deformationGenericMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k' ≫
      deformationGenericToPoint c.C y.left.ker k' = deformationGenericToPoint B b.left.ker k' :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have e₂ : (j ≫ F.ι).left ≫ c.C.hom = B.hom := Over.w (j ≫ F.ι)
  rw [← e₁, ← e₂] at s
  exact IsPullback.of_right s (componentModelHom k' j hb).comm_ε t

/-- **`ι_F` is surjective** (blueprint `lemma-fixed-point-scheme-deformation`, last assertion, for
`Z = {x}`): if `j : B ⟶ F` is surjective, every point of the total space `F̃` of the deformed fixed
locus comes from the deformation `𝒟_b B`. Over the closed point of the trait, a fixed point lies on
the zero section of `N_y C ⊗ k'`, which is the single point given by the vertex; over the generic
point, the deformation is the base change of `B ⟶ C`, and `F̃ ⟶ C` lands in `F`. -/
theorem surjective_componentFixedLocusTotalLift [Surjective j.left] :
    Surjective (componentFixedLocusTotalLift hc k' F j hb) := by
  refine ⟨fun p ↦ ?_⟩
  suffices hq : deformedFixedLocusTotalFst hc k' F p ∈
      Set.range (componentModelHom k' j hb).total by
    obtain ⟨z, hz⟩ := hq
    refine ⟨z, (deformedFixedLocusTotalFst hc k' F).isClosedEmbedding.injective ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, componentFixedLocusTotalLift_fst]
    rfl
  by_cases hτ : deformationTotalToTrait c.C y.left.ker k' (deformedFixedLocusTotalFst hc k' F p) ∈
      Set.range (traitClosedPoint k')
  · obtain ⟨s, hs⟩ : deformedFixedLocusTotalFst hc k' F p ∈
        Set.range (deformationSpecialToTotal c.C y.left.ker k') := by
      exact (Scheme.Pullback.range_fst (deformationTotalToTrait c.C y.left.ker k')
        (traitClosedPoint k')).ge hτ
    have : IsClosedImmersion (traitClosedPoint k') :=
      IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩
    have : IsClosedImmersion (deformationSpecialToTotal X (y ≫ c.c₁).left.ker k') :=
      inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
    have hγ : (hc.specialLeg₁ k').left s = (hc.specialLeg₂ k').left s := by
      apply (deformationSpecialToTotal X (y ≫ c.c₁).left.ker k').isClosedEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, deformationSpecialFibreMap_toTotal,
        deformationSpecialFibreMap_toTotal, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs,
        ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        deformedFixedLocusTotalFst_comp_deformationTotalMap]
    obtain ⟨z₁, hz₁⟩ := hc.mem_range_zeroSection_of_specialLeg₁ k'
      (hγ ▸ hc.range_specialLeg₂_subset k' ⟨s, rfl⟩)
    obtain ⟨pt⟩ : Nonempty (point k').left :=
      ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k')⟩
    obtain ⟨z₂, hz₂⟩ := deformationSpecialFibreMap_vertex_mem_range k' (j ≫ F.ι) b
      (map_siteIdeal_le_ker_component j hb) pt
    have : Subsingleton (deformationSpecialZeroLocus c.C y.left.ker k').left :=
      subsingleton_deformationSpecialZeroLocus y k'
    refine ⟨deformationSpecialToTotal B b.left.ker k' ((deformationVertex b k').left pt), ?_⟩
    rw [← hs, ← hz₁, Subsingleton.elim z₁ z₂, hz₂, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, deformationSpecialFibreMap_toTotal]
    rfl
  · obtain ⟨ω, hω⟩ := mem_range_traitGenericPoint_of_notMem_range_traitClosedPoint k' _ hτ
    obtain ⟨g, hg⟩ : deformedFixedLocusTotalFst hc k' F p ∈
        Set.range (deformationGenericToTotal c.C y.left.ker k') := by
      exact (Scheme.Pullback.range_fst (deformationTotalToTrait c.C y.left.ker k')
        (traitGenericPoint k')).ge ⟨ω, hω⟩
    obtain ⟨β, hβ⟩ : deformationTotalToBase c.C y.left.ker k'
        (deformedFixedLocusTotalFst hc k' F p) ∈ Set.range (j ≫ F.ι).left := by
      obtain ⟨φ, hφ⟩ := deformationTotalToBase_deformedFixedLocusTotalFst_mem_range hc k' F p
      obtain ⟨β, rfl⟩ := j.left.surjective φ
      exact ⟨β, by rw [Over.comp_left, Scheme.Hom.comp_apply, hφ]⟩
    have hpb := isPullback_componentGenericMap k' F j hb
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := deformationGenericToTotal c.C y.left.ker k' ≫ deformationTotalToBase c.C y.left.ker k')
      (g := (j ≫ F.ι).left) g β (by
        rw [hβ, ← hg, Scheme.Hom.comp_apply])
    refine ⟨deformationGenericToTotal B b.left.ker k' (hpb.isoPullback.inv w), ?_⟩
    have e := congrArg (fun f ↦ f (hpb.isoPullback.inv w))
      (deformationGenericMap_toTotal (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k')
    have e₂ := congrArg (fun f ↦ f w) (IsPullback.isoPullback_inv_fst hpb)
    simp only [Scheme.Hom.comp_apply] at e e₂
    rw [← hg, ← hw, ← e₂]
    exact e.symm

/-- **`ι_F` is a universal homeomorphism** (blueprint `lemma-fixed-point-scheme-deformation`, last
assertion, for `Z = {x}`): if `B ⊂ F ⊂ C` is closed and `j` is surjective, `ι_F : 𝒟_b B ⟶ F̃` is a
surjective closed immersion; in particular `(ι_F)_red` is an isomorphism. -/
theorem isUniversalHomeomorphism_componentFixedLocusTotalLift [IsClosedImmersion (j ≫ F.ι).left]
    [Surjective j.left] : IsUniversalHomeomorphism (componentFixedLocusTotalLift hc k' F j hb) :=
  have := isClosedImmersion_componentFixedLocusTotalLift hc k' F j hb
  have := surjective_componentFixedLocusTotalLift hc k' F j hb
  {}

/-- **`ι_F` is a universal homeomorphism for a connected fixed locus** (blueprint
`lemma-fixed-point-scheme-deformation`, `Z = {x}`): if the fixed locus `F` is connected, it is the
single point `y` (`subsingleton_component`), so every `j : B ⟶ F` with `B ⊂ F` closed is
surjective, and `ι_F : 𝒟_b B ⟶ F̃` is a surjective closed immersion. -/
theorem isUniversalHomeomorphism_componentFixedLocusTotalLift_of_connected
    [IsClosedImmersion (j ≫ F.ι).left] [ConnectedSpace F.F.left] :
    IsUniversalHomeomorphism (componentFixedLocusTotalLift hc k' F j hb) := by
  have : IsClosedImmersion (𝟙 F.F : F.F ⟶ F.F).left := by
    rw [Over.id_left]
    infer_instance
  have : Subsingleton F.F.left :=
    hc.subsingleton_component F (𝟙 F.F) (b ≫ j) (by rw [Category.id_comp, Category.assoc, hb])
  have : Surjective j.left :=
    ⟨fun _ ↦ ⟨b.left (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), Subsingleton.elim _ _⟩⟩
  exact isUniversalHomeomorphism_componentFixedLocusTotalLift hc k' F j hb

/-- If the total space `F̃` of the deformed fixed locus is reduced, `ι_F : 𝒟_b B ⟶ F̃` is an
isomorphism (blueprint `lemma-fixed-point-scheme-deformation`, `Z = {x}`): a surjective closed
immersion into a reduced scheme is an isomorphism. -/
theorem isIso_componentFixedLocusTotalLift_of_isReduced [IsClosedImmersion (j ≫ F.ι).left]
    [Surjective j.left] [IsReduced (deformedFixedLocusTotal hc k' F)] :
    IsIso (componentFixedLocusTotalLift hc k' F j hb) :=
  have := isClosedImmersion_componentFixedLocusTotalLift hc k' F j hb
  have := surjective_componentFixedLocusTotalLift hc k' F j hb
  isIso_of_isClosedImmersion_of_surjective _

end Correspondence.IsContractingAt

end ProEtale.CondensedRing

end AlgebraicGeometry
