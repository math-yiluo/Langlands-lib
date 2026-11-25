/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperStarLimits.SectionsIso
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsGlobal

/-!
# The pullback to an affine base preserves limits

For an arbitrary morphism of schemes `g : Z ⟶ Y` with `Y` affine, the pullback `g^*` of
pro-étale sheaves of modules preserves all small limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isAffine_target`).

The objects `V` of `Z_proét` which are affine with split affine covers (e.g. spectra of
w-contractible rings) cover `Z_proét` (`AlgebraicGeometry.ProEtale.exists_affineCoversSplit_cover`)
and are weakly contractible. Over such `V`, with weakly étale hull `W₀` of `V ⟶ Y`
(`AlgebraicGeometry.Scheme.ProEt.exists_isHull`), the sections of `g^* F` are `F(W₀)`
(`AlgebraicGeometry.ProEtale.isIso_hullSectionsNatTrans`), which commute with limits in `F`. So
the comparison map `g^*(lim F) ⟶ lim g^* F` is bijective on sections over these `V`, hence its
kernel and cokernel vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Every object `V` of the small pro-étale site is covered by objects whose underlying schemes
are affine with split affine covers: cover `V` by affine opens `Spec R`, and each `Spec R` by
`Spec S`, for a faithfully flat, ind-étale and w-contractible `R`-algebra `S`. -/
theorem exists_affineCoversSplit_cover {T : Scheme.{u}} (V : T.ProEt) :
    ∃ (ι : Type u) (W : ι → T.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, IsAffine (W i).left ∧ (W i).left.AffineCoversSplit) ∧
        Sieve.ofArrows W f ∈ ProEt.topology T V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := ProEt.ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : T.ProEt := ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ ProEt.ofOpenImmersionHom V (𝒜.f x), fun x ↦ ⟨?_, ?_⟩, ?_⟩
  · exact inferInstanceAs (IsAffine (Spec _))
  · have := hw x
    exact affineCoversSplit_Spec (R := CommRingCat.of (S x))
      (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction (S x) T)
  · have hU : Sieve.ofArrows U (fun x ↦ ProEt.ofOpenImmersionHom V (𝒜.f x)) ∈
        ProEt.topology T V :=
      ProEt.mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
        (fun x ↦ Sieve.ofArrows_mk _ _ x)
    refine (ProEt.topology T).transitive hU _ fun Y g hg ↦ ?_
    obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
    rw [Sieve.pullback_comp]
    refine (ProEt.topology T).pullback_stable c ((ProEt.topology T).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
    · rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
      exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance

/-- An object of the small pro-étale site which is affine with split affine covers is weakly
contractible. -/
lemma isWeaklyContractible_of_affineCoversSplit {T : Scheme.{u}} {V : T.ProEt} [IsAffine V.left]
    (hV : V.left.AffineCoversSplit) : (ProEt.topology T).IsWeaklyContractible.{u + 1} V :=
  ProEt.isWeaklyContractible_of_forall_exists_retraction (R := Γ(V.left, ⊤))
    (hV.of_iso V.left.isoSpec).exists_retraction V.left.isoSpec

variable {R : Type (u + 1)} [Ring R]

/-- On an affine object `V` of `Z_proét` with split affine covers, sections of `g^*` commute with
limits, for `g : Z ⟶ Spec B`: they are the sections over the hull of `V ⟶ Spec B`. -/
lemma isIso_map_limit_post_of_affineCoversSplit {Z : Scheme.{u}} {B : CommRingCat.{u}}
    (g : Z ⟶ Spec B) {J : Type (u + 1)} [Category.{u + 1} J]
    (D : J ⥤ Sheaf (ProEt.topology (Spec B)) (ModuleCat.{u + 1} R)) {V : Z.ProEt}
    [IsAffine V.left] (hV : V.left.AffineCoversSplit) :
    IsIso ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op V)).map
      (limit.post D (g)^*[ModuleCat.{u + 1} R])) := by
  have hhull (V' : Z.ProEt) (_ : IsAffine V'.left) (hV' : V'.left.AffineCoversSplit) :
      ∃ W ψ', ProEt.IsHull (V'.hom ≫ g) W ψ' :=
    ProEt.exists_isHull hV' _
  obtain ⟨W₀, ψ, hψ⟩ := hhull V inferInstance hV
  let EV := sheafToPresheaf (ProEt.topology Z) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op V)
  have : IsIso (hullSectionsNatTrans (R := R) g hψ) := isIso_hullSectionsNatTrans g hψ hV hhull
  have : PreservesLimit D ((g)^*[ModuleCat.{u + 1} R] ⋙ EV) :=
    preservesLimit_of_natIso D (asIso (hullSectionsNatTrans (R := R) g hψ))
  have h := limit.post_post D (g)^*[ModuleCat.{u + 1} R] EV
  have : IsIso (EV.map (limit.post D (g)^*[ModuleCat.{u + 1} R]) ≫
      limit.post (D ⋙ (g)^*[ModuleCat.{u + 1} R]) EV) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (limit.post (D ⋙ (g)^*[ModuleCat.{u + 1} R]) EV)

/-- **The pullback to the spectrum of a ring preserves limits**: for an arbitrary morphism
`g : Z ⟶ Spec B`, the pullback `g^*` of pro-étale sheaves of modules preserves all small
limits. The comparison map `g^*(lim F) ⟶ lim g^* F` is bijective on sections over the affine
objects with split affine covers (`isIso_map_limit_post_of_affineCoversSplit`), which are weakly
contractible and cover `Z_proét`; so its kernel and cokernel vanish. -/
theorem preservesLimitsOfSize_upperStar_toSpec {Z : Scheme.{u}} {B : CommRingCat.{u}}
    (g : Z ⟶ Spec B) : PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[ModuleCat.{u + 1} R]) := by
  refine ⟨fun {J} _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  set c := limit.post D (g)^*[ModuleCat.{u + 1} R]
  let E (V : Z.ProEt) := sheafToPresheaf (ProEt.topology Z) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op V)
  let P (V : Z.ProEt) : Prop := IsAffine V.left ∧ V.left.AffineCoversSplit
  have hc (V : Z.ProEt) (hV : P V) : IsIso ((E V).map c) :=
    have := hV.1
    isIso_map_limit_post_of_affineCoversSplit g D hV.2
  have hmono : Mono c := by
    refine Preadditive.mono_of_isZero_kernel _ ?_
    refine (GrothendieckTopology.isZero_sheaf_iff_of_forall_exists (R := R) P
      exists_affineCoversSplit_cover (kernel c)).2 fun V hV ↦ ?_
    have := hc V hV
    exact ModuleCat.subsingleton_of_isZero
      ((isZero_kernel_of_mono ((E V).map c)).of_iso (PreservesKernel.iso (E V) c))
  have hepi : Epi c := by
    refine Preadditive.epi_of_isZero_cokernel _ ?_
    refine (GrothendieckTopology.isZero_sheaf_iff_of_forall_exists (R := R) P
      exists_affineCoversSplit_cover (cokernel c)).2 fun V hV ↦ ?_
    have := hc V hV
    have := hV.1
    refine ⟨fun y y' ↦ ?_⟩
    have hsurj := surjective_app_of_isWeaklyContractible
      (isWeaklyContractible_of_affineCoversSplit hV.2) (cokernel.π c)
    have hcsurj : Function.Surjective ((E V).map c) :=
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
    have hzero : ∀ z, (cokernel.π c).hom.app (op V) ((E V).map c z) = 0 := fun z ↦ by
      change ((E V).map (c ≫ cokernel.π c)) z = 0
      rw [cokernel.condition, Functor.map_zero]
      rfl
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨x', rfl⟩ := hsurj y'
    obtain ⟨z, rfl⟩ := hcsurj x
    obtain ⟨z', rfl⟩ := hcsurj x'
    rw [hzero, hzero]
  have : IsIso c := isIso_of_mono_of_epi c
  exact preservesLimit_of_isIso_post _ _

/-- **The pullback to an affine scheme preserves limits**: for an arbitrary morphism `g : Z ⟶ Y`
with `Y` affine, the pullback `g^*` of pro-étale sheaves of modules preserves all small
limits. -/
theorem preservesLimitsOfSize_upperStar_of_isAffine_target {Z Y : Scheme.{u}} [IsAffine Y]
    (g : Z ⟶ Y) : PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[ModuleCat.{u + 1} R]) := by
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      ((g ≫ Y.isoSpec.hom)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_toSpec _
  have : PreservesLimitsOfSize.{u + 1, u + 1} ((Y.isoSpec.inv)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_of_mono Y.isoSpec.inv
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (((g ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_comp _ _
  have hg : (g ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv = g := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact preservesLimits_of_natIso
    (eqToIso (congrArg (fun f ↦ (f)^*[ModuleCat.{u + 1} R]) hg))

end AlgebraicGeometry.ProEtale
